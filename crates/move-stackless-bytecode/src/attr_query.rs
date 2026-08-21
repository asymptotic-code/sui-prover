//! Helpers for reading prover-relevant attributes from the compiled model.

use codespan_reporting::diagnostic::Severity;
use move_compiler::{
    expansion::ast::{Attributes, ModuleAccess, ModuleIdent, Value_},
    shared::known_attributes::{
        AttributeKind_, ExternalAttribute, ExternalAttributeEntry_, ExternalAttributeValue_,
        KnownAttribute, ModeAttribute,
    },
};
use move_model::model::{FunctionEnv, GlobalEnv, Loc, ModuleEnv};

/// The compiler mode that marks spec-only code: `#[mode(spec)]`.
pub const SPEC_MODE: &str = "spec";

/// The realized form of an `#[ext(spec(...))]` annotation.
#[derive(Debug, Clone, Default)]
pub struct SpecInfo {
    pub role: Option<SpecRole>,
    pub explicit_spec_modules: Vec<ModuleIdent>,
    pub explicit_specs: Vec<ModuleAccess>,
    pub extra_bpl: Vec<String>,
}

/// The role an `#[ext(spec(...))]` annotation assigns to its item; at most one
/// may be given.
#[derive(Debug, Clone)]
pub enum SpecRole {
    Axiom,
    Invariant {
        target: ModuleAccess,
    },
    /// A missing target is diagnosed at the use site.
    LoopInvariant {
        target: Option<ModuleAccess>,
        label: usize,
    },
}

/// Prover flags carried by a plain `#[ext(...)]` attribute.
#[derive(Debug, Clone, Copy, Default)]
pub struct ExtFlags {
    pub no_abort: bool,
    pub pure: bool,
    pub uninterpreted: bool,
}

/// Access to the `#[mode(spec)]` marker and the realized `#[ext(spec(...))]`
/// annotation on model items.
pub trait SpecModeAnnotated {
    fn global_env(&self) -> &GlobalEnv;
    fn loc(&self) -> Loc;
    fn attributes(&self) -> &Attributes;
    fn item_name(&self) -> String;

    fn is_spec_mode(&self) -> bool {
        matches!(
            self.attributes().get_(&AttributeKind_::Mode).map(|attr| &attr.value),
            Some(KnownAttribute::Mode(ModeAttribute { modes }))
                if modes.contains_(&SPEC_MODE.into())
        )
    }

    /// The realized `#[ext(spec(...))]` annotation, if present. Reports an error
    /// and returns `None` when the annotation appears without `#[mode(spec)]`.
    fn get_spec_info(&self) -> Option<SpecInfo> {
        let env = self.global_env();
        let loc = self.loc();
        let info = parse_spec_info(env, &loc, self.attributes())?;
        if !self.is_spec_mode() {
            attr_error(
                env,
                &loc,
                &format!(
                    "#[ext(spec(...))] on '{}' requires #[mode(spec)]",
                    self.item_name()
                ),
            );
            return None;
        }
        Some(info)
    }
}

impl SpecModeAnnotated for FunctionEnv<'_> {
    fn global_env(&self) -> &GlobalEnv {
        self.module_env.env
    }
    fn loc(&self) -> Loc {
        self.get_loc()
    }
    fn attributes(&self) -> &Attributes {
        self.get_toplevel_attributes()
    }
    fn item_name(&self) -> String {
        self.get_full_name_str()
    }
}

impl SpecModeAnnotated for ModuleEnv<'_> {
    fn global_env(&self) -> &GlobalEnv {
        self.env
    }
    fn loc(&self) -> Loc {
        self.get_loc()
    }
    fn attributes(&self) -> &Attributes {
        self.get_toplevel_attributes()
    }
    fn item_name(&self) -> String {
        self.get_full_name_str()
    }
}

/// Collects the prover flags from an `#[ext(...)]` attribute.
pub fn get_ext_flags(attrs: &Attributes) -> ExtFlags {
    let mut flags = ExtFlags::default();
    let Some(entries) = ext_entries(attrs) else {
        return flags;
    };
    for entry in entries {
        match entry.name().value.as_str() {
            "no_abort" => flags.no_abort = true,
            "pure" => flags.pure = true,
            "uninterpreted" => flags.uninterpreted = true,
            _ => (),
        }
    }
    flags
}

fn ext_entries(attrs: &Attributes) -> Option<impl Iterator<Item = &ExternalAttributeEntry_>> {
    match attrs
        .get_(&AttributeKind_::External)
        .map(|attr| &attr.value)
    {
        Some(KnownAttribute::External(ExternalAttribute { attrs })) => {
            Some(attrs.into_iter().map(|entry| &entry.2.value))
        }
        _ => None,
    }
}

fn attr_error(env: &GlobalEnv, loc: &Loc, msg: &str) {
    env.diag(Severity::Error, loc, msg);
}

fn parse_spec_info(env: &GlobalEnv, loc: &Loc, attrs: &Attributes) -> Option<SpecInfo> {
    let spec_entry = ext_entries(attrs)?.find(|entry| entry.name().value.as_str() == "spec")?;
    let ExternalAttributeEntry_::Parameterized(_, entries) = spec_entry else {
        attr_error(
            env,
            loc,
            "`spec` in #[ext(...)] expects parameters, e.g. `ext(spec(axiom))`",
        );
        return None;
    };

    let mut info = SpecInfo::default();
    for entry in entries.into_iter().map(|entry| &entry.2.value) {
        match entry.name().value.as_str() {
            "axiom" => match entry {
                ExternalAttributeEntry_::Name(_) => set_role(env, loc, &mut info, SpecRole::Axiom),
                _ => attr_error(env, loc, "`axiom` in #[ext(spec(...))] takes no value"),
            },
            "inv_target" => {
                if let Some(target) = expect_path(env, loc, entry, "inv_target") {
                    set_role(env, loc, &mut info, SpecRole::Invariant { target });
                }
            }
            "loop_inv" => {
                if let Some(role) = parse_loop_inv(env, loc, entry) {
                    set_role(env, loc, &mut info, role);
                }
            }
            "include" => parse_include(env, loc, entry, &mut info),
            "extra_bpl" => parse_extra_bpl(env, loc, entry, &mut info),
            other => attr_error(
                env,
                loc,
                &format!("unknown #[ext(spec(...))] parameter '{}'", other),
            ),
        }
    }
    Some(info)
}

fn set_role(env: &GlobalEnv, loc: &Loc, info: &mut SpecInfo, role: SpecRole) {
    if info.role.is_some() {
        attr_error(
            env,
            loc,
            "at most one of `axiom`, `inv_target`, and `loop_inv` may be given in #[ext(spec(...))]",
        );
    } else {
        info.role = Some(role);
    }
}

fn parse_loop_inv(env: &GlobalEnv, loc: &Loc, entry: &ExternalAttributeEntry_) -> Option<SpecRole> {
    let ExternalAttributeEntry_::Parameterized(_, entries) = entry else {
        attr_error(
            env,
            loc,
            "`loop_inv` in #[ext(spec(...))] expects parameters, e.g. `loop_inv(target = f)`",
        );
        return None;
    };
    let mut target = None;
    let mut label = 0;
    for entry in entries.into_iter().map(|entry| &entry.2.value) {
        match entry.name().value.as_str() {
            "target" => target = expect_path(env, loc, entry, "target"),
            "label" => label = expect_number(env, loc, entry, "label").unwrap_or(0),
            other => attr_error(
                env,
                loc,
                &format!("unknown `loop_inv` parameter '{}'", other),
            ),
        }
    }
    Some(SpecRole::LoopInvariant { target, label })
}

/// `include = p` gives one path; `include(a = p1, b = p2)` gives several, since
/// entry names within one attribute list must be unique. The same holds for
/// `extra_bpl`.
fn entry_values<'a>(
    env: &GlobalEnv,
    loc: &Loc,
    entry: &'a ExternalAttributeEntry_,
    what: &str,
) -> Vec<&'a ExternalAttributeValue_> {
    match entry {
        ExternalAttributeEntry_::Assigned(_, value) => vec![&value.value],
        ExternalAttributeEntry_::Parameterized(_, entries) => {
            let mut values = vec![];
            for entry in entries.into_iter().map(|entry| &entry.2.value) {
                match entry {
                    ExternalAttributeEntry_::Assigned(_, value) => values.push(&value.value),
                    _ => attr_error(
                        env,
                        loc,
                        &format!("`{what}` in #[ext(spec(...))] expects a path"),
                    ),
                }
            }
            values
        }
        ExternalAttributeEntry_::Name(_) => {
            attr_error(
                env,
                loc,
                &format!("`{what}` in #[ext(spec(...))] expects a path"),
            );
            vec![]
        }
    }
}

fn parse_include(env: &GlobalEnv, loc: &Loc, entry: &ExternalAttributeEntry_, info: &mut SpecInfo) {
    for value in entry_values(env, loc, entry, "include") {
        match value {
            ExternalAttributeValue_::Module(mi) => info.explicit_spec_modules.push(*mi),
            ExternalAttributeValue_::ModuleAccess(ma) => info.explicit_specs.push(*ma),
            _ => attr_error(
                env,
                loc,
                "`include` in #[ext(spec(...))] expects a module or function path, \
                 e.g. `include = 0x42::m` or `include = 0x42::m::f`",
            ),
        }
    }
}

fn parse_extra_bpl(
    env: &GlobalEnv,
    loc: &Loc,
    entry: &ExternalAttributeEntry_,
    info: &mut SpecInfo,
) {
    for value in entry_values(env, loc, entry, "extra_bpl") {
        match expect_bytestring(value) {
            Some(path) => info.extra_bpl.push(path),
            None => attr_error(
                env,
                loc,
                "`extra_bpl` in #[ext(spec(...))] expects a bytestring path, \
                 e.g. `extra_bpl = b\"file.bpl\"`",
            ),
        }
    }
}

fn expect_path(
    env: &GlobalEnv,
    loc: &Loc,
    entry: &ExternalAttributeEntry_,
    what: &str,
) -> Option<ModuleAccess> {
    if let ExternalAttributeEntry_::Assigned(_, value) = entry {
        if let ExternalAttributeValue_::ModuleAccess(ma) = &value.value {
            return Some(*ma);
        }
    }
    attr_error(
        env,
        loc,
        &format!(
            "`{what}` in #[ext(spec(...))] expects an assigned path, e.g. `{what} = 0x42::m::f`"
        ),
    );
    None
}

fn expect_number(
    env: &GlobalEnv,
    loc: &Loc,
    entry: &ExternalAttributeEntry_,
    what: &str,
) -> Option<usize> {
    if let ExternalAttributeEntry_::Assigned(_, value) = entry {
        if let ExternalAttributeValue_::Value(v) = &value.value {
            let n = match &v.value {
                Value_::InferredNum(n) | Value_::U256(n) => n.to_string().parse().ok(),
                Value_::U8(n) => Some(*n as usize),
                Value_::U16(n) => Some(*n as usize),
                Value_::U32(n) => Some(*n as usize),
                Value_::U64(n) => usize::try_from(*n).ok(),
                Value_::U128(n) => usize::try_from(*n).ok(),
                _ => None,
            };
            if n.is_some() {
                return n;
            }
        }
    }
    attr_error(
        env,
        loc,
        &format!("`{what}` in `loop_inv` expects a number, e.g. `{what} = 0`"),
    );
    None
}

fn expect_bytestring(value: &ExternalAttributeValue_) -> Option<String> {
    if let ExternalAttributeValue_::Value(v) = value {
        if let Value_::Bytearray(bytes) | Value_::InferredString(bytes) = &v.value {
            return String::from_utf8(bytes.clone()).ok();
        }
    }
    None
}
