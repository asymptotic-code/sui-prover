//! Helpers for reading prover-relevant attributes from the compiled model.
//!
//! Spec code is marked with the compiler mode `#[mode(spec)]` together with a
//! companion external attribute that says what the item is:
//!
//! ```text
//!   #[mode(spec), ext(spec)]                  // was #[spec]
//!   #[mode(spec), ext(spec(prove, ...))]      // was #[spec(prove, ...)]
//!   #[mode(spec), ext(spec_only)]             // was #[spec_only]
//!   #[mode(spec), ext(spec_only(axiom))]      // was #[spec_only(axiom)]
//! ```
//!
//! `ext(spec(...))` accepts every parameter of the deprecated `#[spec(...)]`, and
//! `ext(spec_only(...))` every parameter of the deprecated `#[spec_only(...)]`.
//! Both syntaxes are realized into the same [`SpecAttr`] / [`SpecOnlyAttr`].

use codespan_reporting::diagnostic::Severity;
use move_compiler::{
    expansion::ast::{Attributes, ModuleAccess, ModuleIdent, Value_},
    shared::known_attributes::{
        AttributeKind_, ExternalAttribute, ExternalAttributeEntry_, ExternalAttributeValue_,
        KnownAttribute, ModeAttribute, VerificationAttribute,
    },
};
use move_ir_types::location::Spanned;
use move_model::model::{FunctionEnv, GlobalEnv, Loc, ModuleEnv};

/// The compiler mode that marks spec code: `#[mode(spec)]`.
pub const SPEC_MODE: &str = "spec";
/// The `ext` entry marking a spec function: `#[ext(spec(...))]`.
pub const EXT_SPEC: &str = "spec";
/// The `ext` entry marking spec-only helper code: `#[ext(spec_only(...))]`.
pub const EXT_SPEC_ONLY: &str = "spec_only";

/// Parameters shared by `spec` and `spec_only`: `include` and `extra_bpl`.
#[derive(Debug, Clone, Default)]
pub struct SpecIncludes {
    pub explicit_specs: Vec<ModuleAccess>,
    pub explicit_spec_modules: Vec<ModuleIdent>,
    pub extra_bpl: Vec<String>,
}

/// The realized form of `#[spec(...)]` or `#[mode(spec), ext(spec(...))]`.
#[derive(Debug, Clone, Default)]
pub struct SpecAttr {
    pub focus: bool,
    pub prove: bool,
    pub skip: Option<String>,
    pub target: Option<ModuleAccess>,
    pub no_opaque: bool,
    pub ignore_abort: bool,
    pub boogie_opt: Option<String>,
    pub timeout: Option<u64>,
    pub uninterpreted: Vec<ModuleAccess>,
    pub interpreted: Vec<ModuleAccess>,
    pub run_on: Option<String>,
    pub includes: SpecIncludes,
}

/// The role a spec-only item plays; the deprecated syntax allows at most one.
#[derive(Debug, Clone)]
pub enum SpecOnlyRole {
    Axiom,
    Invariant { target: ModuleAccess },
    LoopInvariant { target: ModuleAccess, label: usize },
}

/// The realized form of `#[spec_only(...)]` or `#[mode(spec), ext(spec_only(...))]`.
#[derive(Debug, Clone, Default)]
pub struct SpecOnlyAttr {
    pub role: Option<SpecOnlyRole>,
    pub includes: SpecIncludes,
}

/// The spec annotations of one item; at most one of the two is present.
#[derive(Debug, Clone, Default)]
pub struct SpecAnnotations {
    pub spec: Option<SpecAttr>,
    pub spec_only: Option<SpecOnlyAttr>,
}

/// Prover flags carried by a plain `#[ext(...)]` attribute.
#[derive(Debug, Clone, Copy, Default)]
pub struct ExtFlags {
    pub no_abort: bool,
    pub pure: bool,
    pub uninterpreted: bool,
}

/// Access to the spec annotations of model items.
pub trait SpecModeAnnotated {
    fn global_env(&self) -> &GlobalEnv;
    fn loc(&self) -> Loc;
    fn attributes(&self) -> &Attributes;
    fn item_name(&self) -> String;

    fn is_spec_mode(&self) -> bool {
        is_spec_mode(self.attributes())
    }

    /// Realizes the item's spec annotations from either syntax, reporting
    /// deprecated usage and malformed or mixed annotations.
    /// Call it once per item, since it reports diagnostics.
    fn spec_annotations(&self) -> SpecAnnotations {
        let item = Item {
            env: self.global_env(),
            loc: self.loc(),
            name: self.item_name(),
        };
        item.realize(self.attributes())
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

pub fn is_spec_mode(attrs: &Attributes) -> bool {
    matches!(
        attrs.get_(&AttributeKind_::Mode).map(|attr| &attr.value),
        Some(KnownAttribute::Mode(ModeAttribute { modes }))
            if modes.contains_(&SPEC_MODE.into())
    )
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

fn find_ext_entry<'a>(attrs: &'a Attributes, name: &str) -> Option<&'a ExternalAttributeEntry_> {
    ext_entries(attrs)?.find(|entry| entry.name().value.as_str() == name)
}

fn entries_of(entry: &ExternalAttributeEntry_) -> Vec<&ExternalAttributeEntry_> {
    match entry {
        ExternalAttributeEntry_::Parameterized(_, entries) => {
            entries.into_iter().map(|entry| &entry.2.value).collect()
        }
        _ => vec![],
    }
}

/// The item whose attributes are being realized; carries the diagnostic context.
struct Item<'env> {
    env: &'env GlobalEnv,
    loc: Loc,
    name: String,
}

impl Item<'_> {
    fn error(&self, msg: &str) {
        self.env.diag(Severity::Error, &self.loc, msg);
    }

    fn realize(&self, attrs: &Attributes) -> SpecAnnotations {
        let legacy_spec = attrs.get_(&AttributeKind_::Spec);
        let legacy_spec_only = attrs.get_(&AttributeKind_::SpecOnly);
        let ext_spec = find_ext_entry(attrs, EXT_SPEC);
        let ext_spec_only = find_ext_entry(attrs, EXT_SPEC_ONLY);
        let spec_mode = is_spec_mode(attrs);

        let has_legacy = legacy_spec.is_some() || legacy_spec_only.is_some();
        let has_new = spec_mode || ext_spec.is_some() || ext_spec_only.is_some();

        if has_legacy && has_new {
            self.error(&format!(
                "'{}' mixes the deprecated #[spec]/#[spec_only] attributes with \
                 #[mode(spec)]/#[ext(spec(...))]/#[ext(spec_only(...))]; use only the latter",
                self.name
            ));
            return SpecAnnotations::default();
        }

        if has_legacy {
            for attr in legacy_spec.into_iter().chain(legacy_spec_only) {
                self.warn_deprecated(attr);
            }
            return SpecAnnotations {
                spec: legacy_spec.and_then(|attr| legacy_spec_attr(&attr.value)),
                spec_only: legacy_spec_only.and_then(|attr| legacy_spec_only_attr(&attr.value)),
            };
        }

        if !has_new {
            return SpecAnnotations::default();
        }
        if ext_spec.is_some() && ext_spec_only.is_some() {
            self.error(&format!(
                "'{}' cannot be both #[ext(spec(...))] and #[ext(spec_only(...))]",
                self.name
            ));
            return SpecAnnotations::default();
        }
        if !spec_mode {
            let which = if ext_spec.is_some() {
                EXT_SPEC
            } else {
                EXT_SPEC_ONLY
            };
            self.error(&format!(
                "#[ext({which}(...))] on '{}' requires #[mode(spec)]",
                self.name
            ));
            return SpecAnnotations::default();
        }
        if ext_spec.is_none() && ext_spec_only.is_none() {
            self.error(&format!(
                "#[mode(spec)] on '{}' requires #[ext(spec)] or #[ext(spec_only)]; \
                 e.g. #[mode(spec), ext(spec_only)] for a spec helper",
                self.name
            ));
            return SpecAnnotations::default();
        }

        SpecAnnotations {
            spec: ext_spec.and_then(|entry| self.parse_spec(entry)),
            spec_only: ext_spec_only.and_then(|entry| self.parse_spec_only(entry)),
        }
    }

    fn warn_deprecated(&self, attr: &Spanned<KnownAttribute>) {
        let (old, new) = match &attr.value {
            KnownAttribute::Verification(VerificationAttribute::Spec { .. }) => {
                ("#[spec(...)]", "#[mode(spec), ext(spec(...))]")
            }
            _ => ("#[spec_only(...)]", "#[mode(spec), ext(spec_only(...))]"),
        };
        self.env.diag(
            Severity::Warning,
            &self.env.to_loc(&attr.loc),
            &format!("{old} is deprecated; use {new} with the same parameters"),
        );
    }

    /// Parses `spec` / `spec(...)` from `#[ext(...)]`, following the rules of
    /// the deprecated `#[spec(...)]`.
    fn parse_spec(&self, entry: &ExternalAttributeEntry_) -> Option<SpecAttr> {
        const ATTR: &str = "spec(...)";
        let entries = self.params(entry, ATTR)?;
        let mut spec = SpecAttr::default();
        for entry in entries {
            if self.parse_include_param(entry, ATTR, &mut spec.includes)? {
                continue;
            }
            let name = entry.name().value;
            match (name.as_str(), entry) {
                ("focus", ExternalAttributeEntry_::Name(_)) => spec.focus = true,
                ("prove", ExternalAttributeEntry_::Name(_)) => spec.prove = true,
                ("skip", ExternalAttributeEntry_::Name(_)) => spec.skip = Some(String::new()),
                ("no_opaque", ExternalAttributeEntry_::Name(_)) => spec.no_opaque = true,
                ("ignore_abort", ExternalAttributeEntry_::Name(_)) => spec.ignore_abort = true,
                ("skip", _) => spec.skip = Some(self.expect_bytestring(entry, ATTR)?),
                ("target", _) => spec.target = Some(self.expect_path(entry, ATTR)?),
                ("boogie_opt", _) => spec.boogie_opt = Some(self.expect_bytestring(entry, ATTR)?),
                ("run_on", _) => spec.run_on = Some(self.expect_bytestring(entry, ATTR)?),
                ("timeout", _) => match self.expect_number(entry, ATTR)? {
                    0 => return self.fail(ATTR, "`timeout` must be greater than zero"),
                    timeout => spec.timeout = Some(timeout),
                },
                ("uninterpreted", _) => spec.uninterpreted = self.expect_paths(entry, ATTR)?,
                ("interpreted", _) => spec.interpreted = self.expect_paths(entry, ATTR)?,
                (other, _) => {
                    return self.fail(
                        ATTR,
                        &format!(
                            "unknown parameter '{other}'; expected one of: focus, prove, skip, \
                             no_opaque, ignore_abort, target, boogie_opt, timeout, run_on, \
                             include, extra_bpl, uninterpreted, interpreted"
                        ),
                    )
                }
            }
        }
        if spec.focus && spec.skip.is_some() {
            return self.fail(ATTR, "cannot use both `focus` and `skip`");
        }
        Some(spec)
    }

    /// Parses `spec_only` / `spec_only(...)` from `#[ext(...)]`, following the
    /// rules of the deprecated `#[spec_only(...)]`.
    fn parse_spec_only(&self, entry: &ExternalAttributeEntry_) -> Option<SpecOnlyAttr> {
        const ATTR: &str = "spec_only(...)";
        let entries = self.params(entry, ATTR)?;
        let mut spec_only = SpecOnlyAttr::default();
        let standalone = entries.len() == 1;
        for entry in entries {
            if self.parse_include_param(entry, ATTR, &mut spec_only.includes)? {
                continue;
            }
            let role = match (entry.name().value.as_str(), entry) {
                ("axiom", ExternalAttributeEntry_::Name(_)) if standalone => SpecOnlyRole::Axiom,
                ("loop_inv", ExternalAttributeEntry_::Parameterized(..)) if standalone => {
                    self.parse_loop_inv(entry)?
                }
                ("axiom", ExternalAttributeEntry_::Name(_))
                | ("loop_inv", ExternalAttributeEntry_::Parameterized(..)) => {
                    return self.fail(
                        ATTR,
                        &format!("`{}` must be the only parameter", entry.name().value),
                    )
                }
                ("inv_target", _) => SpecOnlyRole::Invariant {
                    target: self.expect_path(entry, ATTR)?,
                },
                (other, _) => {
                    return self.fail(
                        ATTR,
                        &format!(
                            "unknown parameter '{other}'; expected one of: axiom, \
                             inv_target, loop_inv(target = ..., label = ...), include, extra_bpl"
                        ),
                    )
                }
            };
            spec_only.role = Some(role);
        }
        let has_include = !spec_only.includes.explicit_specs.is_empty()
            || !spec_only.includes.explicit_spec_modules.is_empty();
        if matches!(spec_only.role, Some(SpecOnlyRole::Invariant { .. })) && has_include {
            return self.fail(ATTR, "cannot combine `inv_target` with `include`");
        }
        Some(spec_only)
    }

    fn parse_loop_inv(&self, entry: &ExternalAttributeEntry_) -> Option<SpecOnlyRole> {
        const ATTR: &str = "spec_only(loop_inv(...))";
        let mut target = None;
        let mut label = 0;
        for entry in entries_of(entry) {
            match entry.name().value.as_str() {
                "target" => target = Some(self.expect_path(entry, ATTR)?),
                "label" => label = usize::try_from(self.expect_number(entry, ATTR)?).ok()?,
                other => {
                    return self.fail(
                        ATTR,
                        &format!("unknown parameter '{other}'; expected `target` or `label`"),
                    )
                }
            }
        }
        let Some(target) = target else {
            return self.fail(ATTR, "missing required parameter `target`");
        };
        Some(SpecOnlyRole::LoopInvariant { target, label })
    }

    /// The parameters of a bare (`spec`) or parameterized (`spec(...)`) entry.
    fn params<'a>(
        &self,
        entry: &'a ExternalAttributeEntry_,
        attr: &str,
    ) -> Option<Vec<&'a ExternalAttributeEntry_>> {
        match entry {
            ExternalAttributeEntry_::Name(_) => Some(vec![]),
            ExternalAttributeEntry_::Parameterized(..) => Some(entries_of(entry)),
            ExternalAttributeEntry_::Assigned(..) => {
                let name = entry.name().value;
                self.fail(
                    attr,
                    &format!("use either `{name}` or `{name}(<param>, ...)`"),
                )
            }
        }
    }

    /// Handles the parameters shared by `spec` and `spec_only`. Returns whether
    /// `entry` was one of them, or `None` after reporting a malformed one.
    fn parse_include_param(
        &self,
        entry: &ExternalAttributeEntry_,
        attr: &str,
        includes: &mut SpecIncludes,
    ) -> Option<bool> {
        match entry.name().value.as_str() {
            "include" => {
                for value in self.entry_values(entry, attr)? {
                    match value {
                        ExternalAttributeValue_::Module(mi) => {
                            includes.explicit_spec_modules.push(*mi)
                        }
                        ExternalAttributeValue_::ModuleAccess(ma) => {
                            includes.explicit_specs.push(*ma)
                        }
                        _ => return self.fail(attr, "`include` expects a module or function path"),
                    }
                }
            }
            "extra_bpl" => {
                for value in self.entry_values(entry, attr)? {
                    match bytestring(value) {
                        Some(path) if includes.extra_bpl.contains(&path) => {
                            return self.fail(attr, "duplicated `extra_bpl` value")
                        }
                        Some(path) => includes.extra_bpl.push(path),
                        None => return self.fail(attr, "`extra_bpl` expects a bytestring path"),
                    }
                }
            }
            _ => return Some(false),
        }
        Some(true)
    }

    /// Reports an error about a malformed `ext(<attr>(...))` annotation.
    fn fail<T>(&self, attr: &str, msg: &str) -> Option<T> {
        self.error(&format!("invalid #[ext({attr})] on '{}': {msg}", self.name));
        None
    }

    /// `key = v` gives one value; `key(a = v1, b = v2)` gives several, since entry
    /// names within one attribute list must be unique.
    fn entry_values<'a>(
        &self,
        entry: &'a ExternalAttributeEntry_,
        attr: &str,
    ) -> Option<Vec<&'a ExternalAttributeValue_>> {
        let key = entry.name().value;
        match entry {
            ExternalAttributeEntry_::Assigned(_, value) => Some(vec![&value.value]),
            ExternalAttributeEntry_::Parameterized(..) => entries_of(entry)
                .into_iter()
                .map(|entry| match entry {
                    ExternalAttributeEntry_::Assigned(_, value) => Some(&value.value),
                    _ => self.fail(attr, &format!("expected `{key}(a = ..., b = ...)`")),
                })
                .collect(),
            ExternalAttributeEntry_::Name(_) => {
                self.fail(attr, &format!("`{key}` expects a value"))
            }
        }
    }

    /// The single value of a `key = v` entry.
    fn assigned_value<'a>(
        &self,
        entry: &'a ExternalAttributeEntry_,
        attr: &str,
    ) -> Option<&'a ExternalAttributeValue_> {
        match entry {
            ExternalAttributeEntry_::Assigned(_, value) => Some(&value.value),
            _ => self.fail(
                attr,
                &format!("`{}` expects a single assigned value", entry.name().value),
            ),
        }
    }

    fn expect_path(&self, entry: &ExternalAttributeEntry_, attr: &str) -> Option<ModuleAccess> {
        match self.assigned_value(entry, attr)? {
            ExternalAttributeValue_::ModuleAccess(ma) => Some(*ma),
            _ => self.fail(
                attr,
                &format!("`{}` expects a path, e.g. `0x42::m::f`", entry.name().value),
            ),
        }
    }

    fn expect_paths(
        &self,
        entry: &ExternalAttributeEntry_,
        attr: &str,
    ) -> Option<Vec<ModuleAccess>> {
        self.entry_values(entry, attr)?
            .into_iter()
            .map(|value| match value {
                ExternalAttributeValue_::ModuleAccess(ma) => Some(*ma),
                _ => self.fail(
                    attr,
                    &format!("`{}` expects function paths", entry.name().value),
                ),
            })
            .collect()
    }

    fn expect_bytestring(&self, entry: &ExternalAttributeEntry_, attr: &str) -> Option<String> {
        bytestring(self.assigned_value(entry, attr)?).or_else(|| {
            self.fail(
                attr,
                &format!(
                    "`{}` expects a bytestring, e.g. b\"...\"",
                    entry.name().value
                ),
            )
        })
    }

    fn expect_number(&self, entry: &ExternalAttributeEntry_, attr: &str) -> Option<u64> {
        let number = match self.assigned_value(entry, attr)? {
            ExternalAttributeValue_::Value(v) => match &v.value {
                Value_::InferredNum(n) | Value_::U256(n) => n.to_string().parse().ok(),
                Value_::U8(n) => Some(*n as u64),
                Value_::U16(n) => Some(*n as u64),
                Value_::U32(n) => Some(*n as u64),
                Value_::U64(n) => Some(*n),
                Value_::U128(n) => u64::try_from(*n).ok(),
                _ => None,
            },
            _ => None,
        };
        number.or_else(|| self.fail(attr, &format!("`{}` expects a number", entry.name().value)))
    }
}

fn bytestring(value: &ExternalAttributeValue_) -> Option<String> {
    if let ExternalAttributeValue_::Value(v) = value {
        if let Value_::Bytearray(bytes) | Value_::InferredString(bytes) = &v.value {
            return String::from_utf8(bytes.clone()).ok();
        }
    }
    None
}

fn legacy_spec_attr(attr: &KnownAttribute) -> Option<SpecAttr> {
    let KnownAttribute::Verification(VerificationAttribute::Spec {
        focus,
        prove,
        skip,
        target,
        no_opaque,
        ignore_abort,
        boogie_opt,
        timeout,
        extra_bpl,
        explicit_specs,
        explicit_spec_modules,
        uninterpreted,
        interpreted,
        run_on,
    }) = attr
    else {
        return None;
    };
    Some(SpecAttr {
        focus: *focus,
        prove: *prove,
        skip: skip.clone(),
        target: *target,
        no_opaque: *no_opaque,
        ignore_abort: *ignore_abort,
        boogie_opt: boogie_opt.clone(),
        timeout: *timeout,
        uninterpreted: uninterpreted.clone(),
        interpreted: interpreted.clone(),
        run_on: run_on.clone(),
        includes: SpecIncludes {
            explicit_specs: explicit_specs.clone(),
            explicit_spec_modules: explicit_spec_modules.clone(),
            extra_bpl: extra_bpl.clone(),
        },
    })
}

fn legacy_spec_only_attr(attr: &KnownAttribute) -> Option<SpecOnlyAttr> {
    let KnownAttribute::Verification(VerificationAttribute::SpecOnly {
        axiom,
        extra_bpl,
        inv_target,
        loop_inv,
        explicit_specs,
        explicit_spec_modules,
    }) = attr
    else {
        return None;
    };
    // The compiler's parser admits at most one role.
    let role = if *axiom {
        Some(SpecOnlyRole::Axiom)
    } else if let Some(info) = loop_inv {
        Some(SpecOnlyRole::LoopInvariant {
            target: info.target,
            label: info.label,
        })
    } else {
        inv_target.map(|target| SpecOnlyRole::Invariant { target })
    };
    Some(SpecOnlyAttr {
        role,
        includes: SpecIncludes {
            explicit_specs: explicit_specs.clone(),
            explicit_spec_modules: explicit_spec_modules.clone(),
            extra_bpl: extra_bpl.clone(),
        },
    })
}
