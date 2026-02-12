// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//! Provides a model for a set of Move modules (and scripts, which
//! are handled like modules). The model allows to access many different aspects of the Move
//! code: all declared functions and types, their associated bytecode, their source location,
//! their source text, and the specification fragments.
//!
//! The environment is nested into a hierarchy:
//!
//! - A `GlobalEnv` which gives access to all modules plus other information on global level,
//!   and is the owner of all related data.
//! - A `ModuleEnv` which is a reference to the data of some module in the environment.
//! - A `StructEnv` which is a reference to the data of some struct in a module.
//! - A `FunctionEnv` which is a reference to the data of some function in a module.

use std::{
    any::{Any, TypeId},
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, VecDeque},
    ffi::OsStr,
    fmt::{self, Formatter},
    rc::Rc,
};

use anyhow::bail;
use codespan::{ByteIndex, ByteOffset, ColumnOffset, FileId, Files, LineOffset, Location, Span};
use codespan_reporting::{
    diagnostic::{Diagnostic, Label, Severity},
    term::{emit, termcolor::WriteColor, Config},
};
use itertools::Itertools;
#[allow(unused_imports)]
use log::{info, warn};
use move_compiler::expansion;
use move_ir_types::ast as IR;
use num::{BigUint, Zero};
use regex::Regex;
use serde::{Deserialize, Serialize};

pub use move_binary_format::file_format::{AbilitySet, Visibility as FunctionVisibility};
use move_binary_format::{
    file_format::{
        AddressIdentifierIndex, Bytecode, Constant as VMConstant, ConstantPoolIndex,
        DatatypeHandleIndex, EnumDefinitionIndex, FunctionDefinition, FunctionDefinitionIndex,
        FunctionHandleIndex, IdentifierIndex, ModuleHandle, SignatureIndex, SignatureToken,
        StructDefinitionIndex, StructFieldInformation, VariantJumpTable, Visibility,
    },
    CompiledModule,
};
use move_bytecode_source_map::{mapping::SourceMapping, source_map::SourceMap};
use move_command_line_common::files::FileHash;
use move_core_types::{
    account_address::AccountAddress,
    identifier::{IdentStr, Identifier},
    language_storage,
    runtime_value::MoveValue,
};
use move_core_types::{language_storage::StructTag, parsing::address::NumericalAddress};
use move_disassembler::disassembler::{Disassembler, DisassemblerOptions};

use crate::{
    ast::{Attribute, ModuleName, QualifiedSymbol, Value},
    symbol::{Symbol, SymbolPool},
    ty::{PrimitiveType, Type, TypeDisplayContext},
};

// =================================================================================================
// # Constants

/// A name we use to represent a script as a module.
pub const SCRIPT_MODULE_NAME: &str = "<SELF>";

/// Names used in the bytecode/AST to represent the main function of a script
pub const SCRIPT_BYTECODE_FUN_NAME: &str = "<SELF>";

/// A prefix used for structs which are backing specification ("ghost") memory.
pub const GHOST_MEMORY_PREFIX: &str = "Ghost$";

// =================================================================================================
// # Locations

/// A location, consisting of a FileId and a span in this file.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Loc {
    file_id: FileId,
    span: Span,
}

impl Loc {
    pub fn new(file_id: FileId, span: Span) -> Loc {
        Loc { file_id, span }
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn file_id(&self) -> FileId {
        self.file_id
    }

    // Delivers a location pointing to the end of this one.
    pub fn at_end(&self) -> Loc {
        if self.span.end() > ByteIndex(0) {
            Loc::new(
                self.file_id,
                Span::new(self.span.end() - ByteOffset(1), self.span.end()),
            )
        } else {
            self.clone()
        }
    }

    // Delivers a location pointing to the start of this one.
    pub fn at_start(&self) -> Loc {
        Loc::new(
            self.file_id,
            Span::new(self.span.start(), self.span.start() + ByteOffset(1)),
        )
    }

    /// Creates a location which encloses all the locations in the provided slice,
    /// which must not be empty. All locations are expected to be in the same file.
    pub fn enclosing(locs: &[&Loc]) -> Loc {
        assert!(!locs.is_empty());
        let loc = locs[0];
        let mut start = loc.span.start();
        let mut end = loc.span.end();
        for l in locs.iter().skip(1) {
            if l.file_id() == loc.file_id() {
                start = std::cmp::min(start, l.span().start());
                end = std::cmp::max(end, l.span().end());
            }
        }
        Loc::new(loc.file_id(), Span::new(start, end))
    }

    /// Returns true if the other location is enclosed by this location.
    pub fn is_enclosing(&self, other: &Loc) -> bool {
        self.file_id == other.file_id && GlobalEnv::enclosing_span(self.span, other.span)
    }
}

impl Default for Loc {
    fn default() -> Self {
        let mut files = Files::new();
        let dummy_id = files.add(String::new(), String::new());
        Loc::new(dummy_id, Span::default())
    }
}

/// Alias for the Loc variant of MoveIR. This uses a `&static str` instead of `FileId` for the
/// file name.
pub type MoveIrLoc = move_ir_types::location::Loc;

// =================================================================================================
// # Identifiers
//
// Identifiers are opaque values used to reference entities in the environment.
//
// We have two kinds of ids: those based on an index, and those based on a symbol. We use
// the symbol based ids where we do not have control of the definition index order in bytecode
// (i.e. we do not know in which order move-compiler enters functions and structs into file format),
// and index based ids where we do have control (for modules, SpecFun and SpecVar).
//
// In any case, ids are opaque in the sense that if someone has a StructId or similar in hand,
// it is known to be defined in the environment, as it has been obtained also from the environment.

/// Raw index type used in ids. 16 bits are sufficient currently.
pub type RawIndex = u16;

/// Identifier for a module.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct ModuleId(RawIndex);

/// Identifier for a named constant, relative to module.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct NamedConstantId(Symbol);

/// Identifier for a datatype, relative to module.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct DatatypeId(Symbol);

/// Identifier for an enum variant, relative to an enum.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct VariantId(Symbol);

/// Identifier for a field of a structure, relative to struct.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct FieldId(Symbol);

/// Identifier for a Move function, relative to module.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct FunId(Symbol);

/// Identifier for a node in the AST, relative to a module. This is used to associate attributes
/// with the node, like source location and type.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct NodeId(usize);

/// A global id. Instances of this type represent unique identifiers relative to `GlobalEnv`.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct GlobalId(usize);

/// Identifier for an intrinsic declaration, relative globally in `GlobalEnv`.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct IntrinsicId(usize);

/// Some identifier qualified by a module.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct QualifiedId<Id> {
    pub module_id: ModuleId,
    pub id: Id,
}

/// Reference type when unpacking an enum variant.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum RefType {
    ByValue,
    ByImmRef,
    ByMutRef,
}

/// Some identifier qualified by a module and a type instantiation.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct QualifiedInstId<Id> {
    pub module_id: ModuleId,
    pub inst: Vec<Type>,
    pub id: Id,
}

impl NamedConstantId {
    pub fn new(sym: Symbol) -> Self {
        Self(sym)
    }

    pub fn symbol(self) -> Symbol {
        self.0
    }
}

impl FunId {
    pub fn new(sym: Symbol) -> Self {
        Self(sym)
    }

    pub fn symbol(self) -> Symbol {
        self.0
    }
}

impl DatatypeId {
    pub fn new(sym: Symbol) -> Self {
        Self(sym)
    }

    pub fn symbol(self) -> Symbol {
        self.0
    }
}

impl FieldId {
    pub fn new(sym: Symbol) -> Self {
        Self(sym)
    }

    pub fn symbol(self) -> Symbol {
        self.0
    }
}

impl NodeId {
    pub fn new(idx: usize) -> Self {
        Self(idx)
    }

    pub fn as_usize(self) -> usize {
        self.0
    }
}

impl ModuleId {
    pub fn new(idx: usize) -> Self {
        Self(idx as RawIndex)
    }

    pub fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl ModuleId {
    pub fn qualified<Id>(self, id: Id) -> QualifiedId<Id> {
        QualifiedId {
            module_id: self,
            id,
        }
    }

    pub fn qualified_inst<Id>(self, id: Id, inst: Vec<Type>) -> QualifiedInstId<Id> {
        QualifiedInstId {
            module_id: self,
            inst,
            id,
        }
    }
}

impl GlobalId {
    pub fn new(idx: usize) -> Self {
        Self(idx)
    }

    pub fn as_usize(self) -> usize {
        self.0
    }
}

impl IntrinsicId {
    pub fn new(idx: usize) -> Self {
        Self(idx)
    }

    pub fn as_usize(self) -> usize {
        self.0
    }
}

impl<Id: Clone> QualifiedId<Id> {
    pub fn instantiate(self, inst: Vec<Type>) -> QualifiedInstId<Id> {
        let QualifiedId { module_id, id } = self;
        QualifiedInstId {
            module_id,
            inst,
            id,
        }
    }
}

impl<Id: Clone> QualifiedInstId<Id> {
    pub fn instantiate(self, params: &[Type]) -> Self {
        if params.is_empty() {
            self
        } else {
            let Self {
                module_id,
                inst,
                id,
            } = self;
            Self {
                module_id,
                inst: Type::instantiate_vec(inst, params),
                id,
            }
        }
    }

    pub fn instantiate_ref(&self, params: &[Type]) -> Self {
        let res = self.clone();
        res.instantiate(params)
    }

    pub fn to_qualified_id(&self) -> QualifiedId<Id> {
        let Self { module_id, id, .. } = self;
        module_id.qualified(id.to_owned())
    }
}

impl QualifiedInstId<DatatypeId> {
    pub fn to_type(&self) -> Type {
        Type::Datatype(self.module_id, self.id, self.inst.to_owned())
    }
}

// =================================================================================================
/// # Verification Scope

/// Defines what functions to verify.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, PartialOrd)]
pub enum VerificationScope {
    /// Verify only public functions.
    Public,
    /// Verify all functions.
    All,
    /// Verify only one function.
    Only(String),
    /// Verify only functions from the given module.
    OnlyModule(String),
    /// Verify no functions
    None,
}

impl Default for VerificationScope {
    fn default() -> Self {
        Self::Public
    }
}

impl VerificationScope {
    /// Whether verification is exclusive to only one function or module. If set, this overrides
    /// all implicitly included verification targets via invariants and friends.
    pub fn is_exclusive(&self) -> bool {
        matches!(
            self,
            VerificationScope::Only(_) | VerificationScope::OnlyModule(_)
        )
    }

    /// Returns the target function if verification is exclusive to one function.
    pub fn get_exclusive_verify_function_name(&self) -> Option<&String> {
        match self {
            VerificationScope::Only(s) => Some(s),
            _ => None,
        }
    }
}

// =================================================================================================
/// # Global Environment

/// Global environment for a set of modules.
#[derive(Debug)]
pub struct GlobalEnv {
    /// A Files database for the codespan crate which supports diagnostics.
    source_files: Files<String>,
    /// A mapping from file hash to file name and associated FileId. Though this information is
    /// already in `source_files`, we can't get it out of there so need to book keep here.
    file_hash_map: BTreeMap<FileHash, (String, FileId)>,
    /// A mapping from file id to associated alias map.
    file_alias_map: BTreeMap<FileId, Rc<BTreeMap<Symbol, NumericalAddress>>>,
    /// Bijective mapping between FileId and a plain int. FileId's are themselves wrappers around
    /// ints, but the inner representation is opaque and cannot be accessed. This is used so we
    /// can emit FileId's to generated code and read them back.
    file_id_to_idx: BTreeMap<FileId, u16>,
    file_idx_to_id: BTreeMap<u16, FileId>,
    /// A set indicating whether a file id is a target or a dependency.
    file_id_is_dep: BTreeSet<FileId>,
    /// A special constant location representing an unknown location.
    /// This uses a pseudo entry in `source_files` to be safely represented.
    unknown_loc: Loc,
    /// An equivalent of the MoveIrLoc to the above location. Used to map back and force between
    /// them.
    unknown_move_ir_loc: MoveIrLoc,
    /// A special constant location representing an opaque location.
    /// In difference to an `unknown_loc`, this is a well-known but undisclosed location.
    internal_loc: Loc,
    /// Accumulated diagnosis. In a RefCell so we can add to it without needing a mutable GlobalEnv.
    /// The boolean indicates whether the diag was reported.
    diags: RefCell<Vec<(Diagnostic<FileId>, bool)>>,
    /// Pool of symbols -- internalized strings.
    symbol_pool: SymbolPool,
    /// A counter for allocating node ids.
    next_free_node_id: RefCell<usize>,
    /// A map from node id to associated information of the expression.
    exp_info: RefCell<BTreeMap<NodeId, ExpInfo>>,
    /// List of loaded modules, in order they have been provided using `add`.
    pub module_data: Vec<ModuleData>,
    /// A counter for issuing global ids.
    global_id_counter: RefCell<usize>,
    /// A type-indexed container for storing extension data in the environment.
    extensions: RefCell<BTreeMap<TypeId, Box<dyn Any>>>,
    /// The address of the standard and extension libaries.
    stdlib_address: Option<BigUint>,
    extlib_address: Option<BigUint>,
}

/// Struct a helper type for implementing fmt::Display depending on GlobalEnv
pub struct EnvDisplay<'a, T> {
    pub env: &'a GlobalEnv,
    pub val: &'a T,
}

impl GlobalEnv {
    /// Creates a new environment.
    pub fn new() -> Self {
        let mut source_files = Files::new();
        let mut file_hash_map = BTreeMap::new();
        let mut file_id_to_idx = BTreeMap::new();
        let mut file_idx_to_id = BTreeMap::new();
        let mut fake_loc = |content: &str| {
            let file_id = source_files.add(content, content.to_string());
            let file_hash = FileHash::new(content);
            file_hash_map.insert(file_hash, (content.to_string(), file_id));
            let file_idx = file_id_to_idx.len() as u16;
            file_id_to_idx.insert(file_id, file_idx);
            file_idx_to_id.insert(file_idx, file_id);
            Loc::new(
                file_id,
                Span::from(ByteIndex(0_u32)..ByteIndex(content.len() as u32)),
            )
        };
        let unknown_loc = fake_loc("<unknown>");
        let unknown_move_ir_loc = MoveIrLoc::new(FileHash::new("<unknown>"), 0, 0);
        let internal_loc = fake_loc("<internal>");
        GlobalEnv {
            source_files,
            unknown_loc,
            unknown_move_ir_loc,
            internal_loc,
            file_hash_map,
            file_alias_map: BTreeMap::new(),
            file_id_to_idx,
            file_idx_to_id,
            file_id_is_dep: BTreeSet::new(),
            diags: RefCell::new(vec![]),
            symbol_pool: SymbolPool::new(),
            next_free_node_id: Default::default(),
            exp_info: Default::default(),
            module_data: vec![],
            global_id_counter: RefCell::new(0),
            extensions: Default::default(),
            stdlib_address: None,
            extlib_address: None,
        }
    }

    pub fn cleanup(&self) {
        self.exp_info.borrow_mut().clear();
        self.extensions.borrow_mut().clear();
        self.global_id_counter.borrow_mut().set_zero();
        self.next_free_node_id.borrow_mut().set_zero();
    }

    /// Creates a display container for the given value. There must be an implementation
    /// of fmt::Display for an instance to work in formatting.
    pub fn display<'a, T>(&'a self, val: &'a T) -> EnvDisplay<'a, T> {
        EnvDisplay { env: self, val }
    }

    /// Stores extension data in the environment. This can be arbitrary data which is
    /// indexed by type. Used by tools which want to store their own data in the environment,
    /// like a set of tool dependent options/flags. This can also be used to update
    /// extension data.
    pub fn set_extension<T: Any>(&self, x: T) {
        let id = TypeId::of::<T>();
        self.extensions
            .borrow_mut()
            .insert(id, Box::new(Rc::new(x)));
    }

    /// Retrieves extension data from the environment. Use as in `env.get_extension::<T>()`.
    /// An Rc<T> is returned because extension data is stored in a RefCell and we can't use
    /// lifetimes (`&'a T`) to control borrowing.
    pub fn get_extension<T: Any>(&self) -> Option<Rc<T>> {
        let id = TypeId::of::<T>();
        self.extensions
            .borrow()
            .get(&id)
            .and_then(|d| d.downcast_ref::<Rc<T>>().cloned())
    }

    /// Retrieves a clone of the extension data from the environment. Use as in `env.get_cloned_extension::<T>()`.
    pub fn get_cloned_extension<T: Any + Clone>(&self) -> T {
        let id = TypeId::of::<T>();
        let d = self
            .extensions
            .borrow_mut()
            .remove(&id)
            .expect("extension defined")
            .downcast_ref::<Rc<T>>()
            .cloned()
            .unwrap();
        Rc::try_unwrap(d).unwrap_or_else(|d| d.as_ref().clone())
    }

    /// Updates extension data. If they are no outstanding references to this extension it
    /// is updated in place, otherwise it will be cloned before the update.
    pub fn update_extension<T: Any + Clone>(&self, f: impl FnOnce(&mut T)) {
        let id = TypeId::of::<T>();
        let d = self
            .extensions
            .borrow_mut()
            .remove(&id)
            .expect("extension defined")
            .downcast_ref::<Rc<T>>()
            .cloned()
            .unwrap();
        let mut curr = Rc::try_unwrap(d).unwrap_or_else(|d| d.as_ref().clone());
        f(&mut curr);
        self.set_extension(curr);
    }

    /// Checks whether there is an extension of type `T`.
    pub fn has_extension<T: Any>(&self) -> bool {
        let id = TypeId::of::<T>();
        self.extensions.borrow().contains_key(&id)
    }

    /// Clear extension data from the environment (return the data if it is previously set).
    /// Use as in `env.clear_extension::<T>()` and an `Rc<T>` is returned if the extension data is
    /// previously stored in the environment.
    pub fn clear_extension<T: Any>(&self) -> Option<Rc<T>> {
        let id = TypeId::of::<T>();
        self.extensions
            .borrow_mut()
            .remove(&id)
            .and_then(|d| d.downcast::<Rc<T>>().ok())
            .map(|boxed| *boxed)
    }

    /// Create a new global id unique to this environment.
    pub fn new_global_id(&self) -> GlobalId {
        let mut counter = self.global_id_counter.borrow_mut();
        let id = GlobalId::new(*counter);
        *counter += 1;
        id
    }

    /// Returns a reference to the symbol pool owned by this environment.
    pub fn symbol_pool(&self) -> &SymbolPool {
        &self.symbol_pool
    }

    /// Adds a source to this environment, returning a FileId for it.
    pub fn add_source(
        &mut self,
        file_hash: FileHash,
        address_aliases: Rc<BTreeMap<Symbol, NumericalAddress>>,
        file_name: &str,
        source: &str,
        is_dep: bool,
    ) -> FileId {
        let file_id = self.source_files.add(file_name, source.to_string());
        self.stdlib_address =
            self.resolve_std_address_alias(self.stdlib_address.clone(), "std", &address_aliases);
        self.extlib_address = self.resolve_std_address_alias(
            self.extlib_address.clone(),
            "Extensions",
            &address_aliases,
        );
        self.file_alias_map.insert(file_id, address_aliases);
        self.file_hash_map
            .insert(file_hash, (file_name.to_string(), file_id));
        let file_idx = self.file_id_to_idx.len() as u16;
        self.file_id_to_idx.insert(file_id, file_idx);
        self.file_idx_to_id.insert(file_idx, file_id);
        if is_dep {
            self.file_id_is_dep.insert(file_id);
        }
        file_id
    }

    fn resolve_std_address_alias(
        &self,
        def: Option<BigUint>,
        name: &str,
        aliases: &BTreeMap<Symbol, NumericalAddress>,
    ) -> Option<BigUint> {
        let name_sym = self.symbol_pool().make(name);
        if let Some(a) = aliases.get(&name_sym) {
            let addr = BigUint::from_bytes_be(a.as_ref());
            if matches!(&def, Some(other_addr) if &addr != other_addr) {
                self.error(
                    &self.unknown_loc,
                    &format!(
                        "Ambiguous definition of standard address alias `{}` (`0x{} != 0x{}`).\
                                 This alias currently must be unique across all packages.",
                        name,
                        addr,
                        def.unwrap()
                    ),
                );
            }
            Some(addr)
        } else {
            def
        }
    }

    /// Find all target modules and return in a vector
    pub fn get_target_modules(&self) -> Vec<ModuleEnv> {
        let mut target_modules: Vec<ModuleEnv> = vec![];
        for module_env in self.get_modules() {
            if module_env.is_target() {
                target_modules.push(module_env);
            }
        }
        target_modules
    }

    /// Adds diagnostic to the environment.
    pub fn add_diag(&self, diag: Diagnostic<FileId>) {
        if self.has_diag(&diag) {
            // Avoid adding the same diagnostic twice.
            return;
        }
        self.diags.borrow_mut().push((diag.clone(), false));
    }

    /// Adds an error to this environment, without notes.
    pub fn error(&self, loc: &Loc, msg: &str) {
        self.diag(Severity::Error, loc, msg)
    }

    /// Adds an error to this environment, with notes.
    pub fn error_with_notes(&self, loc: &Loc, msg: &str, notes: Vec<String>) {
        self.diag_with_notes(Severity::Error, loc, msg, notes)
    }

    /// Adds a diagnostic of given severity to this environment.
    pub fn diag(&self, severity: Severity, loc: &Loc, msg: &str) {
        let diag = Diagnostic::new(severity)
            .with_message(msg)
            .with_labels(vec![Label::primary(loc.file_id, loc.span)]);
        self.add_diag(diag);
    }

    /// Adds a diagnostic of given severity to this environment, with notes.
    pub fn diag_with_notes(&self, severity: Severity, loc: &Loc, msg: &str, notes: Vec<String>) {
        let diag = Diagnostic::new(severity)
            .with_message(msg)
            .with_labels(vec![Label::primary(loc.file_id, loc.span)]);
        let diag = diag.with_notes(notes);
        self.add_diag(diag);
    }

    /// Adds a diagnostic of given severity to this environment, with secondary labels.
    pub fn diag_with_labels(
        &self,
        severity: Severity,
        loc: &Loc,
        msg: &str,
        labels: Vec<(Loc, String)>,
    ) {
        let diag = Diagnostic::new(severity)
            .with_message(msg)
            .with_labels(vec![Label::primary(loc.file_id, loc.span)]);
        let labels = labels
            .into_iter()
            .map(|(l, m)| Label::secondary(l.file_id, l.span).with_message(m))
            .collect_vec();
        let diag = diag.with_labels(labels);
        self.add_diag(diag);
    }

    /// Checks whether any of the diagnostics contains string.
    pub fn has_diag(&self, diag: &Diagnostic<FileId>) -> bool {
        self.diags.borrow().iter().any(|(d, _)| d == diag)
    }

    /// Clear all accumulated diagnosis.
    pub fn clear_diag(&self) {
        self.diags.borrow_mut().clear();
    }

    /// Returns the unknown location.
    pub fn unknown_loc(&self) -> Loc {
        self.unknown_loc.clone()
    }

    /// Returns a Move IR version of the unknown location which is guaranteed to map to the
    /// regular unknown location via `to_loc`.
    pub fn unknown_move_ir_loc(&self) -> MoveIrLoc {
        self.unknown_move_ir_loc
    }

    /// Returns the internal location.
    pub fn internal_loc(&self) -> Loc {
        self.internal_loc.clone()
    }

    /// Converts a Loc as used by the move-compiler compiler to the one we are using here.
    /// TODO: move-compiler should use FileId as well so we don't need this here. There is already
    /// a todo in their code to remove the current use of `&'static str` for file names in Loc.
    pub fn to_loc(&self, loc: &MoveIrLoc) -> Loc {
        let Some(file_id) = self.get_file_id(loc.file_hash()) else {
            return self.unknown_loc();
        };
        Loc {
            file_id,
            span: Span::new(loc.start(), loc.end()),
        }
    }

    /// Returns the file id for a file name, if defined.
    pub fn get_file_id(&self, fhash: FileHash) -> Option<FileId> {
        self.file_hash_map.get(&fhash).map(|(_, id)| id).cloned()
    }

    /// Maps a FileId to an index which can be mapped back to a FileId.
    pub fn file_id_to_idx(&self, file_id: FileId) -> u16 {
        *self
            .file_id_to_idx
            .get(&file_id)
            .expect("file_id undefined")
    }

    /// Maps an index which was obtained by `file_id_to_idx` back to a FileId.
    pub fn file_idx_to_id(&self, file_idx: u16) -> FileId {
        *self
            .file_idx_to_id
            .get(&file_idx)
            .expect("file_idx undefined")
    }

    /// Returns file name and line/column position for a location, if available.
    pub fn get_file_and_location(&self, loc: &Loc) -> Option<(String, Location)> {
        self.get_location(loc).map(|line_column| {
            (
                self.source_files
                    .name(loc.file_id())
                    .to_string_lossy()
                    .to_string(),
                line_column,
            )
        })
    }

    /// Returns line/column position for a location, if available.
    pub fn get_location(&self, loc: &Loc) -> Option<Location> {
        self.source_files
            .location(loc.file_id(), loc.span().start())
            .ok()
    }

    /// Return the source text for the given location.
    pub fn get_source(&self, loc: &Loc) -> Result<&str, codespan_reporting::files::Error> {
        self.source_files.source_slice(loc.file_id, loc.span)
    }

    /// Return the source file name for `file_id`
    pub fn get_file(&self, file_id: FileId) -> &OsStr {
        self.source_files.name(file_id)
    }

    /// Return the source file names.
    pub fn get_source_file_names(&self) -> Vec<String> {
        self.file_hash_map
            .iter()
            .filter_map(|(_, (k, _))| {
                if k.eq("<internal>") || k.eq("<unknown>") {
                    None
                } else {
                    Some(k.clone())
                }
            })
            .collect()
    }

    /// Return the source file ids.
    pub fn get_source_file_ids(&self) -> Vec<FileId> {
        self.file_hash_map
            .iter()
            .filter_map(|(_, (k, id))| {
                if k.eq("<internal>") || k.eq("<unknown>") {
                    None
                } else {
                    Some(*id)
                }
            })
            .collect()
    }

    // Gets the number of source files in this environment.
    pub fn get_file_count(&self) -> usize {
        self.file_hash_map.len()
    }

    /// Returns true if diagnostics have error severity or worse.
    pub fn has_errors(&self) -> bool {
        self.error_count() > 0
    }

    /// Returns the number of diagnostics.
    pub fn diag_count(&self, min_severity: Severity) -> usize {
        self.diags
            .borrow()
            .iter()
            .filter(|(d, reported)| !reported && d.severity >= min_severity)
            .count()
    }

    /// Returns the number of errors.
    pub fn error_count(&self) -> usize {
        self.diag_count(Severity::Error)
    }

    /// Returns true if diagnostics have warning severity or worse.
    pub fn has_warnings(&self) -> bool {
        self.diag_count(Severity::Warning) > 0
    }

    /// Writes accumulated diagnostics of given or higher severity.
    pub fn report_diag<W: WriteColor>(&self, writer: &mut W, severity: Severity) {
        self.report_diag_with_filter(writer, |d| d.severity >= severity)
    }

    /// Writes accumulated diagnostics that pass through `filter`
    pub fn report_diag_with_filter<W: WriteColor, F: Fn(&Diagnostic<FileId>) -> bool>(
        &self,
        writer: &mut W,
        filter: F,
    ) {
        self.diags
            .borrow_mut()
            .iter_mut()
            .for_each(|(diag, reported)| {
                if !*reported && filter(diag) {
                    let mut d = diag.clone();
                    d.notes = d.notes.iter().map(|n| filter_out_sensetives(n)).collect();

                    emit(writer, &Config::default(), &self.source_files, &d)
                        .expect("emit must not fail");
                    *reported = true;
                }
            });
    }

    /// Adds a new module to the environment. StructData and FunctionData need to be provided
    /// in definition index order. See `create_function_data` and `create_struct_data` for how
    /// to create them.
    #[allow(clippy::too_many_arguments)]
    pub fn add(
        &mut self,
        loc: Loc,
        attributes: Vec<Attribute>,
        toplevel_attributes: expansion::ast::Attributes,
        module: CompiledModule,
        source_map: SourceMap,
        named_constants: BTreeMap<NamedConstantId, NamedConstantData>,
        struct_data: BTreeMap<DatatypeId, StructData>,
        enum_data: BTreeMap<DatatypeId, EnumData>,
        function_data: BTreeMap<FunId, FunctionData>,
    ) {
        let idx = self.module_data.len();
        let effective_name = if module.self_id().name().as_str() == SCRIPT_MODULE_NAME {
            // Use the name of the first function in this module.
            function_data
                .iter()
                .next()
                .expect("functions in script")
                .1
                .name
        } else {
            self.symbol_pool.make(module.self_id().name().as_str())
        };
        let name = ModuleName::from_str(&module.self_id().address().to_string(), effective_name);
        let struct_idx_to_id: BTreeMap<StructDefinitionIndex, DatatypeId> = struct_data
            .iter()
            .map(|(id, data)| match &data.info {
                StructInfo::Declared { def_idx, .. } => (*def_idx, *id),
            })
            .collect();
        let function_idx_to_id: BTreeMap<FunctionDefinitionIndex, FunId> = function_data
            .iter()
            .map(|(id, data)| (data.def_idx, *id))
            .collect();

        let enum_idx_to_id: BTreeMap<EnumDefinitionIndex, DatatypeId> = enum_data
            .iter()
            .map(|(id, data)| (data.def_idx, *id))
            .collect();

        self.module_data.push(ModuleData {
            name,
            id: ModuleId(idx as RawIndex),
            module,
            named_constants,
            struct_data,
            struct_idx_to_id,
            enum_data,
            enum_idx_to_id,
            function_data,
            function_idx_to_id,
            source_map,
            loc,
            attributes,
            toplevel_attributes,
            used_modules: Default::default(),
            friend_modules: Default::default(),
        });
    }

    /// Creates data for a named constant.
    pub fn create_named_constant_data(
        &self,
        name: Symbol,
        loc: Loc,
        typ: Type,
        value: Value,
        attributes: Vec<Attribute>,
    ) -> NamedConstantData {
        NamedConstantData {
            name,
            loc,
            typ,
            value,
            attributes,
        }
    }

    /// Creates data for a function, adding any information not contained in bytecode. This is
    /// a helper for adding a new module to the environment.
    pub fn create_function_data(
        &self,
        module: &CompiledModule,
        def_idx: FunctionDefinitionIndex,
        name: Symbol,
        loc: Loc,
        attributes: Vec<Attribute>,
        toplevel_attributes: expansion::ast::Attributes,
        arg_names: Vec<Symbol>,
        type_arg_names: Vec<Symbol>,
    ) -> FunctionData {
        let handle_idx = module.function_def_at(def_idx).function;
        FunctionData {
            name,
            loc,
            attributes,
            toplevel_attributes,
            def_idx,
            handle_idx,
            arg_names,
            type_arg_names,
            called_funs: Default::default(),
            calling_funs: Default::default(),
            transitive_closure_of_called_funs: Default::default(),
        }
    }

    /// Creates data for a struct declared in Move. Currently all information is contained in
    /// the byte code. This is a helper for adding a new module to the environment.
    pub fn create_move_struct_data(
        &self,
        module: &CompiledModule,
        def_idx: StructDefinitionIndex,
        name: Symbol,
        loc: Loc,
        attributes: Vec<Attribute>,
    ) -> StructData {
        let handle_idx = module.struct_def_at(def_idx).struct_handle;
        let field_data = if let StructFieldInformation::Declared(fields) =
            &module.struct_def_at(def_idx).field_information
        {
            let mut map = BTreeMap::new();
            for (offset, field) in fields.iter().enumerate() {
                let name = self
                    .symbol_pool
                    .make(module.identifier_at(field.name).as_str());
                let info = FieldInfo::DeclaredStruct { def_idx };
                map.insert(FieldId(name), FieldData { name, offset, info });
            }
            map
        } else {
            BTreeMap::new()
        };
        let info = StructInfo::Declared {
            def_idx,
            handle_idx,
        };
        StructData {
            name,
            loc,
            attributes,
            info,
            field_data,
        }
    }

    /// Creates data for a enum declared in Move. Currently all information is contained in
    /// the byte code. This is a helper for adding a new module to the environment.
    pub fn create_move_enum_data(
        &self,
        module: &CompiledModule,
        def_idx: EnumDefinitionIndex,
        name: Symbol,
        loc: Loc,
        source_map: Option<&SourceMap>,
        attributes: Vec<Attribute>,
    ) -> EnumData {
        let enum_def = module.enum_def_at(def_idx);
        let enum_smap = source_map.map(|smap| smap.get_enum_source_map(def_idx).unwrap());
        let handle_idx = enum_def.enum_handle;
        let mut variant_data = BTreeMap::new();
        for (tag, variant) in enum_def.variants.iter().enumerate() {
            let mut field_data = BTreeMap::new();
            for (offset, field) in variant.fields.iter().enumerate() {
                let name = self
                    .symbol_pool
                    .make(module.identifier_at(field.name).as_str());
                let info = FieldInfo::DeclaredEnum { def_idx };
                field_data.insert(FieldId(name), FieldData { name, offset, info });
            }
            let variant_name = self
                .symbol_pool
                .make(module.identifier_at(variant.variant_name).as_str());
            let loc = match enum_smap {
                None => Loc::default(),
                Some(smap) => self.to_loc(&smap.variants[tag].0 .1),
            };
            variant_data.insert(
                VariantId(variant_name),
                VariantData {
                    name: variant_name,
                    loc,
                    tag,
                    field_data,
                },
            );
        }

        EnumData {
            name,
            loc,
            attributes,
            def_idx,
            handle_idx,
            variant_data,
        }
    }

    /// Finds a module by name and returns an environment for it.
    pub fn find_module(&self, name: &ModuleName) -> Option<ModuleEnv<'_>> {
        for module_data in &self.module_data {
            let module_env = ModuleEnv {
                env: self,
                data: module_data,
            };
            if module_env.get_name() == name {
                return Some(module_env);
            }
        }
        None
    }

    /// Finds a module by simple name and returns an environment for it.
    /// TODO: we may need to disallow this to support modules of the same simple name but with
    ///    different addresses in one verification session.
    pub fn find_module_by_name(&self, simple_name: Symbol) -> Option<ModuleEnv<'_>> {
        self.get_modules()
            .find(|m| m.get_name().name() == simple_name && m.get_function_count() > 0)
    }

    /// Find a module by its bytecode format ID
    pub fn find_module_by_language_storage_id(
        &self,
        id: &language_storage::ModuleId,
    ) -> Option<ModuleEnv<'_>> {
        self.find_module(&self.to_module_name(id))
    }

    /// Find a function by its bytecode format name and ID
    pub fn find_function_by_language_storage_id_name(
        &self,
        id: &language_storage::ModuleId,
        name: &IdentStr,
    ) -> Option<FunctionEnv<'_>> {
        self.find_module_by_language_storage_id(id)
            .and_then(|menv| menv.find_function(menv.symbol_pool().make(name.as_str())))
    }

    pub fn find_function_by_name(
        &self,
        module_id: ModuleId,
        simple_name: Symbol,
    ) -> Option<FunctionEnv<'_>> {
        self.get_module(module_id).find_function(simple_name)
    }

    /// Gets a StructEnv in this module by its `StructTag`
    pub fn find_datatype_by_tag(
        &self,
        tag: &language_storage::StructTag,
    ) -> Option<QualifiedId<DatatypeId>> {
        self.find_module(&self.to_module_name(&tag.module_id()))
            .and_then(|menv| {
                menv.find_struct_by_identifier(tag.name.clone())
                    .map(|sid| menv.get_id().qualified(sid))
                    .or_else(|| {
                        menv.find_enum_by_identifier(tag.name.clone())
                            .map(|sid| menv.get_id().qualified(sid))
                    })
            })
    }

    /// Return the module enclosing this location.
    pub fn get_enclosing_module(&self, loc: &Loc) -> Option<ModuleEnv<'_>> {
        for data in &self.module_data {
            if data.loc.file_id() == loc.file_id()
                && Self::enclosing_span(data.loc.span(), loc.span())
            {
                return Some(ModuleEnv { env: self, data });
            }
        }
        None
    }

    /// Returns the function enclosing this location.
    pub fn get_enclosing_function(&self, loc: &Loc) -> Option<FunctionEnv<'_>> {
        // Currently we do a brute-force linear search, may need to speed this up if it appears
        // to be a bottleneck.
        let module_env = self.get_enclosing_module(loc)?;
        for func_env in module_env.into_functions() {
            if Self::enclosing_span(func_env.get_loc().span(), loc.span()) {
                return Some(func_env.clone());
            }
        }
        None
    }

    /// Returns the struct enclosing this location.
    pub fn get_enclosing_struct(&self, loc: &Loc) -> Option<StructEnv<'_>> {
        let module_env = self.get_enclosing_module(loc)?;
        module_env
            .into_structs()
            .find(|struct_env| Self::enclosing_span(struct_env.get_loc().span(), loc.span()))
    }

    fn enclosing_span(outer: Span, inner: Span) -> bool {
        inner.start() >= outer.start() && inner.end() <= outer.end()
    }

    /// Return the `FunctionEnv` for `fun`
    pub fn get_function(&self, fun: QualifiedId<FunId>) -> FunctionEnv<'_> {
        self.get_module(fun.module_id).into_function(fun.id)
    }

    /// Return the `StructEnv` for `str`
    pub fn get_struct(&self, str: QualifiedId<DatatypeId>) -> StructEnv<'_> {
        self.get_module(str.module_id).into_struct(str.id)
    }

    // Gets the number of modules in this environment.
    pub fn get_module_count(&self) -> usize {
        self.module_data.len()
    }

    /// Gets a module by id.
    pub fn get_module(&self, id: ModuleId) -> ModuleEnv<'_> {
        let module_data = &self.module_data[id.0 as usize];
        ModuleEnv {
            env: self,
            data: module_data,
        }
    }

    /// Gets a struct by qualified id.
    pub fn get_struct_qid(&self, qid: QualifiedId<DatatypeId>) -> StructEnv<'_> {
        self.get_module(qid.module_id).into_struct(qid.id)
    }

    pub fn get_enum_qid(&self, qid: QualifiedId<DatatypeId>) -> EnumEnv<'_> {
        self.get_module(qid.module_id).into_enum(qid.id)
    }

    pub fn get_struct_or_enum_qid(&self, qid: QualifiedId<DatatypeId>) -> StructOrEnumEnv<'_> {
        self.get_module(qid.module_id).into_struct_or_enum(qid.id)
    }

    /// Gets a function by qualified id.
    pub fn get_function_qid(&self, qid: QualifiedId<FunId>) -> FunctionEnv<'_> {
        self.get_module(qid.module_id).into_function(qid.id)
    }

    /// Returns an iterator for all modules in the environment.
    pub fn get_modules(&self) -> impl Iterator<Item = ModuleEnv<'_>> {
        self.module_data.iter().map(move |module_data| ModuleEnv {
            env: self,
            data: module_data,
        })
    }

    /// Returns an iterator for all bytecode modules in the environment.
    pub fn get_bytecode_modules(&self) -> impl Iterator<Item = &CompiledModule> {
        self.module_data
            .iter()
            .map(|module_data| &module_data.module)
    }

    /// Converts a storage module id into an AST module name.
    pub fn to_module_name(&self, storage_id: &language_storage::ModuleId) -> ModuleName {
        ModuleName::from_str(
            &storage_id.address().to_string(),
            self.symbol_pool.make(storage_id.name().as_str()),
        )
    }

    /// Attempt to compute a struct tag for (`mid`, `sid`, `ts`). Returns `Some` if all types in
    /// `ts` are closed, `None` otherwise
    pub fn get_struct_tag(&self, mid: ModuleId, sid: DatatypeId, ts: &[Type]) -> Option<StructTag> {
        let menv = self.get_module(mid);
        let name = menv
            .find_struct(sid.symbol())
            .map(|senv| senv.get_identifier())
            .or_else(|| {
                menv.find_enum(sid.symbol())
                    .map(|eenv| eenv.get_identifier())
            })??;
        Some(StructTag {
            address: *menv.self_address(),
            module: menv.get_identifier(),
            name,
            type_params: ts
                .iter()
                .map(|t| t.clone().into_type_tag(self).unwrap())
                .collect(),
        })
    }

    /// Gets the location of the given node.
    pub fn get_node_loc(&self, node_id: NodeId) -> Loc {
        self.exp_info
            .borrow()
            .get(&node_id)
            .map_or_else(|| self.unknown_loc(), |info| info.loc.clone())
    }

    /// Gets the type of the given node.
    pub fn get_node_type(&self, node_id: NodeId) -> Type {
        self.get_node_type_opt(node_id).expect("node type defined")
    }

    /// Gets the type of the given node, if available.
    pub fn get_node_type_opt(&self, node_id: NodeId) -> Option<Type> {
        self.exp_info
            .borrow()
            .get(&node_id)
            .map(|info| info.ty.clone())
    }

    /// Converts an index into a node id.
    pub fn index_to_node_id(&self, index: usize) -> Option<NodeId> {
        let id = NodeId::new(index);
        if self.exp_info.borrow().get(&id).is_some() {
            Some(id)
        } else {
            None
        }
    }

    /// Returns the next free node number.
    pub fn next_free_node_number(&self) -> usize {
        *self.next_free_node_id.borrow()
    }

    /// Allocates a new node id.
    pub fn new_node_id(&self) -> NodeId {
        let id = NodeId::new(*self.next_free_node_id.borrow());
        let mut r = self.next_free_node_id.borrow_mut();
        *r = r.checked_add(1).expect("NodeId overflow");
        id
    }

    /// Allocates a new node id and assigns location and type to it.
    pub fn new_node(&self, loc: Loc, ty: Type) -> NodeId {
        let id = self.new_node_id();
        self.exp_info.borrow_mut().insert(id, ExpInfo::new(loc, ty));
        id
    }

    /// Updates type for the given node id. Must have been set before.
    pub fn update_node_type(&self, node_id: NodeId, ty: Type) {
        let mut mods = self.exp_info.borrow_mut();
        let info = mods.get_mut(&node_id).expect("node exist");
        info.ty = ty;
    }

    /// Sets instantiation for the given node id. Must not have been set before.
    pub fn set_node_instantiation(&self, node_id: NodeId, instantiation: Vec<Type>) {
        let mut mods = self.exp_info.borrow_mut();
        let info = mods.get_mut(&node_id).expect("node exist");
        assert!(info.instantiation.is_none());
        info.instantiation = Some(instantiation);
    }

    /// Updates instantiation for the given node id. Must have been set before.
    pub fn update_node_instantiation(&self, node_id: NodeId, instantiation: Vec<Type>) {
        let mut mods = self.exp_info.borrow_mut();
        let info = mods.get_mut(&node_id).expect("node exist");
        assert!(info.instantiation.is_some());
        info.instantiation = Some(instantiation);
    }

    /// Gets the type parameter instantiation associated with the given node.
    pub fn get_node_instantiation(&self, node_id: NodeId) -> Vec<Type> {
        self.get_node_instantiation_opt(node_id).unwrap_or_default()
    }

    /// Gets the type parameter instantiation associated with the given node, if it is available.
    pub fn get_node_instantiation_opt(&self, node_id: NodeId) -> Option<Vec<Type>> {
        self.exp_info
            .borrow()
            .get(&node_id)
            .and_then(|info| info.instantiation.clone())
    }

    /// Gets the type parameter instantiation associated with the given node, if it is available.
    pub fn get_nodes(&self) -> Vec<NodeId> {
        (*self.exp_info.borrow()).clone().into_keys().collect_vec()
    }

    /// Return the total number of declared functions in the modules of `self`
    pub fn get_declared_function_count(&self) -> usize {
        let mut total = 0;
        for m in &self.module_data {
            total += m.module.function_defs().len();
        }
        total
    }

    /// Return the total number of declared structs in the modules of `self`
    pub fn get_declared_struct_count(&self) -> usize {
        let mut total = 0;
        for m in &self.module_data {
            total += m.module.struct_defs().len();
        }
        total
    }

    /// Return the total number of Move bytecode instructions (not stackless bytecode) in the modules of `self`
    pub fn get_move_bytecode_instruction_count(&self) -> usize {
        let mut total = 0;
        for m in self.get_modules() {
            for f in m.get_functions() {
                total += f.get_bytecode().len();
            }
        }
        total
    }

    /// Produce a TypeDisplayContext to print types within the scope of this env
    pub fn get_type_display_ctx(&self) -> TypeDisplayContext {
        TypeDisplayContext::WithEnv {
            env: self,
            type_param_names: None,
        }
    }

    /// Returns the address where the standard lib is defined.
    pub fn get_stdlib_address(&self) -> BigUint {
        self.stdlib_address.clone().unwrap_or_else(|| 1u16.into())
    }

    /// Returns the address where the extensions libs are defined.
    pub fn get_extlib_address(&self) -> BigUint {
        self.extlib_address.clone().unwrap_or_else(|| 2u16.into())
    }

    fn find_module_id(&self, module_name: &str) -> ModuleId {
        self.find_module_by_name(self.symbol_pool().make(module_name))
            .expect(&format!("module not found: {}", module_name))
            .get_id()
    }

    fn get_fun_qid(&self, module_name: &str, fun_name: &str) -> QualifiedId<FunId> {
        self.find_module_id(module_name)
            .qualified(FunId::new(self.symbol_pool().make(fun_name)))
    }

    fn get_fun_qid_opt(&self, module_name: &str, fun_name: &str) -> Option<QualifiedId<FunId>> {
        self.find_module_by_name(self.symbol_pool().make(module_name))
            .map(|module_env| {
                module_env
                    .get_id()
                    .qualified(FunId::new(self.symbol_pool().make(fun_name)))
            })
    }

    fn get_struct_qid_opt(
        &self,
        module_name: &str,
        struct_name: &str,
    ) -> Option<QualifiedId<DatatypeId>> {
        Some(
            self.find_module_by_name(self.symbol_pool().make(module_name))?
                .find_struct(self.symbol_pool().make(struct_name))?
                .get_qualified_id(),
        )
    }

    pub const PROVER_MODULE_NAME: &'static str = "prover";
    pub const SPEC_MODULE_NAME: &'static str = "ghost";
    pub const PROVER_VECTOR_MODULE_NAME: &'static str = "vector_iter";
    pub const SPECS_MODULES_NAMES: &'static [&'static str] = &[
        Self::PROVER_MODULE_NAME,
        Self::SPEC_MODULE_NAME,
        "transfer_spec",
        "tx_context_spec",
        "random_spec",
        "object_spec",
        "kiosk_spec",
        "event_spec",
        "bcs_spec",
        "debug_spec",
        "hash_spec",
        "string_spec",
        "type_name_spec",
        "accumulator_spec",
        "address_spec",
        "config_spec",
        "types_spec",
        "bls12381_spec",
        "ecdsa_k1_spec",
        "ecdsa_r1_spec",
        "ecvrf_spec",
        "ed25519_spec",
        "groth16_spec",
        "group_ops_spec",
        "hmac_spec",
        "crypto_hash_spec",
        "nitro_attestation_spec",
        "poseidon_spec",
        "vdf_spec",
        "zklogin_verified_id_spec",
        "zklogin_verified_issuer_spec",
    ];
    const LOG_MODULE_NAME: &'static str = "log";
    const VECTOR_MODULE_NAME: &'static str = "vector";
    const VEC_SET_MODULE_NAME: &'static str = "vec_set";
    const VEC_MAP_MODULE_NAME: &'static str = "vec_map";
    const OPTION_MODULE_NAME: &'static str = "option";
    const TABLE_MODULE_NAME: &'static str = "table";
    const TABLE_VEC_MODULE_NAME: &'static str = "table_vec";
    const OBJECT_MODULE_NAME: &'static str = "object";
    const OBJECT_TABLE_MODULE_NAME: &'static str = "object_table";
    const DYNAMIC_FIELD_MODULE_NAME: &'static str = "dynamic_field";
    const DYNAMIC_OBJECT_MODULE_NAME: &'static str = "dynamic_object_field";

    const STD_BCS_MODULE_NAME: &'static str = "bcs";
    const STD_DEBUG_MODULE_NAME: &'static str = "debug";
    const STD_HASH_MODULE_NAME: &'static str = "hash";
    const STD_INTEGER_MODULE_NAME: &'static str = "integer";
    const STD_REAL_MODULE_NAME: &'static str = "real";
    const STD_STRING_MODULE_NAME: &'static str = "string";
    const STD_TYPE_NAME_MODULE_NAME: &'static str = "type_name";

    const SUI_ADDRESS_MODULE_NAME: &'static str = "address";
    const SUI_TYPES_MODULE_NAME: &'static str = "types";
    const SUI_BLS12381_MODULE_NAME: &'static str = "bls12381";
    const SUI_ECDSA_K1_MODULE_NAME: &'static str = "ecdsa_k1";
    const SUI_ECDSA_R1_MODULE_NAME: &'static str = "ecdsa_r1";
    const SUI_ECVRF_MODULE_NAME: &'static str = "ecvrf";
    const SUI_ED25519_MODULE_NAME: &'static str = "ed25519";
    const SUI_GROTH16_MODULE_NAME: &'static str = "groth16";
    const SUI_GROUP_OPS_MODULE_NAME: &'static str = "group_ops";
    const SUI_HASH_MODULE_NAME: &'static str = "hash";
    const SUI_HMAC_MODULE_NAME: &'static str = "hmac";
    const SUI_NITRO_ATTESTATION_MODULE_NAME: &'static str = "nitro_attestation";
    const SUI_POSEIDON_MODULE_NAME: &'static str = "poseidon";
    const SUI_VDF_MODULE_NAME: &'static str = "vdf";
    const SUI_ACCUMULATOR_MODULE_NAME: &'static str = "accumulator";
    const SUI_EVENT_MODULE_NAME: &'static str = "event";
    const SUI_TX_CONTEXT_MODULE_NAME: &'static str = "tx_context";

    const REQUIRES_FUNCTION_NAME: &'static str = "requires";
    const ENSURES_FUNCTION_NAME: &'static str = "ensures";
    const ASSERTS_FUNCTION_NAME: &'static str = "asserts";
    const TYPE_INV_FUNCTION_NAME: &'static str = "type_inv";
    const GLOBAL_FUNCTION_NAME: &'static str = "global";
    const GLOBAL_SET_FUNCTION_NAME: &'static str = "global_set";
    const GLOBAL_BORROW_MUT_FUNCTION_NAME: &'static str = "borrow_mut";
    const DECLARE_GLOBAL_FUNCTION_NAME: &'static str = "declare_global";
    const DECLARE_GLOBAL_MUT_FUNCTION_NAME: &'static str = "declare_global_mut";
    const HAVOC_GLOBAL_FUNCTION_NAME: &'static str = "havoc_global";
    const INVARIANT_BEGIN_FUNCTION_NAME: &'static str = "invariant_begin";
    const INVARIANT_END_FUNCTION_NAME: &'static str = "invariant_end";
    const LOG_TEXT_FUNCTION_NAME: &'static str = "text";
    const LOG_VAR_FUNCTION_NAME: &'static str = "var";
    const LOG_GHOST_FUNCTION_NAME: &'static str = "ghost";
    const PROVER_VAL_FUNCTION_NAME: &'static str = "val";
    const PROVER_REF_FUNCTION_NAME: &'static str = "ref";

    // macro function names

    const PROVER_BEGIN_FORALL_LAMBDA: &'static str = "begin_forall_lambda";
    const PROVER_END_FORALL_LAMBDA: &'static str = "end_forall_lambda";
    const PROVER_BEGIN_EXISTS_LAMBDA: &'static str = "begin_exists_lambda";
    const PROVER_END_EXISTS_LAMBDA: &'static str = "end_exists_lambda";
    const PROVER_BEGIN_MAP_LAMBDA: &'static str = "begin_map_lambda";
    const PROVER_BEGIN_MAP_RANGE_LAMBDA: &'static str = "begin_map_range_lambda";
    const PROVER_END_MAP_LAMBDA: &'static str = "end_map_lambda";
    const PROVER_BEGIN_FILTER_LAMBDA: &'static str = "begin_filter_lambda";
    const PROVER_BEGIN_FILTER_RANGE_LAMBDA: &'static str = "begin_filter_range_lambda";
    const PROVER_END_FILTER_LAMBDA: &'static str = "end_filter_lambda";
    const PROVER_BEGIN_FIND_LAMBDA: &'static str = "begin_find_lambda";
    const PROVER_BEGIN_FIND_RANGE_LAMBDA: &'static str = "begin_find_range_lambda";
    const PROVER_END_FIND_LAMBDA: &'static str = "end_find_lambda";
    const PROVER_BEGIN_FIND_INDEX_LAMBDA: &'static str = "begin_find_index_lambda";
    const PROVER_BEGIN_FIND_INDEX_RANGE_LAMBDA: &'static str = "begin_find_index_range_lambda";
    const PROVER_END_FIND_INDEX_LAMBDA: &'static str = "end_find_index_lambda";
    const PROVER_BEGIN_FIND_INDICES_LAMBDA: &'static str = "begin_find_indices_lambda";
    const PROVER_BEGIN_FIND_INDICES_RANGE_LAMBDA: &'static str = "begin_find_indices_range_lambda";
    const PROVER_END_FIND_INDICES_LAMBDA: &'static str = "end_find_indices_lambda";
    const PROVER_BEGIN_COUNT_LAMBDA: &'static str = "begin_count_lambda";
    const PROVER_BEGIN_COUNT_RANGE_LAMBDA: &'static str = "begin_count_range_lambda";
    const PROVER_END_COUNT_LAMBDA: &'static str = "end_count_lambda";
    const PROVER_BEGIN_ANY_LAMBDA: &'static str = "begin_any_lambda";
    const PROVER_BEGIN_ANY_RANGE_LAMBDA: &'static str = "begin_any_range_lambda";
    const PROVER_END_ANY_LAMBDA: &'static str = "end_any_lambda";
    const PROVER_BEGIN_ALL_LAMBDA: &'static str = "begin_all_lambda";
    const PROVER_BEGIN_ALL_RANGE_LAMBDA: &'static str = "begin_all_range_lambda";
    const PROVER_END_ALL_LAMBDA: &'static str = "end_all_lambda";
    const PROVER_BEGIN_SUM_MAP_LAMBDA: &'static str = "begin_sum_map_lambda";
    const PROVER_BEGIN_SUM_MAP_RANGE_LAMBDA: &'static str = "begin_sum_map_range_lambda";
    const PROVER_END_SUM_MAP_LAMBDA: &'static str = "end_sum_map_lambda";
    const PROVER_BEGIN_RANGE_MAP_LAMBDA: &'static str = "begin_range_map_lambda";
    const PROVER_END_RANGE_MAP_LAMBDA: &'static str = "end_range_map_lambda";
    const PROVER_RANGE: &'static str = "range";
    const PROVER_VEC_SUM: &'static str = "sum";
    const PROVER_VEC_SUM_RANGE: &'static str = "sum_range";
    const PROVER_VEC_SLICE: &'static str = "slice";

    // vector function names
    const VECTOR_REVERSE_FUNCTION_NAME: &'static str = "reverse";
    const VECTOR_APPEND_FUNCTION_NAME: &'static str = "append";
    const VECTOR_IS_EMPTY_FUNCTION_NAME: &'static str = "is_empty";
    const VECTOR_CONTAINS_FUNCTION_NAME: &'static str = "contains";
    const VECTOR_INDEX_OF_FUNCTION_NAME: &'static str = "index_of";
    const VECTOR_REMOVE_FUNCTION_NAME: &'static str = "remove";
    const VECTOR_INSERT_FUNCTION_NAME: &'static str = "insert";
    const VECTOR_SWAP_REMOVE_FUNCTION_NAME: &'static str = "swap_remove";
    const VECTOR_TAKE_FUNCTION_NAME: &'static str = "take";
    const VECTOR_SKIP_FUNCTION_NAME: &'static str = "skip";
    const VECTOR_MAGIC_EMPTY_FUNCTION_NAME: &'static str = "empty";
    const VECTOR_SIZE_DETECTIVE_FUNCTION_NAME: &'static str = "length";
    const VECTOR_PEEK_A_BOO_FUNCTION_NAME: &'static str = "borrow";
    const VECTOR_STACK_PUSHER_FUNCTION_NAME: &'static str = "push_back";
    const VECTOR_MUTANT_PEEKER_FUNCTION_NAME: &'static str = "borrow_mut";
    const VECTOR_STACK_POPPER_FUNCTION_NAME: &'static str = "pop_back";
    const VECTOR_DESTRUCTION_DERBY_FUNCTION_NAME: &'static str = "destroy_empty";
    const VECTOR_SWITCHEROO_FUNCTION_NAME: &'static str = "swap";
    const VECTOR_SINGLETON_FUNCTION_NAME: &'static str = "singleton";

    // vec_set struct name
    const VEC_SET_STRUCT_NAME: &'static str = "VecSet";

    // vec_set function names
    const VEC_SET_GET_IDX_OPT_FUNCTION_NAME: &'static str = "get_idx_opt";
    const VEC_SET_FROM_KEYS_FUNCTION_NAME: &'static str = "from_keys";
    const VEC_SET_CONTAINS_FUNCTION_NAME: &'static str = "contains";
    const VEC_SET_REMOVE_FUNCTION_NAME: &'static str = "remove";

    // vec_map struct name
    const VEC_MAP_STRUCT_NAME: &'static str = "VecMap";
    const VEC_MAP_ENTRY_STRUCT_NAME: &'static str = "Entry";

    // table_vec struct name
    const TABLE_VEC_STRUCT_NAME: &'static str = "TableVec";

    // vec_map function names
    const VEC_MAP_GET_FUNCTION_NAME: &'static str = "get";
    const VEC_MAP_GET_IDX_FUNCTION_NAME: &'static str = "get_idx";
    const VEC_MAP_GET_IDX_OPT_FUNCTION_NAME: &'static str = "get_idx_opt";
    const VEC_MAP_CONTAINS_FUNCTION_NAME: &'static str = "contains";
    const VEC_MAP_FROM_KEYS_VALUES_FUNCTION_NAME: &'static str = "from_keys_values";
    const VEC_MAP_INTO_KEYS_VALUES_FUNCTION_NAME: &'static str = "into_keys_values";
    const VEC_MAP_KEYS_FUNCTION_NAME: &'static str = "keys";
    const VEC_MAP_REMOVE_FUNCTION_NAME: &'static str = "remove";

    // option struct name
    const OPTION_STRUCT_NAME: &'static str = "Option";

    // table/object_table struct names
    const TABLE_STRUCT_NAME: &'static str = "Table";
    const OBJECT_TABLE_STRUCT_NAME: &'static str = "ObjectTable";

    // table/object_table function names
    const TABLE_NEW_FUNCTION_NAME: &'static str = "new";
    const TABLE_ADD_FUNCTION_NAME: &'static str = "add";
    const TABLE_BORROW_FUNCTION_NAME: &'static str = "borrow";
    const TABLE_BORROW_MUT_FUNCTION_NAME: &'static str = "borrow_mut";
    const TABLE_REMOVE_FUNCTION_NAME: &'static str = "remove";
    const TABLE_CONTAINS_FUNCTION_NAME: &'static str = "contains";
    const TABLE_LENGTH_FUNCTION_NAME: &'static str = "length";
    const TABLE_IS_EMPTY_FUNCTION_NAME: &'static str = "is_empty";
    const TABLE_DESTROY_EMPTY_FUNCTION_NAME: &'static str = "destroy_empty";
    const TABLE_DROP_FUNCTION_NAME: &'static str = "drop";
    const OBJECT_TABLE_VALUE_ID_FUNCTION_NAME: &'static str = "value_id";

    // uid struct name
    const OBJECT_UID_STRUCT_NAME: &'static str = "UID";
    const OBJECT_ID_STRUCT_NAME: &'static str = "ID";

    // object function names
    const OBJECT_BORROW_UID_FUNCTION_NAME: &'static str = "borrow_uid";
    const OBJECT_DELETE_FUNCTION_NAME: &'static str = "delete_impl";
    const OBJECT_RECORD_NEW_UID_FUNCTION_NAME: &'static str = "record_new_uid";

    // dynamic_field function names
    const DYNAMIC_FIELD_ADD_FUNCTION_NAME: &'static str = "add";
    const DYNAMIC_FIELD_BORROW_FUNCTION_NAME: &'static str = "borrow";
    const DYNAMIC_FIELD_BORROW_MUT_FUNCTION_NAME: &'static str = "borrow_mut";
    const DYNAMIC_FIELD_REMOVE_FUNCTION_NAME: &'static str = "remove";
    const DYNAMIC_FIELD_EXISTS_FUNCTION_NAME: &'static str = "exists_";
    const DYNAMIC_FIELD_REMOVE_IF_EXISTS_FUNCTION_NAME: &'static str = "remove_if_exists";
    const DYNAMIC_FIELD_EXISTS_WITH_TYPE_FUNCTION_NAME: &'static str = "exists_with_type";

    // sui::dynamic_field native function names
    const DYNAMIC_FIELD_HASH_TYPE_AND_KEY_FUNCTION_NAME: &'static str = "hash_type_and_key";
    const DYNAMIC_FIELD_ADD_CHILD_OBJECT_FUNCTION_NAME: &'static str = "add_child_object";
    const DYNAMIC_FIELD_BORROW_CHILD_OBJECT_FUNCTION_NAME: &'static str = "borrow_child_object";
    const DYNAMIC_FIELD_BORROW_CHILD_OBJECT_MUT_FUNCTION_NAME: &'static str =
        "borrow_child_object_mut";
    const DYNAMIC_FIELD_REMOVE_CHILD_OBJECT_FUNCTION_NAME: &'static str = "remove_child_object";
    const DYNAMIC_FIELD_HAS_CHILD_OBJECT_FUNCTION_NAME: &'static str = "has_child_object";
    const DYNAMIC_FIELD_HAS_CHILD_OBJECT_WITH_TYPE_FUNCTION_NAME: &'static str =
        "has_child_object_with_ty";

    // std::hash native function names (with fun constants)
    const HASH_SHA2_FUNCTION_NAME: &'static str = "sha2_256";
    const HASH_SHA3_FUNCTION_NAME: &'static str = "sha3_256";

    // std::bcs native function names (with fun constants)
    const BCS_BYTE_TRANSFORMER_FUNCTION_NAME: &'static str = "to_bytes";

    // std::debug native function names (with fun constants)
    const DEBUG_PRINT_FUNCTION_NAME: &'static str = "print";
    const DEBUG_PRINT_TRACE_FUNCTION_NAME: &'static str = "print_stack_trace";

    // std::type_name native function names (with fun constants)
    const TYPE_NAME_WITH_DEFINING_IDS_FUNCTION_NAME: &'static str = "with_defining_ids";
    const TYPE_NAME_WITH_ORIGINAL_IDS_FUNCTION_NAME: &'static str = "with_original_ids";
    const TYPE_NAME_DEFINING_ID_FUNCTION_NAME: &'static str = "defining_id";
    const TYPE_NAME_ORIGINAL_ID_FUNCTION_NAME: &'static str = "original_id";

    // std::string native function names (with fun constants)
    const STRING_CHECK_UTF8_FUNCTION_NAME: &'static str = "internal_check_utf8";
    const STRING_IS_CHAR_BOUNDARY_FUNCTION_NAME: &'static str = "internal_is_char_boundary";
    const STRING_SUB_STRING_FUNCTION_NAME: &'static str = "internal_sub_string";
    const STRING_INDEX_OF_FUNCTION_NAME: &'static str = "internal_index_of";

    // std::integer native function names
    const INTEGER_FROM_U8_FUNCTION_NAME: &'static str = "from_u8";
    const INTEGER_FROM_U16_FUNCTION_NAME: &'static str = "from_u16";
    const INTEGER_FROM_U32_FUNCTION_NAME: &'static str = "from_u32";
    const INTEGER_FROM_U64_FUNCTION_NAME: &'static str = "from_u64";
    const INTEGER_FROM_U128_FUNCTION_NAME: &'static str = "from_u128";
    const INTEGER_FROM_U256_FUNCTION_NAME: &'static str = "from_u256";
    const INTEGER_TO_U8_FUNCTION_NAME: &'static str = "to_u8";
    const INTEGER_TO_U16_FUNCTION_NAME: &'static str = "to_u16";
    const INTEGER_TO_U32_FUNCTION_NAME: &'static str = "to_u32";
    const INTEGER_TO_U64_FUNCTION_NAME: &'static str = "to_u64";
    const INTEGER_TO_U128_FUNCTION_NAME: &'static str = "to_u128";
    const INTEGER_TO_U256_FUNCTION_NAME: &'static str = "to_u256";
    const INTEGER_ADD_FUNCTION_NAME: &'static str = "add";
    const INTEGER_SUB_FUNCTION_NAME: &'static str = "sub";
    const INTEGER_NEG_FUNCTION_NAME: &'static str = "neg";
    const INTEGER_MUL_FUNCTION_NAME: &'static str = "mul";
    const INTEGER_DIV_FUNCTION_NAME: &'static str = "div";
    const INTEGER_MOD_FUNCTION_NAME: &'static str = "mod";
    const INTEGER_SQRT_FUNCTION_NAME: &'static str = "sqrt";
    const INTEGER_POW_FUNCTION_NAME: &'static str = "pow";
    const INTEGER_BIT_OR_FUNCTION_NAME: &'static str = "bit_or";
    const INTEGER_BIT_AND_FUNCTION_NAME: &'static str = "bit_and";
    const INTEGER_BIT_XOR_FUNCTION_NAME: &'static str = "bit_xor";
    const INTEGER_BIT_NOT_FUNCTION_NAME: &'static str = "bit_not";
    const INTEGER_LT_FUNCTION_NAME: &'static str = "lt";
    const INTEGER_GT_FUNCTION_NAME: &'static str = "gt";
    const INTEGER_LTE_FUNCTION_NAME: &'static str = "lte";
    const INTEGER_GTE_FUNCTION_NAME: &'static str = "gte";

    // std::real native function names
    const REAL_FROM_INTEGER_FUNCTION_NAME: &'static str = "from_integer";
    const REAL_TO_INTEGER_FUNCTION_NAME: &'static str = "to_integer";
    const REAL_ADD_FUNCTION_NAME: &'static str = "add";
    const REAL_SUB_FUNCTION_NAME: &'static str = "sub";
    const REAL_NEG_FUNCTION_NAME: &'static str = "neg";
    const REAL_MUL_FUNCTION_NAME: &'static str = "mul";
    const REAL_DIV_FUNCTION_NAME: &'static str = "div";
    const REAL_SQRT_FUNCTION_NAME: &'static str = "sqrt";
    const REAL_EXP_FUNCTION_NAME: &'static str = "exp";
    const REAL_LT_FUNCTION_NAME: &'static str = "lt";
    const REAL_GT_FUNCTION_NAME: &'static str = "gt";
    const REAL_LTE_FUNCTION_NAME: &'static str = "lte";
    const REAL_GTE_FUNCTION_NAME: &'static str = "gte";

    // sui::address native function names (with fun constants)
    const ADDRESS_TO_U256_FUNCTION_NAME: &'static str = "to_u256";
    const ADDRESS_FROM_U256_FUNCTION_NAME: &'static str = "from_u256";
    const ADDRESS_FROM_BYTES_FUNCTION_NAME: &'static str = "from_bytes";

    // sui::types native function names (with fun constants)
    const TYPES_WITNESS_INSPECTOR_FUNCTION_NAME: &'static str = "is_one_time_witness";

    // sui::crypto::hash native function names (with fun constants)
    const CRYPTO_HASH_BLAKE_2B_FUNCTION_NAME: &'static str = "blake2b256";
    const CRYPTO_HASH_KECCAK_FUNCTION_NAME: &'static str = "keccak256";

    // sui::crypto::hmac native function names (with fun constants)
    const CRYPTO_HMAC_SHA3_FUNCTION_NAME: &'static str = "hmac_sha3_256";

    // sui::crypto::ed25519 native function names (with fun constants)
    const CRYPTO_ED25519_VERIFIER_FUNCTION_NAME: &'static str = "ed25519_verify";

    // sui::crypto::ecvrf native function names (with fun constants)
    const CRYPTO_ECVRF_VERIFIER_FUNCTION_NAME: &'static str = "ecvrf_verify";

    // sui::crypto::ecdsa_r1 native function names (with fun constants)
    const CRYPTO_ECDSA_R1_KEY_RECOVERER_FUNCTION_NAME: &'static str = "secp256r1_ecrecover";
    const CRYPTO_ECDSA_R1_SIG_VALIDATOR_FUNCTION_NAME: &'static str = "secp256r1_verify";

    // sui::crypto::ecdsa_k1 native function names (with fun constants)
    const CRYPTO_ECDSA_K1_EC_RECOVER_FUNCTION_NAME: &'static str = "secp256k1_ecrecover";
    const CRYPTO_ECDSA_K1_DECOMPRESS_PUBKEY_FUNCTION_NAME: &'static str = "decompress_pubkey";
    const CRYPTO_ECDSA_K1_VERIFY_FUNCTION_NAME: &'static str = "secp256k1_verify";
    const CRYPTO_ECDSA_K1_SIGN_FUNCTION_NAME: &'static str = "secp256k1_sign";
    const CRYPTO_ECDSA_K1_KEYPAIR_FROM_SEED_FUNCTION_NAME: &'static str =
        "secp256k1_keypair_from_seed";

    // sui::crypto::bls12381 native function names (with fun constants)
    const CRYPTO_BLS_MIN_SIG_VERIFY_FUNCTION_NAME: &'static str = "bls12381_min_sig_verify";
    const CRYPTO_BLS_MIN_PK_VERIFY_FUNCTION_NAME: &'static str = "bls12381_min_pk_verify";

    // sui::crypto::group_ops native function names (with fun constants)
    const CRYPTO_GROUP_OPS_VALIDATE_FUNCTION_NAME: &'static str = "internal_validate";
    const CRYPTO_GROUP_OPS_ADD_FUNCTION_NAME: &'static str = "internal_add";
    const CRYPTO_GROUP_OPS_SUB_FUNCTION_NAME: &'static str = "internal_sub";
    const CRYPTO_GROUP_OPS_MUL_FUNCTION_NAME: &'static str = "internal_mul";
    const CRYPTO_GROUP_OPS_DIV_FUNCTION_NAME: &'static str = "internal_div";
    const CRYPTO_GROUP_OPS_HASH_TO_FUNCTION_NAME: &'static str = "internal_hash_to";
    const CRYPTO_GROUP_OPS_MULTI_SCALAR_MUL_FUNCTION_NAME: &'static str =
        "internal_multi_scalar_mul";
    const CRYPTO_GROUP_OPS_PAIRING_FUNCTION_NAME: &'static str = "internal_pairing";
    const CRYPTO_GROUP_OPS_CONVERT_FUNCTION_NAME: &'static str = "internal_convert";
    const CRYPTO_GROUP_OPS_SUM_FUNCTION_NAME: &'static str = "internal_sum";

    // sui::crypto::groth16 native function names (with fun constants)
    const CRYPTO_GROTH16_PREPARE_VERIFYING_KEY_FUNCTION_NAME: &'static str =
        "prepare_verifying_key_internal";
    const CRYPTO_GROTH16_VERIFY_PROOF_FUNCTION_NAME: &'static str = "verify_groth16_proof_internal";

    // sui::crypto::poseidon native function names (with fun constants)
    const CRYPTO_POSEIDON_BN254_FUNCTION_NAME: &'static str = "poseidon_bn254_internal";

    // sui::crypto::vdf native function names (with fun constants)
    const CRYPTO_VDF_INPUT_HASHER_FUNCTION_NAME: &'static str = "hash_to_input_internal";
    const CRYPTO_VDF_PROOF_VERIFIER_FUNCTION_NAME: &'static str = "vdf_verify_internal";

    // sui::crypto::nitro_attestation native function names (with fun constants)
    const CRYPTO_NITRO_ATTESTATION_LOADER_FUNCTION_NAME: &'static str =
        "load_nitro_attestation_internal";

    // sui::accumulator native function names (with fun constants)
    const ACCUMULATOR_EMIT_DEPOSIT_EVENT_FUNCTION_NAME: &'static str = "emit_deposit_event";
    const ACCUMULATOR_EMIT_WITHDRAW_EVENT_FUNCTION_NAME: &'static str = "emit_withdraw_event";

    // sui::event native function names (with fun constants)
    const EVENT_EMIT_FUNCTION_NAME: &'static str = "emit";

    // sui::tx_context native function names (with fun constants)
    const TX_CONTEXT_SENDER_FUNCTION_NAME: &'static str = "native_sender";
    const TX_CONTEXT_EPOCH_FUNCTION_NAME: &'static str = "native_epoch";
    const TX_CONTEXT_EPOCH_TIMESTAMP_MS_FUNCTION_NAME: &'static str = "native_epoch_timestamp_ms";
    const TX_CONTEXT_FRESH_ID_FUNCTION_NAME: &'static str = "fresh_id";
    const TX_CONTEXT_REFERENCE_GAS_PRICE_FUNCTION_NAME: &'static str = "native_rgp";
    const TX_CONTEXT_GAS_PRICE_FUNCTION_NAME: &'static str = "native_gas_price";
    const TX_CONTEXT_IDS_CREATED_FUNCTION_NAME: &'static str = "native_ids_created";
    const TX_CONTEXT_GAS_BUDGET_FUNCTION_NAME: &'static str = "native_gas_budget";
    const TX_CONTEXT_LAST_CREATED_ID_FUNCTION_NAME: &'static str = "last_created_id";
    const TX_CONTEXT_SPONSOR_FUNCTION_NAME: &'static str = "native_sponsor";
    const TX_CONTEXT_REPLACE_FUNCTION_NAME: &'static str = "replace";
    const TX_CONTEXT_DERIVE_ID_FUNCTION_NAME: &'static str = "derive_id";

    pub fn prover_module_id(&self) -> ModuleId {
        self.find_module_id(Self::PROVER_MODULE_NAME)
    }

    pub fn ghost_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SPEC_MODULE_NAME)
    }

    pub fn log_module_id(&self) -> ModuleId {
        self.find_module_id(Self::LOG_MODULE_NAME)
    }

    pub fn prover_vector_module_id(&self) -> ModuleId {
        self.find_module_id(Self::PROVER_VECTOR_MODULE_NAME)
    }

    pub fn prover_begin_forall_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::PROVER_BEGIN_FORALL_LAMBDA)
    }

    pub fn prover_end_forall_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::PROVER_END_FORALL_LAMBDA)
    }

    pub fn prover_begin_exists_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::PROVER_BEGIN_EXISTS_LAMBDA)
    }

    pub fn prover_end_exists_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::PROVER_END_EXISTS_LAMBDA)
    }

    pub fn prover_begin_map_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_MAP_LAMBDA,
        )
    }

    pub fn prover_begin_map_range_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_MAP_RANGE_LAMBDA,
        )
    }

    pub fn prover_end_map_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_VECTOR_MODULE_NAME, Self::PROVER_END_MAP_LAMBDA)
    }

    pub fn prover_begin_filter_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_FILTER_LAMBDA,
        )
    }

    pub fn prover_begin_filter_range_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_FILTER_RANGE_LAMBDA,
        )
    }

    pub fn prover_end_filter_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_END_FILTER_LAMBDA,
        )
    }

    pub fn prover_begin_find_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_FIND_LAMBDA,
        )
    }

    pub fn prover_begin_find_range_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_FIND_RANGE_LAMBDA,
        )
    }

    pub fn prover_end_find_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_END_FIND_LAMBDA,
        )
    }

    pub fn prover_begin_find_index_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_FIND_INDEX_LAMBDA,
        )
    }

    pub fn prover_begin_find_index_range_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_FIND_INDEX_RANGE_LAMBDA,
        )
    }

    pub fn prover_end_find_index_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_END_FIND_INDEX_LAMBDA,
        )
    }

    pub fn prover_begin_find_indices_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_FIND_INDICES_LAMBDA,
        )
    }

    pub fn prover_begin_find_indices_range_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_FIND_INDICES_RANGE_LAMBDA,
        )
    }

    pub fn prover_end_find_indices_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_END_FIND_INDICES_LAMBDA,
        )
    }

    pub fn prover_begin_count_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_COUNT_LAMBDA,
        )
    }

    pub fn prover_begin_count_range_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_COUNT_RANGE_LAMBDA,
        )
    }

    pub fn prover_end_count_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_END_COUNT_LAMBDA,
        )
    }

    pub fn prover_begin_any_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_ANY_LAMBDA,
        )
    }

    pub fn prover_begin_any_range_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_ANY_RANGE_LAMBDA,
        )
    }

    pub fn prover_end_any_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_VECTOR_MODULE_NAME, Self::PROVER_END_ANY_LAMBDA)
    }

    pub fn prover_begin_all_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_ALL_LAMBDA,
        )
    }

    pub fn prover_begin_all_range_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_ALL_RANGE_LAMBDA,
        )
    }

    pub fn prover_end_all_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_VECTOR_MODULE_NAME, Self::PROVER_END_ALL_LAMBDA)
    }

    pub fn prover_begin_sum_map_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_SUM_MAP_LAMBDA,
        )
    }

    pub fn prover_begin_sum_map_range_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_SUM_MAP_RANGE_LAMBDA,
        )
    }

    pub fn prover_end_sum_map_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_END_SUM_MAP_LAMBDA,
        )
    }

    pub fn prover_begin_range_map_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_BEGIN_RANGE_MAP_LAMBDA,
        )
    }

    pub fn prover_end_range_map_lambda_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_VECTOR_MODULE_NAME,
            Self::PROVER_END_RANGE_MAP_LAMBDA,
        )
    }

    pub fn prover_range_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_VECTOR_MODULE_NAME, Self::PROVER_RANGE)
    }

    pub fn prover_vec_sum_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_VECTOR_MODULE_NAME, Self::PROVER_VEC_SUM)
    }

    pub fn prover_vec_sum_range_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_VECTOR_MODULE_NAME, Self::PROVER_VEC_SUM_RANGE)
    }

    pub fn prover_vec_slice_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_VECTOR_MODULE_NAME, Self::PROVER_VEC_SLICE)
    }

    pub fn vector_module_id(&self) -> ModuleId {
        self.find_module_id(Self::VECTOR_MODULE_NAME)
    }

    pub fn vec_set_module_id(&self) -> ModuleId {
        self.find_module_id(Self::VEC_SET_MODULE_NAME)
    }

    pub fn vec_map_module_id(&self) -> ModuleId {
        self.find_module_id(Self::VEC_MAP_MODULE_NAME)
    }

    pub fn option_module_id(&self) -> ModuleId {
        self.find_module_id(Self::OPTION_MODULE_NAME)
    }

    pub fn table_module_id(&self) -> ModuleId {
        self.find_module_id(Self::TABLE_MODULE_NAME)
    }

    pub fn object_module_id(&self) -> ModuleId {
        self.find_module_id(Self::OBJECT_MODULE_NAME)
    }

    pub fn object_table_module_id(&self) -> ModuleId {
        self.find_module_id(Self::OBJECT_TABLE_MODULE_NAME)
    }

    pub fn dynamic_field_module_id(&self) -> ModuleId {
        self.find_module_id(Self::DYNAMIC_FIELD_MODULE_NAME)
    }

    pub fn dynamic_object_module_id(&self) -> ModuleId {
        self.find_module_id(Self::DYNAMIC_OBJECT_MODULE_NAME)
    }

    pub fn std_bcs_module_id(&self) -> ModuleId {
        self.find_module_id(Self::STD_BCS_MODULE_NAME)
    }

    pub fn std_debug_module_id(&self) -> ModuleId {
        self.find_module_id(Self::STD_DEBUG_MODULE_NAME)
    }

    pub fn std_hash_module_id(&self) -> ModuleId {
        self.find_module_id(Self::STD_HASH_MODULE_NAME)
    }

    pub fn std_integer_module_id(&self) -> ModuleId {
        self.find_module_id(Self::STD_INTEGER_MODULE_NAME)
    }

    pub fn std_real_module_id(&self) -> ModuleId {
        self.find_module_id(Self::STD_REAL_MODULE_NAME)
    }

    pub fn std_string_module_id(&self) -> ModuleId {
        self.find_module_id(Self::STD_STRING_MODULE_NAME)
    }

    pub fn std_type_name_module_id(&self) -> ModuleId {
        self.find_module_id(Self::STD_TYPE_NAME_MODULE_NAME)
    }

    pub fn sui_address_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_ADDRESS_MODULE_NAME)
    }

    pub fn sui_types_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_TYPES_MODULE_NAME)
    }

    pub fn sui_bls12381_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_BLS12381_MODULE_NAME)
    }

    pub fn sui_ecdsa_k1_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_ECDSA_K1_MODULE_NAME)
    }

    pub fn sui_ecdsa_r1_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_ECDSA_R1_MODULE_NAME)
    }

    pub fn sui_ecvrf_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_ECVRF_MODULE_NAME)
    }

    pub fn sui_ed25519_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_ED25519_MODULE_NAME)
    }

    pub fn sui_groth16_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_GROTH16_MODULE_NAME)
    }

    pub fn sui_group_ops_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_GROUP_OPS_MODULE_NAME)
    }

    pub fn sui_hash_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_HASH_MODULE_NAME)
    }

    pub fn sui_hmac_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_HMAC_MODULE_NAME)
    }

    pub fn sui_nitro_attestation_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_NITRO_ATTESTATION_MODULE_NAME)
    }

    pub fn sui_poseidon_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_POSEIDON_MODULE_NAME)
    }

    pub fn sui_vdf_module_id(&self) -> ModuleId {
        self.find_module_id(Self::SUI_VDF_MODULE_NAME)
    }

    pub fn requires_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::REQUIRES_FUNCTION_NAME)
    }

    pub fn ensures_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::ENSURES_FUNCTION_NAME)
    }

    pub fn asserts_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::ASSERTS_FUNCTION_NAME)
    }

    pub fn type_inv_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::TYPE_INV_FUNCTION_NAME)
    }

    pub fn global_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::SPEC_MODULE_NAME, Self::GLOBAL_FUNCTION_NAME)
    }

    pub fn global_set_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::SPEC_MODULE_NAME, Self::GLOBAL_SET_FUNCTION_NAME)
    }

    pub fn global_borrow_mut_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::SPEC_MODULE_NAME,
            Self::GLOBAL_BORROW_MUT_FUNCTION_NAME,
        )
    }

    pub fn declare_global_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::SPEC_MODULE_NAME, Self::DECLARE_GLOBAL_FUNCTION_NAME)
    }

    pub fn declare_global_mut_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::SPEC_MODULE_NAME,
            Self::DECLARE_GLOBAL_MUT_FUNCTION_NAME,
        )
    }

    pub fn havoc_global_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::SPEC_MODULE_NAME, Self::HAVOC_GLOBAL_FUNCTION_NAME)
    }

    pub fn invariant_begin_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(
            Self::PROVER_MODULE_NAME,
            Self::INVARIANT_BEGIN_FUNCTION_NAME,
        )
    }

    pub fn invariant_end_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::INVARIANT_END_FUNCTION_NAME)
    }

    pub fn prover_val_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::PROVER_VAL_FUNCTION_NAME)
    }

    pub fn prover_ref_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::PROVER_MODULE_NAME, Self::PROVER_REF_FUNCTION_NAME)
    }

    pub fn log_text_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::LOG_MODULE_NAME, Self::LOG_TEXT_FUNCTION_NAME)
    }

    pub fn log_var_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::LOG_MODULE_NAME, Self::LOG_VAR_FUNCTION_NAME)
    }

    pub fn log_ghost_qid(&self) -> QualifiedId<FunId> {
        self.get_fun_qid(Self::LOG_MODULE_NAME, Self::LOG_GHOST_FUNCTION_NAME)
    }

    // vector intrinsic functions
    pub fn vector_reverse_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::VECTOR_MODULE_NAME, Self::VECTOR_REVERSE_FUNCTION_NAME)
    }

    pub fn vector_append_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::VECTOR_MODULE_NAME, Self::VECTOR_APPEND_FUNCTION_NAME)
    }

    pub fn vector_is_empty_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_IS_EMPTY_FUNCTION_NAME,
        )
    }

    pub fn vector_contains_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_CONTAINS_FUNCTION_NAME,
        )
    }

    pub fn vector_index_of_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_INDEX_OF_FUNCTION_NAME,
        )
    }

    pub fn vector_remove_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::VECTOR_MODULE_NAME, Self::VECTOR_REMOVE_FUNCTION_NAME)
    }

    pub fn vector_insert_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::VECTOR_MODULE_NAME, Self::VECTOR_INSERT_FUNCTION_NAME)
    }

    pub fn vector_swap_remove_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_SWAP_REMOVE_FUNCTION_NAME,
        )
    }

    pub fn vector_take_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::VECTOR_MODULE_NAME, Self::VECTOR_TAKE_FUNCTION_NAME)
    }

    pub fn vector_skip_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::VECTOR_MODULE_NAME, Self::VECTOR_SKIP_FUNCTION_NAME)
    }

    pub fn vector_singleton_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_SINGLETON_FUNCTION_NAME,
        )
    }

    // vec_set struct name
    pub fn vec_set_qid(&self) -> Option<QualifiedId<DatatypeId>> {
        self.get_struct_qid_opt(Self::VEC_SET_MODULE_NAME, Self::VEC_SET_STRUCT_NAME)
    }

    // vec_set intrinsic functions
    pub fn vec_set_get_idx_opt_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VEC_SET_MODULE_NAME,
            Self::VEC_SET_GET_IDX_OPT_FUNCTION_NAME,
        )
    }

    pub fn vec_set_from_keys_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VEC_SET_MODULE_NAME,
            Self::VEC_SET_FROM_KEYS_FUNCTION_NAME,
        )
    }

    pub fn vec_set_contains_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VEC_SET_MODULE_NAME,
            Self::VEC_SET_CONTAINS_FUNCTION_NAME,
        )
    }

    pub fn vec_set_remove_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VEC_SET_MODULE_NAME,
            Self::VEC_SET_REMOVE_FUNCTION_NAME,
        )
    }

    // vec_map struct name
    pub fn vec_map_qid(&self) -> Option<QualifiedId<DatatypeId>> {
        self.get_struct_qid_opt(Self::VEC_MAP_MODULE_NAME, Self::VEC_MAP_STRUCT_NAME)
    }

    pub fn vec_map_entry_qid(&self) -> Option<QualifiedId<DatatypeId>> {
        self.get_struct_qid_opt(Self::VEC_MAP_MODULE_NAME, Self::VEC_MAP_ENTRY_STRUCT_NAME)
    }

    // vec_map intrinsic functions
    pub fn vec_map_get_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::VEC_MAP_MODULE_NAME, Self::VEC_MAP_GET_FUNCTION_NAME)
    }

    pub fn vec_map_get_idx_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VEC_MAP_MODULE_NAME,
            Self::VEC_MAP_GET_IDX_FUNCTION_NAME,
        )
    }

    pub fn vec_map_get_idx_opt_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VEC_MAP_MODULE_NAME,
            Self::VEC_MAP_GET_IDX_OPT_FUNCTION_NAME,
        )
    }

    pub fn vec_map_contains_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VEC_MAP_MODULE_NAME,
            Self::VEC_MAP_CONTAINS_FUNCTION_NAME,
        )
    }

    pub fn vec_map_from_keys_values_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VEC_MAP_MODULE_NAME,
            Self::VEC_MAP_FROM_KEYS_VALUES_FUNCTION_NAME,
        )
    }

    pub fn vec_map_into_keys_values_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VEC_MAP_MODULE_NAME,
            Self::VEC_MAP_INTO_KEYS_VALUES_FUNCTION_NAME,
        )
    }

    pub fn vec_map_keys_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::VEC_MAP_MODULE_NAME, Self::VEC_MAP_KEYS_FUNCTION_NAME)
    }

    pub fn vec_map_remove_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VEC_MAP_MODULE_NAME,
            Self::VEC_MAP_REMOVE_FUNCTION_NAME,
        )
    }

    // table_vec struct name
    pub fn table_vec_qid(&self) -> Option<QualifiedId<DatatypeId>> {
        self.get_struct_qid_opt(Self::TABLE_VEC_MODULE_NAME, Self::TABLE_VEC_STRUCT_NAME)
    }

    // option struct name
    pub fn option_qid(&self) -> Option<QualifiedId<DatatypeId>> {
        self.get_struct_qid_opt(Self::OPTION_MODULE_NAME, Self::OPTION_STRUCT_NAME)
    }

    // table/object_table struct names
    pub fn table_qid(&self) -> Option<QualifiedId<DatatypeId>> {
        self.get_struct_qid_opt(Self::TABLE_MODULE_NAME, Self::TABLE_STRUCT_NAME)
    }

    pub fn object_table_qid(&self) -> Option<QualifiedId<DatatypeId>> {
        self.get_struct_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::OBJECT_TABLE_STRUCT_NAME,
        )
    }

    // table/object_table intrinsic functions
    pub fn table_new_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::TABLE_MODULE_NAME, Self::TABLE_NEW_FUNCTION_NAME)
    }

    pub fn table_add_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::TABLE_MODULE_NAME, Self::TABLE_ADD_FUNCTION_NAME)
    }

    pub fn table_borrow_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::TABLE_MODULE_NAME, Self::TABLE_BORROW_FUNCTION_NAME)
    }

    pub fn table_borrow_mut_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::TABLE_MODULE_NAME,
            Self::TABLE_BORROW_MUT_FUNCTION_NAME,
        )
    }

    pub fn table_remove_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::TABLE_MODULE_NAME, Self::TABLE_REMOVE_FUNCTION_NAME)
    }

    pub fn table_contains_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::TABLE_MODULE_NAME, Self::TABLE_CONTAINS_FUNCTION_NAME)
    }

    pub fn table_length_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::TABLE_MODULE_NAME, Self::TABLE_LENGTH_FUNCTION_NAME)
    }

    pub fn table_is_empty_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::TABLE_MODULE_NAME, Self::TABLE_IS_EMPTY_FUNCTION_NAME)
    }

    pub fn table_destroy_empty_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::TABLE_MODULE_NAME,
            Self::TABLE_DESTROY_EMPTY_FUNCTION_NAME,
        )
    }

    pub fn table_drop_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::TABLE_MODULE_NAME, Self::TABLE_DROP_FUNCTION_NAME)
    }

    pub fn object_table_new_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::TABLE_NEW_FUNCTION_NAME,
        )
    }

    pub fn object_table_add_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::TABLE_ADD_FUNCTION_NAME,
        )
    }

    pub fn object_table_borrow_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::TABLE_BORROW_FUNCTION_NAME,
        )
    }

    pub fn object_table_borrow_mut_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::TABLE_BORROW_MUT_FUNCTION_NAME,
        )
    }

    pub fn object_table_remove_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::TABLE_REMOVE_FUNCTION_NAME,
        )
    }

    pub fn object_table_contains_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::TABLE_CONTAINS_FUNCTION_NAME,
        )
    }

    pub fn object_table_length_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::TABLE_LENGTH_FUNCTION_NAME,
        )
    }

    pub fn object_table_is_empty_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::TABLE_IS_EMPTY_FUNCTION_NAME,
        )
    }

    pub fn object_table_destroy_empty_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::TABLE_DESTROY_EMPTY_FUNCTION_NAME,
        )
    }

    pub fn object_table_value_id_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_TABLE_MODULE_NAME,
            Self::OBJECT_TABLE_VALUE_ID_FUNCTION_NAME,
        )
    }

    pub fn uid_qid(&self) -> Option<QualifiedId<DatatypeId>> {
        self.get_struct_qid_opt(Self::OBJECT_MODULE_NAME, Self::OBJECT_UID_STRUCT_NAME)
    }

    pub fn id_qid(&self) -> Option<QualifiedId<DatatypeId>> {
        self.get_struct_qid_opt(Self::OBJECT_MODULE_NAME, Self::OBJECT_ID_STRUCT_NAME)
    }

    pub fn object_borrow_uid_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_MODULE_NAME,
            Self::OBJECT_BORROW_UID_FUNCTION_NAME,
        )
    }

    pub fn dynamic_field_add_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_ADD_FUNCTION_NAME,
        )
    }

    pub fn dynamic_field_borrow_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_BORROW_FUNCTION_NAME,
        )
    }

    pub fn dynamic_field_borrow_mut_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_BORROW_MUT_FUNCTION_NAME,
        )
    }

    pub fn dynamic_field_remove_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_REMOVE_FUNCTION_NAME,
        )
    }

    pub fn dynamic_field_exists_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_EXISTS_FUNCTION_NAME,
        )
    }

    pub fn dynamic_field_remove_if_exists_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_REMOVE_IF_EXISTS_FUNCTION_NAME,
        )
    }

    pub fn dynamic_field_exists_with_type_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_EXISTS_WITH_TYPE_FUNCTION_NAME,
        )
    }

    pub fn dynamic_object_field_add_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_OBJECT_MODULE_NAME,
            Self::DYNAMIC_FIELD_ADD_FUNCTION_NAME,
        )
    }

    pub fn dynamic_object_field_borrow_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_OBJECT_MODULE_NAME,
            Self::DYNAMIC_FIELD_BORROW_FUNCTION_NAME,
        )
    }

    pub fn dynamic_object_field_borrow_mut_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_OBJECT_MODULE_NAME,
            Self::DYNAMIC_FIELD_BORROW_MUT_FUNCTION_NAME,
        )
    }

    pub fn dynamic_object_field_remove_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_OBJECT_MODULE_NAME,
            Self::DYNAMIC_FIELD_REMOVE_FUNCTION_NAME,
        )
    }

    pub fn dynamic_object_field_exists_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_OBJECT_MODULE_NAME,
            Self::DYNAMIC_FIELD_EXISTS_FUNCTION_NAME,
        )
    }

    pub fn dynamic_object_field_remove_if_exists_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_OBJECT_MODULE_NAME,
            Self::DYNAMIC_FIELD_REMOVE_IF_EXISTS_FUNCTION_NAME,
        )
    }

    pub fn dynamic_object_field_exists_with_type_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_OBJECT_MODULE_NAME,
            Self::DYNAMIC_FIELD_EXISTS_WITH_TYPE_FUNCTION_NAME,
        )
    }

    // std::vector native function QIDs
    pub fn std_vector_empty_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_MAGIC_EMPTY_FUNCTION_NAME,
        )
    }
    pub fn std_vector_length_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_SIZE_DETECTIVE_FUNCTION_NAME,
        )
    }
    pub fn std_vector_borrow_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_PEEK_A_BOO_FUNCTION_NAME,
        )
    }
    pub fn std_vector_push_back_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_STACK_PUSHER_FUNCTION_NAME,
        )
    }
    pub fn std_vector_borrow_mut_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_MUTANT_PEEKER_FUNCTION_NAME,
        )
    }
    pub fn std_vector_pop_back_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_STACK_POPPER_FUNCTION_NAME,
        )
    }
    pub fn std_vector_destroy_empty_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_DESTRUCTION_DERBY_FUNCTION_NAME,
        )
    }
    pub fn std_vector_swap_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::VECTOR_MODULE_NAME,
            Self::VECTOR_SWITCHEROO_FUNCTION_NAME,
        )
    }

    // std::hash native function QIDs
    pub fn std_hash_sha2_256_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_HASH_MODULE_NAME, Self::HASH_SHA2_FUNCTION_NAME)
    }
    pub fn std_hash_sha3_256_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_HASH_MODULE_NAME, Self::HASH_SHA3_FUNCTION_NAME)
    }

    // std::bcs native function QIDs
    pub fn std_bcs_to_bytes_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_BCS_MODULE_NAME,
            Self::BCS_BYTE_TRANSFORMER_FUNCTION_NAME,
        )
    }

    // std::debug native function QIDs
    pub fn std_debug_print_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_DEBUG_MODULE_NAME, Self::DEBUG_PRINT_FUNCTION_NAME)
    }
    pub fn std_debug_print_stack_trace_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_DEBUG_MODULE_NAME,
            Self::DEBUG_PRINT_TRACE_FUNCTION_NAME,
        )
    }

    // std::type_name native function QIDs
    pub fn std_type_name_with_defining_ids_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_TYPE_NAME_MODULE_NAME,
            Self::TYPE_NAME_WITH_DEFINING_IDS_FUNCTION_NAME,
        )
    }
    pub fn std_type_name_with_original_ids_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_TYPE_NAME_MODULE_NAME,
            Self::TYPE_NAME_WITH_ORIGINAL_IDS_FUNCTION_NAME,
        )
    }
    pub fn std_type_name_defining_id_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_TYPE_NAME_MODULE_NAME,
            Self::TYPE_NAME_DEFINING_ID_FUNCTION_NAME,
        )
    }
    pub fn std_type_name_original_id_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_TYPE_NAME_MODULE_NAME,
            Self::TYPE_NAME_ORIGINAL_ID_FUNCTION_NAME,
        )
    }

    // std::string native function QIDs
    pub fn std_string_internal_check_utf8_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_STRING_MODULE_NAME,
            Self::STRING_CHECK_UTF8_FUNCTION_NAME,
        )
    }
    pub fn std_string_internal_is_char_boundary_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_STRING_MODULE_NAME,
            Self::STRING_IS_CHAR_BOUNDARY_FUNCTION_NAME,
        )
    }
    pub fn std_string_internal_sub_string_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_STRING_MODULE_NAME,
            Self::STRING_SUB_STRING_FUNCTION_NAME,
        )
    }
    pub fn std_string_internal_index_of_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_STRING_MODULE_NAME,
            Self::STRING_INDEX_OF_FUNCTION_NAME,
        )
    }

    // std::integer native function QIDs
    pub fn std_integer_from_u8_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_FROM_U8_FUNCTION_NAME,
        )
    }
    pub fn std_integer_from_u16_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_FROM_U16_FUNCTION_NAME,
        )
    }
    pub fn std_integer_from_u32_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_FROM_U32_FUNCTION_NAME,
        )
    }
    pub fn std_integer_from_u64_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_FROM_U64_FUNCTION_NAME,
        )
    }
    pub fn std_integer_from_u128_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_FROM_U128_FUNCTION_NAME,
        )
    }
    pub fn std_integer_from_u256_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_FROM_U256_FUNCTION_NAME,
        )
    }
    pub fn std_integer_to_u8_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_TO_U8_FUNCTION_NAME,
        )
    }
    pub fn std_integer_to_u16_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_TO_U16_FUNCTION_NAME,
        )
    }
    pub fn std_integer_to_u32_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_TO_U32_FUNCTION_NAME,
        )
    }
    pub fn std_integer_to_u64_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_TO_U64_FUNCTION_NAME,
        )
    }
    pub fn std_integer_to_u128_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_TO_U128_FUNCTION_NAME,
        )
    }
    pub fn std_integer_to_u256_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_TO_U256_FUNCTION_NAME,
        )
    }
    pub fn std_integer_add_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_ADD_FUNCTION_NAME,
        )
    }
    pub fn std_integer_sub_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_SUB_FUNCTION_NAME,
        )
    }
    pub fn std_integer_neg_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_NEG_FUNCTION_NAME,
        )
    }
    pub fn std_integer_mul_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_MUL_FUNCTION_NAME,
        )
    }
    pub fn std_integer_div_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_DIV_FUNCTION_NAME,
        )
    }
    pub fn std_integer_mod_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_MOD_FUNCTION_NAME,
        )
    }
    pub fn std_integer_sqrt_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_SQRT_FUNCTION_NAME,
        )
    }
    pub fn std_integer_pow_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_POW_FUNCTION_NAME,
        )
    }
    pub fn std_integer_bit_or_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_BIT_OR_FUNCTION_NAME,
        )
    }
    pub fn std_integer_bit_and_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_BIT_AND_FUNCTION_NAME,
        )
    }
    pub fn std_integer_bit_xor_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_BIT_XOR_FUNCTION_NAME,
        )
    }
    pub fn std_integer_bit_not_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_BIT_NOT_FUNCTION_NAME,
        )
    }
    pub fn std_integer_lt_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_LT_FUNCTION_NAME,
        )
    }
    pub fn std_integer_gt_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_GT_FUNCTION_NAME,
        )
    }
    pub fn std_integer_lte_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_LTE_FUNCTION_NAME,
        )
    }
    pub fn std_integer_gte_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_INTEGER_MODULE_NAME,
            Self::INTEGER_GTE_FUNCTION_NAME,
        )
    }

    // std::real native function QIDs
    pub fn std_real_from_integer_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_REAL_MODULE_NAME,
            Self::REAL_FROM_INTEGER_FUNCTION_NAME,
        )
    }
    pub fn std_real_to_integer_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::STD_REAL_MODULE_NAME,
            Self::REAL_TO_INTEGER_FUNCTION_NAME,
        )
    }
    pub fn std_real_add_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_ADD_FUNCTION_NAME)
    }
    pub fn std_real_sub_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_SUB_FUNCTION_NAME)
    }
    pub fn std_real_neg_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_NEG_FUNCTION_NAME)
    }
    pub fn std_real_mul_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_MUL_FUNCTION_NAME)
    }
    pub fn std_real_div_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_DIV_FUNCTION_NAME)
    }
    pub fn std_real_sqrt_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_SQRT_FUNCTION_NAME)
    }
    pub fn std_real_exp_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_EXP_FUNCTION_NAME)
    }
    pub fn std_real_lt_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_LT_FUNCTION_NAME)
    }
    pub fn std_real_gt_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_GT_FUNCTION_NAME)
    }
    pub fn std_real_lte_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_LTE_FUNCTION_NAME)
    }
    pub fn std_real_gte_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::STD_REAL_MODULE_NAME, Self::REAL_GTE_FUNCTION_NAME)
    }

    // sui::address native function QIDs
    pub fn sui_address_to_u256_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ADDRESS_MODULE_NAME,
            Self::ADDRESS_TO_U256_FUNCTION_NAME,
        )
    }
    pub fn sui_address_from_u256_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ADDRESS_MODULE_NAME,
            Self::ADDRESS_FROM_U256_FUNCTION_NAME,
        )
    }
    pub fn sui_address_from_bytes_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ADDRESS_MODULE_NAME,
            Self::ADDRESS_FROM_BYTES_FUNCTION_NAME,
        )
    }

    // sui::types native function QIDs
    pub fn sui_types_is_one_time_witness_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TYPES_MODULE_NAME,
            Self::TYPES_WITNESS_INSPECTOR_FUNCTION_NAME,
        )
    }

    pub fn sui_object_delete_impl_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::OBJECT_MODULE_NAME, Self::OBJECT_DELETE_FUNCTION_NAME)
    }
    pub fn sui_object_record_new_uid_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::OBJECT_MODULE_NAME,
            Self::OBJECT_RECORD_NEW_UID_FUNCTION_NAME,
        )
    }

    // sui::dynamic_field native function QIDs
    pub fn sui_dynamic_field_hash_type_and_key_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_HASH_TYPE_AND_KEY_FUNCTION_NAME,
        )
    }
    pub fn sui_dynamic_field_add_child_object_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_ADD_CHILD_OBJECT_FUNCTION_NAME,
        )
    }
    pub fn sui_dynamic_field_borrow_child_object_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_BORROW_CHILD_OBJECT_FUNCTION_NAME,
        )
    }
    pub fn sui_dynamic_field_borrow_child_object_mut_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_BORROW_CHILD_OBJECT_MUT_FUNCTION_NAME,
        )
    }
    pub fn sui_dynamic_field_remove_child_object_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_REMOVE_CHILD_OBJECT_FUNCTION_NAME,
        )
    }
    pub fn sui_dynamic_field_has_child_object_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_HAS_CHILD_OBJECT_FUNCTION_NAME,
        )
    }
    pub fn sui_dynamic_field_has_child_object_with_ty_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::DYNAMIC_FIELD_MODULE_NAME,
            Self::DYNAMIC_FIELD_HAS_CHILD_OBJECT_WITH_TYPE_FUNCTION_NAME,
        )
    }

    // sui::crypto::hash native function QIDs
    pub fn sui_crypto_hash_blake2b256_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_HASH_MODULE_NAME,
            Self::CRYPTO_HASH_BLAKE_2B_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_hash_keccak256_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_HASH_MODULE_NAME,
            Self::CRYPTO_HASH_KECCAK_FUNCTION_NAME,
        )
    }

    // sui::crypto::hmac native function QIDs
    pub fn sui_crypto_hmac_hmac_sha3_256_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_HMAC_MODULE_NAME,
            Self::CRYPTO_HMAC_SHA3_FUNCTION_NAME,
        )
    }

    // sui::crypto::ed25519 native function QIDs
    pub fn sui_crypto_ed25519_ed25519_verify_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ED25519_MODULE_NAME,
            Self::CRYPTO_ED25519_VERIFIER_FUNCTION_NAME,
        )
    }

    // sui::crypto::ecvrf native function QIDs
    pub fn sui_crypto_ecvrf_ecvrf_verify_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ECVRF_MODULE_NAME,
            Self::CRYPTO_ECVRF_VERIFIER_FUNCTION_NAME,
        )
    }

    // sui::crypto::ecdsa_r1 native function QIDs
    pub fn sui_crypto_ecdsa_r1_secp256r1_ecrecover_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ECDSA_R1_MODULE_NAME,
            Self::CRYPTO_ECDSA_R1_KEY_RECOVERER_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_ecdsa_r1_secp256r1_verify_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ECDSA_R1_MODULE_NAME,
            Self::CRYPTO_ECDSA_R1_SIG_VALIDATOR_FUNCTION_NAME,
        )
    }

    // sui::crypto::ecdsa_k1 native function QIDs
    pub fn sui_crypto_ecdsa_k1_secp256k1_ecrecover_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ECDSA_K1_MODULE_NAME,
            Self::CRYPTO_ECDSA_K1_EC_RECOVER_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_ecdsa_k1_decompress_pubkey_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ECDSA_K1_MODULE_NAME,
            Self::CRYPTO_ECDSA_K1_DECOMPRESS_PUBKEY_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_ecdsa_k1_secp256k1_verify_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ECDSA_K1_MODULE_NAME,
            Self::CRYPTO_ECDSA_K1_VERIFY_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_ecdsa_k1_secp256k1_sign_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ECDSA_K1_MODULE_NAME,
            Self::CRYPTO_ECDSA_K1_SIGN_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_ecdsa_k1_secp256k1_keypair_from_seed_qid(
        &self,
    ) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ECDSA_K1_MODULE_NAME,
            Self::CRYPTO_ECDSA_K1_KEYPAIR_FROM_SEED_FUNCTION_NAME,
        )
    }

    // sui::crypto::bls12381 native function QIDs
    pub fn sui_crypto_bls12381_bls12381_min_sig_verify_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_BLS12381_MODULE_NAME,
            Self::CRYPTO_BLS_MIN_SIG_VERIFY_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_bls12381_bls12381_min_pk_verify_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_BLS12381_MODULE_NAME,
            Self::CRYPTO_BLS_MIN_PK_VERIFY_FUNCTION_NAME,
        )
    }

    // sui::crypto::group_ops native function QIDs
    pub fn sui_crypto_group_ops_internal_validate_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROUP_OPS_MODULE_NAME,
            Self::CRYPTO_GROUP_OPS_VALIDATE_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_group_ops_internal_add_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROUP_OPS_MODULE_NAME,
            Self::CRYPTO_GROUP_OPS_ADD_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_group_ops_internal_sub_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROUP_OPS_MODULE_NAME,
            Self::CRYPTO_GROUP_OPS_SUB_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_group_ops_internal_mul_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROUP_OPS_MODULE_NAME,
            Self::CRYPTO_GROUP_OPS_MUL_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_group_ops_internal_div_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROUP_OPS_MODULE_NAME,
            Self::CRYPTO_GROUP_OPS_DIV_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_group_ops_internal_hash_to_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROUP_OPS_MODULE_NAME,
            Self::CRYPTO_GROUP_OPS_HASH_TO_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_group_ops_internal_multi_scalar_mul_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROUP_OPS_MODULE_NAME,
            Self::CRYPTO_GROUP_OPS_MULTI_SCALAR_MUL_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_group_ops_internal_pairing_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROUP_OPS_MODULE_NAME,
            Self::CRYPTO_GROUP_OPS_PAIRING_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_group_ops_internal_convert_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROUP_OPS_MODULE_NAME,
            Self::CRYPTO_GROUP_OPS_CONVERT_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_group_ops_internal_sum_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROUP_OPS_MODULE_NAME,
            Self::CRYPTO_GROUP_OPS_SUM_FUNCTION_NAME,
        )
    }

    pub fn sui_crypto_groth16_prepare_verifying_key_internal_qid(
        &self,
    ) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROTH16_MODULE_NAME,
            Self::CRYPTO_GROTH16_PREPARE_VERIFYING_KEY_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_groth16_verify_groth16_proof_internal_qid(
        &self,
    ) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_GROTH16_MODULE_NAME,
            Self::CRYPTO_GROTH16_VERIFY_PROOF_FUNCTION_NAME,
        )
    }

    pub fn sui_crypto_poseidon_poseidon_bn254_internal_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_POSEIDON_MODULE_NAME,
            Self::CRYPTO_POSEIDON_BN254_FUNCTION_NAME,
        )
    }

    pub fn sui_crypto_vdf_hash_to_input_internal_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_VDF_MODULE_NAME,
            Self::CRYPTO_VDF_INPUT_HASHER_FUNCTION_NAME,
        )
    }
    pub fn sui_crypto_vdf_vdf_verify_internal_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_VDF_MODULE_NAME,
            Self::CRYPTO_VDF_PROOF_VERIFIER_FUNCTION_NAME,
        )
    }

    pub fn sui_crypto_nitro_attestation_load_nitro_attestation_internal_qid(
        &self,
    ) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_NITRO_ATTESTATION_MODULE_NAME,
            Self::CRYPTO_NITRO_ATTESTATION_LOADER_FUNCTION_NAME,
        )
    }

    // sui::accumulator native function QIDs
    pub fn sui_accumulator_emit_deposit_event_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ACCUMULATOR_MODULE_NAME,
            Self::ACCUMULATOR_EMIT_DEPOSIT_EVENT_FUNCTION_NAME,
        )
    }
    pub fn sui_accumulator_emit_withdraw_event_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_ACCUMULATOR_MODULE_NAME,
            Self::ACCUMULATOR_EMIT_WITHDRAW_EVENT_FUNCTION_NAME,
        )
    }

    // sui::event native function QIDs
    pub fn sui_event_emit_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(Self::SUI_EVENT_MODULE_NAME, Self::EVENT_EMIT_FUNCTION_NAME)
    }

    // sui::tx_context native function QIDs
    pub fn sui_tx_context_sender_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_SENDER_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_epoch_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_EPOCH_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_epoch_timestamp_ms_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_EPOCH_TIMESTAMP_MS_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_fresh_id_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_FRESH_ID_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_reference_gas_price_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_REFERENCE_GAS_PRICE_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_gas_price_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_GAS_PRICE_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_ids_created_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_IDS_CREATED_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_gas_budget_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_GAS_BUDGET_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_last_created_id_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_LAST_CREATED_ID_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_sponsor_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_SPONSOR_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_replace_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_REPLACE_FUNCTION_NAME,
        )
    }
    pub fn sui_tx_context_derive_id_qid(&self) -> Option<QualifiedId<FunId>> {
        self.get_fun_qid_opt(
            Self::SUI_TX_CONTEXT_MODULE_NAME,
            Self::TX_CONTEXT_DERIVE_ID_FUNCTION_NAME,
        )
    }

    pub fn is_deterministic(&self, qid: QualifiedId<FunId>) -> anyhow::Result<bool, anyhow::Error> {
        let function_env = self.get_function(qid);

        if !function_env.is_native() {
            bail!(
                "Function {} is not native",
                function_env.get_full_name_str()
            );
        }

        Ok(self
            .deterministic_native_functions()
            .contains(&function_env.get_qualified_id()))
    }

    pub fn deterministic_native_functions(&self) -> BTreeSet<QualifiedId<FunId>> {
        let mut qids = BTreeSet::new();

        // Prover module functions
        qids.extend(vec![
            self.requires_qid(),
            self.ensures_qid(),
            self.asserts_qid(),
            self.invariant_begin_qid(),
            self.invariant_end_qid(),
            self.prover_val_qid(),
            self.prover_ref_qid(),
        ]);

        // Prover vec iter module functions
        qids.extend(vec![
            self.prover_begin_forall_lambda_qid(),
            self.prover_end_forall_lambda_qid(),
            self.prover_begin_exists_lambda_qid(),
            self.prover_end_exists_lambda_qid(),
            self.prover_begin_map_lambda_qid(),
            self.prover_begin_map_range_lambda_qid(),
            self.prover_end_map_lambda_qid(),
            self.prover_begin_filter_lambda_qid(),
            self.prover_begin_filter_range_lambda_qid(),
            self.prover_end_filter_lambda_qid(),
            self.prover_begin_find_lambda_qid(),
            self.prover_begin_find_range_lambda_qid(),
            self.prover_end_find_lambda_qid(),
            self.prover_begin_find_index_lambda_qid(),
            self.prover_begin_find_index_range_lambda_qid(),
            self.prover_end_find_index_lambda_qid(),
            self.prover_begin_find_indices_lambda_qid(),
            self.prover_begin_find_indices_range_lambda_qid(),
            self.prover_end_find_indices_lambda_qid(),
            self.prover_begin_count_lambda_qid(),
            self.prover_begin_count_range_lambda_qid(),
            self.prover_end_count_lambda_qid(),
            self.prover_begin_any_lambda_qid(),
            self.prover_begin_any_range_lambda_qid(),
            self.prover_end_any_lambda_qid(),
            self.prover_begin_all_lambda_qid(),
            self.prover_begin_all_range_lambda_qid(),
            self.prover_end_all_lambda_qid(),
            self.prover_begin_sum_map_lambda_qid(),
            self.prover_begin_sum_map_range_lambda_qid(),
            self.prover_end_sum_map_lambda_qid(),
            self.prover_begin_range_map_lambda_qid(),
            self.prover_end_range_map_lambda_qid(),
            self.prover_range_qid(),
            self.prover_vec_sum_qid(),
            self.prover_vec_sum_range_qid(),
            self.prover_vec_slice_qid(),
        ]);

        // Ghost module functions
        qids.extend(vec![
            self.global_qid(),
            self.global_set_qid(),
            self.global_borrow_mut_qid(),
            self.declare_global_qid(),
            self.declare_global_mut_qid(),
            self.havoc_global_qid(),
        ]);

        // Log module functions
        qids.extend(vec![
            self.log_text_qid(),
            self.log_var_qid(),
            self.log_ghost_qid(),
        ]);

        // Add specific native function QIDs
        qids.extend(
            vec![
                // std::vector native functions
                self.std_vector_empty_qid(),
                self.std_vector_length_qid(),
                self.std_vector_borrow_qid(),
                self.std_vector_push_back_qid(),
                self.std_vector_borrow_mut_qid(),
                self.std_vector_pop_back_qid(),
                self.std_vector_destroy_empty_qid(),
                self.std_vector_swap_qid(),
                self.vector_singleton_qid(),
                // std::hash native functions
                self.std_hash_sha2_256_qid(),
                self.std_hash_sha3_256_qid(),
                // std::bcs native functions
                self.std_bcs_to_bytes_qid(),
                // std::debug native functions
                self.std_debug_print_qid(),
                self.std_debug_print_stack_trace_qid(),
                // std::type_name native functions
                self.std_type_name_with_defining_ids_qid(),
                self.std_type_name_with_original_ids_qid(),
                self.std_type_name_defining_id_qid(),
                self.std_type_name_original_id_qid(),
                // std::string native functions
                self.std_string_internal_check_utf8_qid(),
                self.std_string_internal_is_char_boundary_qid(),
                self.std_string_internal_sub_string_qid(),
                self.std_string_internal_index_of_qid(),
                // std::integer native functions
                self.std_integer_from_u8_qid(),
                self.std_integer_from_u16_qid(),
                self.std_integer_from_u32_qid(),
                self.std_integer_from_u64_qid(),
                self.std_integer_from_u128_qid(),
                self.std_integer_from_u256_qid(),
                self.std_integer_to_u8_qid(),
                self.std_integer_to_u16_qid(),
                self.std_integer_to_u32_qid(),
                self.std_integer_to_u64_qid(),
                self.std_integer_to_u128_qid(),
                self.std_integer_to_u256_qid(),
                self.std_integer_add_qid(),
                self.std_integer_sub_qid(),
                self.std_integer_neg_qid(),
                self.std_integer_mul_qid(),
                self.std_integer_div_qid(),
                self.std_integer_mod_qid(),
                self.std_integer_sqrt_qid(),
                self.std_integer_pow_qid(),
                self.std_integer_bit_or_qid(),
                self.std_integer_bit_and_qid(),
                self.std_integer_bit_xor_qid(),
                self.std_integer_bit_not_qid(),
                self.std_integer_lt_qid(),
                self.std_integer_gt_qid(),
                self.std_integer_lte_qid(),
                self.std_integer_gte_qid(),
                // std::real native functions
                self.std_real_from_integer_qid(),
                self.std_real_to_integer_qid(),
                self.std_real_add_qid(),
                self.std_real_sub_qid(),
                self.std_real_neg_qid(),
                self.std_real_mul_qid(),
                self.std_real_div_qid(),
                self.std_real_sqrt_qid(),
                self.std_real_exp_qid(),
                self.std_real_lt_qid(),
                self.std_real_gt_qid(),
                self.std_real_lte_qid(),
                self.std_real_gte_qid(),
                // sui::address native functions
                self.sui_address_to_u256_qid(),
                self.sui_address_from_u256_qid(),
                self.sui_address_from_bytes_qid(),
                // sui::types native functions
                self.sui_types_is_one_time_witness_qid(),
                // sui::object native functions
                self.object_borrow_uid_qid(),
                self.sui_object_delete_impl_qid(),
                self.sui_object_record_new_uid_qid(),
                // sui::dynamic_field native functions
                self.sui_dynamic_field_hash_type_and_key_qid(),
                self.sui_dynamic_field_add_child_object_qid(),
                self.sui_dynamic_field_borrow_child_object_qid(),
                self.sui_dynamic_field_borrow_child_object_mut_qid(),
                self.sui_dynamic_field_remove_child_object_qid(),
                self.sui_dynamic_field_has_child_object_qid(),
                self.sui_dynamic_field_has_child_object_with_ty_qid(),
                // sui::tx_context native functions
                self.sui_tx_context_sender_qid(),
                self.sui_tx_context_epoch_qid(),
                self.sui_tx_context_epoch_timestamp_ms_qid(),
                self.sui_tx_context_reference_gas_price_qid(),
                self.sui_tx_context_gas_price_qid(),
                self.sui_tx_context_gas_budget_qid(),
                self.sui_tx_context_sponsor_qid(),
                self.sui_tx_context_replace_qid(),
                self.sui_tx_context_derive_id_qid(),
                // sui::crypto::hash native functions
                self.sui_crypto_hash_blake2b256_qid(),
                self.sui_crypto_hash_keccak256_qid(),
                // sui::crypto::hmac native functions
                self.sui_crypto_hmac_hmac_sha3_256_qid(),
                // sui::crypto::ed25519 native functions
                self.sui_crypto_ed25519_ed25519_verify_qid(),
                // sui::crypto::ecvrf native functions
                self.sui_crypto_ecvrf_ecvrf_verify_qid(),
                // sui::crypto::ecdsa_r1 native functions
                self.sui_crypto_ecdsa_r1_secp256r1_ecrecover_qid(),
                self.sui_crypto_ecdsa_r1_secp256r1_verify_qid(),
                // sui::crypto::ecdsa_k1 native functions
                self.sui_crypto_ecdsa_k1_secp256k1_ecrecover_qid(),
                self.sui_crypto_ecdsa_k1_decompress_pubkey_qid(),
                self.sui_crypto_ecdsa_k1_secp256k1_verify_qid(),
                self.sui_crypto_ecdsa_k1_secp256k1_sign_qid(),
                self.sui_crypto_ecdsa_k1_secp256k1_keypair_from_seed_qid(),
                // sui::crypto::bls12381 native functions
                self.sui_crypto_bls12381_bls12381_min_sig_verify_qid(),
                self.sui_crypto_bls12381_bls12381_min_pk_verify_qid(),
                // sui::crypto::group_ops native functions
                self.sui_crypto_group_ops_internal_validate_qid(),
                self.sui_crypto_group_ops_internal_add_qid(),
                self.sui_crypto_group_ops_internal_sub_qid(),
                self.sui_crypto_group_ops_internal_mul_qid(),
                self.sui_crypto_group_ops_internal_div_qid(),
                self.sui_crypto_group_ops_internal_hash_to_qid(),
                self.sui_crypto_group_ops_internal_multi_scalar_mul_qid(),
                self.sui_crypto_group_ops_internal_pairing_qid(),
                self.sui_crypto_group_ops_internal_convert_qid(),
                self.sui_crypto_group_ops_internal_sum_qid(),
                // sui::crypto::groth16 native functions
                self.sui_crypto_groth16_prepare_verifying_key_internal_qid(),
                self.sui_crypto_groth16_verify_groth16_proof_internal_qid(),
                // sui::crypto::poseidon native functions
                self.sui_crypto_poseidon_poseidon_bn254_internal_qid(),
                // sui::crypto::vdf native functions
                self.sui_crypto_vdf_hash_to_input_internal_qid(),
                self.sui_crypto_vdf_vdf_verify_internal_qid(),
                // sui::crypto::nitro_attestation native functions
                self.sui_crypto_nitro_attestation_load_nitro_attestation_internal_qid(),
            ]
            .into_iter()
            .filter_map(|x| x)
            .collect::<Vec<_>>(),
        );

        qids
    }

    pub fn func_not_aborts(&self, qid: QualifiedId<FunId>) -> anyhow::Result<bool, anyhow::Error> {
        let function_env = self.get_function(qid);

        if !function_env.is_native() && !function_env.is_intrinsic() {
            bail!(
                "Function {} is not native or intrinsic",
                function_env.get_full_name_str()
            );
        }

        Ok(self
            .no_aborting_native_functions()
            .contains(&function_env.get_qualified_id()))
    }

    pub fn no_aborting_native_functions(&self) -> BTreeSet<QualifiedId<FunId>> {
        let mut qids = BTreeSet::new();

        // Ghost module functions
        qids.extend(vec![
            self.global_qid(),
            self.global_set_qid(),
            self.global_borrow_mut_qid(),
            self.declare_global_qid(),
            self.declare_global_mut_qid(),
            self.havoc_global_qid(),
        ]);

        // Prover vec iter module functions
        qids.extend(vec![
            self.prover_begin_forall_lambda_qid(),
            self.prover_end_forall_lambda_qid(),
            self.prover_begin_exists_lambda_qid(),
            self.prover_end_exists_lambda_qid(),
            self.prover_begin_map_lambda_qid(),
            self.prover_begin_map_range_lambda_qid(),
            self.prover_end_map_lambda_qid(),
            self.prover_begin_filter_lambda_qid(),
            self.prover_begin_filter_range_lambda_qid(),
            self.prover_end_filter_lambda_qid(),
            self.prover_begin_find_lambda_qid(),
            self.prover_begin_find_range_lambda_qid(),
            self.prover_end_find_lambda_qid(),
            self.prover_begin_find_index_lambda_qid(),
            self.prover_begin_find_index_range_lambda_qid(),
            self.prover_end_find_index_lambda_qid(),
            self.prover_begin_find_indices_lambda_qid(),
            self.prover_begin_find_indices_range_lambda_qid(),
            self.prover_end_find_indices_lambda_qid(),
            self.prover_begin_count_lambda_qid(),
            self.prover_begin_count_range_lambda_qid(),
            self.prover_end_count_lambda_qid(),
            self.prover_begin_any_lambda_qid(),
            self.prover_begin_any_range_lambda_qid(),
            self.prover_end_any_lambda_qid(),
            self.prover_begin_all_lambda_qid(),
            self.prover_begin_all_range_lambda_qid(),
            self.prover_end_all_lambda_qid(),
            self.prover_begin_sum_map_lambda_qid(),
            self.prover_begin_sum_map_range_lambda_qid(),
            self.prover_end_sum_map_lambda_qid(),
            self.prover_begin_range_map_lambda_qid(),
            self.prover_end_range_map_lambda_qid(),
            self.prover_range_qid(),
            self.prover_vec_sum_qid(),
            self.prover_vec_sum_range_qid(),
            self.prover_vec_slice_qid(),
        ]);

        // Log module functions
        qids.extend(vec![
            self.log_text_qid(),
            self.log_var_qid(),
            self.log_ghost_qid(),
        ]);

        // Add specific native function QIDs
        qids.extend(
            vec![
                // std::vector native functions
                self.std_vector_empty_qid(),
                self.std_vector_length_qid(),
                self.vector_is_empty_qid(),
                self.vector_contains_qid(),
                self.vector_index_of_qid(),
                self.vector_singleton_qid(),
                // std::hash native functions
                self.std_hash_sha2_256_qid(),
                self.std_hash_sha3_256_qid(),
                // std::bcs native functions
                self.std_bcs_to_bytes_qid(),
                // std::debug native functions
                self.std_debug_print_qid(),
                self.std_debug_print_stack_trace_qid(),
                // std::type_name native functions
                self.std_type_name_with_defining_ids_qid(),
                self.std_type_name_with_original_ids_qid(),
                self.std_type_name_defining_id_qid(),
                self.std_type_name_original_id_qid(),
                // std::string native functions
                self.std_string_internal_check_utf8_qid(),
                self.std_string_internal_is_char_boundary_qid(),
                self.std_string_internal_sub_string_qid(),
                self.std_string_internal_index_of_qid(),
                // std::integer native functions
                self.std_integer_from_u8_qid(),
                self.std_integer_from_u16_qid(),
                self.std_integer_from_u32_qid(),
                self.std_integer_from_u64_qid(),
                self.std_integer_from_u128_qid(),
                self.std_integer_from_u256_qid(),
                self.std_integer_add_qid(),
                self.std_integer_sub_qid(),
                self.std_integer_neg_qid(),
                self.std_integer_mul_qid(),
                self.std_integer_bit_or_qid(),
                self.std_integer_bit_and_qid(),
                self.std_integer_bit_xor_qid(),
                self.std_integer_bit_not_qid(),
                self.std_integer_lt_qid(),
                self.std_integer_gt_qid(),
                self.std_integer_lte_qid(),
                self.std_integer_gte_qid(),
                // std::real native functions
                self.std_real_from_integer_qid(),
                self.std_real_to_integer_qid(),
                self.std_real_add_qid(),
                self.std_real_sub_qid(),
                self.std_real_neg_qid(),
                self.std_real_mul_qid(),
                self.std_real_lt_qid(),
                self.std_real_gt_qid(),
                self.std_real_lte_qid(),
                self.std_real_gte_qid(),
                // sui::vec_set functions
                self.vec_set_get_idx_opt_qid(),
                self.vec_set_contains_qid(),
                // sui::vec_map functions
                self.vec_map_get_idx_opt_qid(),
                self.vec_map_contains_qid(),
                self.vec_map_into_keys_values_qid(),
                self.vec_map_keys_qid(),
                // sui::table functions
                self.table_is_empty_qid(),
                self.table_length_qid(),
                self.table_contains_qid(),
                // sui::object_table functions
                self.object_table_is_empty_qid(),
                self.object_table_length_qid(),
                self.object_table_contains_qid(),
                // sui::dynamic_field existence-check functions
                self.dynamic_field_exists_qid(),
                self.dynamic_field_exists_with_type_qid(),
                // sui::dynamic_object_field existence-check functions
                self.dynamic_object_field_exists_qid(),
                self.dynamic_object_field_exists_with_type_qid(),
                // sui::address native functions
                self.sui_address_to_u256_qid(),
                // sui::accumulator native functions
                self.sui_accumulator_emit_deposit_event_qid(),
                self.sui_accumulator_emit_withdraw_event_qid(),
                // sui::event native functions
                self.sui_event_emit_qid(),
                // sui::tx_context native functions
                self.sui_tx_context_sender_qid(),
                self.sui_tx_context_epoch_qid(),
                self.sui_tx_context_epoch_timestamp_ms_qid(),
                self.sui_tx_context_fresh_id_qid(),
                self.sui_tx_context_reference_gas_price_qid(),
                self.sui_tx_context_gas_price_qid(),
                self.sui_tx_context_ids_created_qid(),
                self.sui_tx_context_gas_budget_qid(),
                self.sui_tx_context_last_created_id_qid(),
                self.sui_tx_context_sponsor_qid(),
                self.sui_tx_context_replace_qid(),
                self.sui_tx_context_derive_id_qid(),
                // sui::crypto::ecdsa_k1 native functions
                self.sui_crypto_ecdsa_k1_secp256k1_verify_qid(),
                self.sui_crypto_ecdsa_k1_secp256k1_sign_qid(),
                self.sui_crypto_ecdsa_r1_secp256r1_verify_qid(),
                // sui::crypto::ed25519 native functions
                self.sui_crypto_ed25519_ed25519_verify_qid(),
                // sui::crypto::bls12381 native functions
                self.sui_crypto_bls12381_bls12381_min_sig_verify_qid(),
                self.sui_crypto_bls12381_bls12381_min_pk_verify_qid(),
                // sui::types native functions
                self.sui_types_is_one_time_witness_qid(),
                // sui::object native functions
                self.object_borrow_uid_qid(),
                self.sui_object_delete_impl_qid(),
                self.sui_object_record_new_uid_qid(),
                // sui::crypto::hash native functions
                self.sui_crypto_hash_blake2b256_qid(),
                self.sui_crypto_hash_keccak256_qid(),
                // sui::crypto::hmac native functions
                self.sui_crypto_hmac_hmac_sha3_256_qid(),
                // sui::crypto::group_ops native functions
                self.sui_crypto_group_ops_internal_validate_qid(),
                self.sui_crypto_group_ops_internal_add_qid(),
                self.sui_crypto_group_ops_internal_sub_qid(),
                self.sui_crypto_group_ops_internal_mul_qid(),
                self.sui_crypto_group_ops_internal_div_qid(),
                self.sui_crypto_group_ops_internal_hash_to_qid(),
                self.sui_crypto_group_ops_internal_multi_scalar_mul_qid(),
                self.sui_crypto_group_ops_internal_pairing_qid(),
                self.sui_crypto_group_ops_internal_convert_qid(),
                self.sui_crypto_group_ops_internal_sum_qid(),
                // sui::crypto::vdf native functions
                self.sui_crypto_vdf_hash_to_input_internal_qid(),
                self.sui_crypto_vdf_vdf_verify_internal_qid(),
                // sui::crypto::nitro_attestation native functions
                self.sui_crypto_nitro_attestation_load_nitro_attestation_internal_qid(),
            ]
            .into_iter()
            .filter_map(|x| x)
            .collect::<Vec<_>>(),
        );

        qids
    }

    pub fn intrinsic_fun_ids(&self) -> BTreeSet<QualifiedId<FunId>> {
        vec![
            self.vector_reverse_qid(),
            self.vector_append_qid(),
            self.vector_is_empty_qid(),
            self.vector_contains_qid(),
            self.vector_index_of_qid(),
            self.vector_remove_qid(),
            self.vector_insert_qid(),
            self.vector_swap_remove_qid(),
            self.vector_take_qid(),
            self.vector_skip_qid(),
            self.vector_singleton_qid(),
            self.vec_set_get_idx_opt_qid(),
            self.vec_set_from_keys_qid(),
            self.vec_set_contains_qid(),
            self.vec_set_remove_qid(),
            self.vec_map_get_qid(),
            self.vec_map_get_idx_qid(),
            self.vec_map_get_idx_opt_qid(),
            self.vec_map_contains_qid(),
            self.vec_map_from_keys_values_qid(),
            self.vec_map_into_keys_values_qid(),
            self.vec_map_keys_qid(),
            self.vec_map_remove_qid(),
            self.table_new_qid(),
            self.table_add_qid(),
            self.table_borrow_qid(),
            self.table_borrow_mut_qid(),
            self.table_remove_qid(),
            self.table_contains_qid(),
            self.table_length_qid(),
            self.table_is_empty_qid(),
            self.table_destroy_empty_qid(),
            self.table_drop_qid(),
            self.object_table_new_qid(),
            self.object_table_add_qid(),
            self.object_table_borrow_qid(),
            self.object_table_borrow_mut_qid(),
            self.object_table_remove_qid(),
            self.object_table_contains_qid(),
            self.object_table_length_qid(),
            self.object_table_is_empty_qid(),
            self.object_table_destroy_empty_qid(),
            self.object_table_value_id_qid(),
            self.dynamic_field_add_qid(),
            self.dynamic_field_borrow_qid(),
            self.dynamic_field_borrow_mut_qid(),
            self.dynamic_field_remove_qid(),
            self.dynamic_field_exists_qid(),
            self.dynamic_field_remove_if_exists_qid(),
            self.dynamic_field_exists_with_type_qid(),
            self.dynamic_object_field_add_qid(),
            self.dynamic_object_field_borrow_qid(),
            self.dynamic_object_field_borrow_mut_qid(),
            self.dynamic_object_field_remove_qid(),
            self.dynamic_object_field_exists_qid(),
            self.dynamic_object_field_remove_if_exists_qid(),
            self.dynamic_object_field_exists_with_type_qid(),
        ]
        .into_iter()
        .filter_map(|x| x)
        .collect()
    }

    pub fn intrinsic_datatype_ids(&self) -> BTreeSet<QualifiedId<DatatypeId>> {
        vec![self.table_qid(), self.object_table_qid()]
            .into_iter()
            .filter_map(|x| x)
            .collect()
    }

    pub fn should_be_used_as_func(&self, qid: &QualifiedId<FunId>) -> bool {
        self.native_fn_ids().contains(qid)
    }

    pub fn native_fn_ids(&self) -> BTreeSet<QualifiedId<FunId>> {
        vec![
            // std::integer native functions
            self.std_integer_from_u8_qid(),
            self.std_integer_from_u16_qid(),
            self.std_integer_from_u32_qid(),
            self.std_integer_from_u64_qid(),
            self.std_integer_from_u128_qid(),
            self.std_integer_from_u256_qid(),
            self.std_integer_to_u8_qid(),
            self.std_integer_to_u16_qid(),
            self.std_integer_to_u32_qid(),
            self.std_integer_to_u64_qid(),
            self.std_integer_to_u128_qid(),
            self.std_integer_to_u256_qid(),
            self.std_integer_add_qid(),
            self.std_integer_sub_qid(),
            self.std_integer_neg_qid(),
            self.std_integer_mul_qid(),
            self.std_integer_div_qid(),
            self.std_integer_mod_qid(),
            self.std_integer_sqrt_qid(),
            self.std_integer_pow_qid(),
            self.std_integer_bit_or_qid(),
            self.std_integer_bit_and_qid(),
            self.std_integer_bit_xor_qid(),
            self.std_integer_bit_not_qid(),
            self.std_integer_lt_qid(),
            self.std_integer_gt_qid(),
            self.std_integer_lte_qid(),
            self.std_integer_gte_qid(),
            // std::real native functions
            self.std_real_from_integer_qid(),
            self.std_real_to_integer_qid(),
            self.std_real_add_qid(),
            self.std_real_sub_qid(),
            self.std_real_neg_qid(),
            self.std_real_mul_qid(),
            self.std_real_div_qid(),
            self.std_real_sqrt_qid(),
            self.std_real_exp_qid(),
            self.std_real_lt_qid(),
            self.std_real_gt_qid(),
            self.std_real_lte_qid(),
            self.std_real_gte_qid(),
            // std::bcs native functions
            self.std_bcs_to_bytes_qid(),
            // std::vector native functions
            self.std_vector_empty_qid(),
            self.vector_is_empty_qid(),
            self.std_vector_length_qid(),
            self.vector_contains_qid(),
            self.std_vector_push_back_qid(),
            self.vector_append_qid(),
            self.vector_reverse_qid(),
            self.vector_singleton_qid(),
            // vec_set and vec_map native functions
            self.vec_set_contains_qid(),
            self.vec_map_contains_qid(),
            self.vec_map_get_idx_opt_qid(),
            self.vec_map_keys_qid(),
            Some(self.prover_vec_slice_qid()),
            Some(self.prover_vec_sum_qid()),
            Some(self.prover_vec_sum_range_qid()),
            Some(self.prover_range_qid()),
            // table and object_table native functions
            self.table_is_empty_qid(),
            self.table_length_qid(),
            self.table_contains_qid(),
            self.object_table_is_empty_qid(),
            self.object_table_length_qid(),
            self.object_table_contains_qid(),
            // dynamic_field and dynamic_object_field existence-check functions
            self.dynamic_field_exists_qid(),
            self.dynamic_field_exists_with_type_qid(),
            self.dynamic_object_field_exists_qid(),
            self.dynamic_object_field_exists_with_type_qid(),
            self.object_borrow_uid_qid(),
            // sui::tx_context native functions
            self.sui_tx_context_sender_qid(),
            self.sui_tx_context_epoch_qid(),
            self.sui_tx_context_epoch_timestamp_ms_qid(),
            self.sui_tx_context_reference_gas_price_qid(),
            self.sui_tx_context_gas_price_qid(),
        ]
        .into_iter()
        .filter_map(|x| x)
        .collect()
    }

    fn add_stub_module(&mut self, module_symbol: Symbol) {
        if self.find_module_by_name(module_symbol).is_none() {
            let mut compiled_module: CompiledModule = CompiledModule::default();
            compiled_module.module_handles.push(ModuleHandle {
                address: AddressIdentifierIndex::default(),
                name: IdentifierIndex::default(),
            });
            compiled_module
                .address_identifiers
                .push(AccountAddress::ZERO);
            // Use a valid identifier for stub module handle name; "<SELF>" is disallowed.
            compiled_module
                .identifiers
                .push(Identifier::new("SELF").unwrap());
            self.module_data.push(ModuleData {
                name: ModuleName::new(Default::default(), module_symbol),
                id: ModuleId::new(self.get_module_count()),
                module: compiled_module,
                named_constants: BTreeMap::new(),
                struct_data: BTreeMap::new(),
                struct_idx_to_id: BTreeMap::new(),
                function_data: BTreeMap::new(),
                function_idx_to_id: BTreeMap::new(),
                // below this line is source/prover specific
                source_map: SourceMap::new(
                    MoveIrLoc::new(FileHash::empty(), 0, 0),
                    IR::ModuleIdent::new(
                        IR::ModuleName(move_symbol_pool::Symbol::from(
                            self.symbol_pool.string(module_symbol).as_str(),
                        )),
                        AccountAddress::ZERO,
                    ),
                ),
                loc: Loc::default(),
                attributes: Default::default(),
                toplevel_attributes: Default::default(),
                used_modules: Default::default(),
                friend_modules: Default::default(),
                enum_data: BTreeMap::new(),
                enum_idx_to_id: BTreeMap::new(),
            })
        }
    }

    pub fn add_stub_prover_module(&mut self) {
        self.add_stub_module(self.symbol_pool().make(Self::PROVER_MODULE_NAME))
    }

    pub fn add_stub_spec_module(&mut self) {
        self.add_stub_module(self.symbol_pool().make(Self::SPEC_MODULE_NAME))
    }

    pub fn add_stub_log_module(&mut self) {
        self.add_stub_module(self.symbol_pool().make(Self::LOG_MODULE_NAME))
    }
}

impl Default for GlobalEnv {
    fn default() -> Self {
        Self::new()
    }
}

// =================================================================================================
// # Module Environment

/// Represents data for a module.
#[derive(Debug)]
pub struct ModuleData {
    /// Module name.
    pub name: ModuleName,

    /// Id of this module in the global env.
    pub id: ModuleId,

    /// Attributes attached to this module.
    attributes: Vec<Attribute>,

    toplevel_attributes: expansion::ast::Attributes,

    /// Module byte code.
    pub module: CompiledModule,

    /// Named constant data
    pub named_constants: BTreeMap<NamedConstantId, NamedConstantData>,

    /// Struct data.
    pub struct_data: BTreeMap<DatatypeId, StructData>,

    /// Enum data.
    pub enum_data: BTreeMap<DatatypeId, EnumData>,

    /// Mapping from struct definition index to id in struct map.
    pub struct_idx_to_id: BTreeMap<StructDefinitionIndex, DatatypeId>,

    /// Mapping from enum definition index to id in the enum_data map
    pub enum_idx_to_id: BTreeMap<EnumDefinitionIndex, DatatypeId>,

    /// Function data.
    pub function_data: BTreeMap<FunId, FunctionData>,

    /// Mapping from function definition index to id in above map.
    pub function_idx_to_id: BTreeMap<FunctionDefinitionIndex, FunId>,

    /// Module source location information.
    pub source_map: SourceMap,

    /// The location of this module.
    pub loc: Loc,

    /// A cache for the modules used by this one.
    used_modules: RefCell<BTreeMap<bool, BTreeSet<ModuleId>>>,

    /// A cache for the modules declared as friends by this one.
    friend_modules: RefCell<Option<BTreeSet<ModuleId>>>,
}

impl ModuleData {
    pub fn stub(name: ModuleName, id: ModuleId, module: CompiledModule) -> Self {
        let ident = IR::ModuleIdent::new(
            IR::ModuleName(module.name().as_str().into()),
            *module.address(),
        );
        ModuleData {
            name,
            id,
            module,
            named_constants: BTreeMap::new(),
            struct_data: BTreeMap::new(),
            struct_idx_to_id: BTreeMap::new(),
            function_data: BTreeMap::new(),
            function_idx_to_id: BTreeMap::new(),
            source_map: SourceMap::new(MoveIrLoc::new(FileHash::empty(), 0, 0), ident),
            loc: Loc::default(),
            attributes: Default::default(),
            toplevel_attributes: Default::default(),
            used_modules: Default::default(),
            friend_modules: Default::default(),
            enum_data: BTreeMap::new(),
            enum_idx_to_id: BTreeMap::new(),
        }
    }
}

/// Represents a module environment.
#[derive(Debug, Clone)]
pub struct ModuleEnv<'env> {
    /// Reference to the outer env.
    pub env: &'env GlobalEnv,

    /// Reference to the data of the module.
    pub data: &'env ModuleData,
}

impl<'env> ModuleEnv<'env> {
    /// Returns the id of this module in the global env.
    pub fn get_id(&self) -> ModuleId {
        self.data.id
    }

    /// Returns the name of this module.
    pub fn get_name(&'env self) -> &'env ModuleName {
        &self.data.name
    }

    /// Returns true if either the full name or simple name of this module matches the given string
    pub fn matches_name(&self, name: &str) -> bool {
        self.get_full_name_str() == name
            || self.get_name().display(self.symbol_pool()).to_string() == name
    }

    /// Returns the location of this module.
    pub fn get_loc(&'env self) -> Loc {
        self.data.loc.clone()
    }

    /// Returns the attributes of this module.
    pub fn get_attributes(&self) -> &[Attribute] {
        &self.data.attributes
    }

    pub fn get_toplevel_attributes(&self) -> &expansion::ast::Attributes {
        &self.data.toplevel_attributes
    }

    /// Returns full name as a string.
    pub fn get_full_name_str(&self) -> String {
        self.get_name().display_full(self.symbol_pool()).to_string()
    }

    /// Returns the VM identifier for this module
    pub fn get_identifier(&'env self) -> Identifier {
        self.data.module.name().to_owned()
    }

    /// Returns true if this is a module representing a script.
    pub fn is_script_module(&self) -> bool {
        self.data.name.is_script()
    }

    /// Returns true of this module is target of compilation. A non-target module is
    /// a dependency only but not explicitly requested to process.
    pub fn is_target(&self) -> bool {
        let file_id = self.data.loc.file_id;
        !self.env.file_id_is_dep.contains(&file_id)
    }

    /// Returns the path to source file of this module.
    pub fn get_source_path(&self) -> &OsStr {
        let file_id = self.data.loc.file_id;
        self.env.source_files.name(file_id)
    }

    /// Return the set of language storage ModuleId's that this module's bytecode depends on
    /// (including itself), friend modules are excluded from the return result.
    pub fn get_dependencies(&self) -> Vec<language_storage::ModuleId> {
        let compiled_module = &self.data.module;
        let mut deps = compiled_module.immediate_dependencies();
        deps.push(compiled_module.self_id());
        deps
    }

    /// Return the set of language storage ModuleId's that this module declares as friends
    pub fn get_friends(&self) -> Vec<language_storage::ModuleId> {
        self.data.module.immediate_friends()
    }

    /// Returns the set of modules that use this one.
    pub fn get_using_modules(&self) -> BTreeSet<ModuleId> {
        self.env
            .get_modules()
            .filter_map(|module_env| {
                if module_env.get_used_modules().contains(&self.data.id) {
                    Some(module_env.data.id)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Returns the set of modules this one uses.
    pub fn get_used_modules(&self) -> BTreeSet<ModuleId> {
        if let Some(usage) = self.data.used_modules.borrow().get(&false) {
            return usage.clone();
        }
        // Determine modules used in bytecode from the compiled module.
        let usage: BTreeSet<ModuleId> = self
            .get_dependencies()
            .into_iter()
            .map(|storage_id| self.env.to_module_name(&storage_id))
            .filter_map(|name| self.env.find_module(&name))
            .map(|env| env.get_id())
            .filter(|id| *id != self.get_id())
            .collect();
        self.data
            .used_modules
            .borrow_mut()
            .insert(false, usage.clone());
        usage
    }

    /// Returns the set of modules this one declares as friends.
    pub fn get_friend_modules(&self) -> BTreeSet<ModuleId> {
        self.data
            .friend_modules
            .borrow_mut()
            .get_or_insert_with(|| {
                // Determine modules used in bytecode from the compiled module.
                self.get_friends()
                    .into_iter()
                    .map(|storage_id| self.env.to_module_name(&storage_id))
                    .filter_map(|name| self.env.find_module(&name))
                    .map(|env| env.get_id())
                    .collect()
            })
            .clone()
    }

    /// Returns true if the given module is a transitive dependency of this one. The
    /// transitive dependency set contains this module and all directly or indirectly used
    /// modules (without spec usage).
    pub fn is_transitive_dependency(&self, module_id: ModuleId) -> bool {
        if self.get_id() == module_id {
            true
        } else {
            for dep in self.get_used_modules() {
                if self.env.get_module(dep).is_transitive_dependency(module_id) {
                    return true;
                }
            }
            false
        }
    }

    /// Shortcut for accessing the symbol pool.
    pub fn symbol_pool(&self) -> &SymbolPool {
        &self.env.symbol_pool
    }

    /// Gets the underlying bytecode module.
    pub fn get_verified_module(&'env self) -> &'env CompiledModule {
        &self.data.module
    }

    /// Gets a `NamedConstantEnv` in this module by name
    pub fn find_named_constant(&'env self, name: Symbol) -> Option<NamedConstantEnv<'env>> {
        let id = NamedConstantId(name);
        self.data
            .named_constants
            .get(&id)
            .map(|data| NamedConstantEnv {
                module_env: self.clone(),
                data,
            })
    }

    /// Gets a `NamedConstantEnv` in this module by the constant's id
    pub fn get_named_constant(&'env self, id: NamedConstantId) -> NamedConstantEnv<'env> {
        self.clone().into_named_constant(id)
    }

    /// Gets a `NamedConstantEnv` by id
    pub fn into_named_constant(self, id: NamedConstantId) -> NamedConstantEnv<'env> {
        let data = self
            .data
            .named_constants
            .get(&id)
            .expect("NamedConstantId undefined");
        NamedConstantEnv {
            module_env: self,
            data,
        }
    }

    /// Gets the number of named constants in this module.
    pub fn get_named_constant_count(&self) -> usize {
        self.data.named_constants.len()
    }

    /// Returns iterator over `NamedConstantEnv`s in this module.
    pub fn get_named_constants(&'env self) -> impl Iterator<Item = NamedConstantEnv<'env>> {
        self.clone().into_named_constants()
    }

    /// Returns an iterator over `NamedConstantEnv`s in this module.
    pub fn into_named_constants(self) -> impl Iterator<Item = NamedConstantEnv<'env>> {
        self.data
            .named_constants
            .values()
            .map(move |data| NamedConstantEnv {
                module_env: self.clone(),
                data,
            })
    }

    /// Gets a FunctionEnv in this module by name.
    pub fn find_function(&self, name: Symbol) -> Option<FunctionEnv<'env>> {
        let id = FunId(name);
        self.data
            .function_data
            .get(&id)
            .map(move |data| FunctionEnv {
                module_env: self.clone(),
                data,
            })
    }

    /// Gets a FunctionEnv by id.
    pub fn get_function(&'env self, id: FunId) -> FunctionEnv<'env> {
        self.clone().into_function(id)
    }

    /// Gets a FunctionEnv by id.
    pub fn into_function(self, id: FunId) -> FunctionEnv<'env> {
        let data = self.data.function_data.get(&id).expect(&format!(
            "FunId undefined: {}",
            QualifiedSymbol {
                module_name: self.get_name().clone(),
                symbol: id.symbol(),
            }
            .display_full(self.symbol_pool())
        ));
        FunctionEnv {
            module_env: self,
            data,
        }
    }

    /// Gets the number of functions in this module.
    pub fn get_function_count(&self) -> usize {
        self.data.function_data.len()
    }

    /// Returns iterator over FunctionEnvs in this module.
    pub fn get_functions(&'env self) -> impl Iterator<Item = FunctionEnv<'env>> {
        self.clone().into_functions()
    }

    /// Returns iterator over FunctionEnvs in this module.
    pub fn into_functions(self) -> impl Iterator<Item = FunctionEnv<'env>> {
        self.data
            .function_data
            .values()
            .map(move |data| FunctionEnv {
                module_env: self.clone(),
                data,
            })
    }

    /// Gets FunctionEnv for a function used in this module, via the FunctionHandleIndex. The
    /// returned function might be from this or another module.
    pub fn get_used_function(&self, idx: FunctionHandleIndex) -> FunctionEnv<'_> {
        let module = &self.data.module;
        let fhandle = module.function_handle_at(idx);
        let fname = module.identifier_at(fhandle.name).as_str();
        let declaring_module_handle = module.module_handle_at(fhandle.module);
        let declaring_module = module.module_id_for_handle(declaring_module_handle);
        let module_env = self
            .env
            .find_module(&self.env.to_module_name(&declaring_module))
            .expect("unexpected reference to module not found in global env");
        module_env.into_function(FunId::new(self.env.symbol_pool.make(fname)))
    }

    /// Gets the function id from a definition index.
    pub fn try_get_function_id(&self, idx: FunctionDefinitionIndex) -> Option<FunId> {
        self.data.function_idx_to_id.get(&idx).cloned()
    }

    /// Gets the function definition index for the given function id. This is always defined.
    pub fn get_function_def_idx(&self, fun_id: FunId) -> FunctionDefinitionIndex {
        self.data
            .function_data
            .get(&fun_id)
            .expect("function id defined")
            .def_idx
    }

    /// Gets a StructEnv in this module by name.
    pub fn find_struct(&self, name: Symbol) -> Option<StructEnv<'_>> {
        let id = DatatypeId(name);
        self.data.struct_data.get(&id).map(|data| StructEnv {
            module_env: self.clone(),
            data,
        })
    }

    /// Gets a StructEnv in this module by identifier
    pub fn find_struct_by_identifier(&self, identifier: Identifier) -> Option<DatatypeId> {
        let some_id = Some(identifier);
        for data in self.data.struct_data.values() {
            let senv = StructEnv {
                module_env: self.clone(),
                data,
            };
            if senv.get_identifier() == some_id {
                return Some(senv.get_id());
            }
        }
        None
    }

    /// Gets the struct id from a definition index which must be valid for this environment.
    pub fn get_struct_id(&self, idx: StructDefinitionIndex) -> DatatypeId {
        *self
            .data
            .struct_idx_to_id
            .get(&idx)
            .unwrap_or_else(|| panic!("undefined struct definition index {:?}", idx))
    }

    /// Gets a StructEnv by id.
    pub fn get_struct(&self, id: DatatypeId) -> StructEnv<'_> {
        let data = self
            .data
            .struct_data
            .get(&id)
            .expect("DatatypeId undefined");
        StructEnv {
            module_env: self.clone(),
            data,
        }
    }

    pub fn get_struct_by_def_idx(&self, idx: StructDefinitionIndex) -> StructEnv<'_> {
        self.get_struct(self.get_struct_id(idx))
    }

    /// Gets a StructEnv by id, consuming this module env.
    pub fn into_struct(self, id: DatatypeId) -> StructEnv<'env> {
        let data = self
            .data
            .struct_data
            .get(&id)
            .expect("DatatypeId undefined");
        StructEnv {
            module_env: self,
            data,
        }
    }

    /// Gets the number of structs in this module.
    pub fn get_struct_count(&self) -> usize {
        self.data.struct_data.len()
    }

    /// Returns an iterator over structs in this module.
    pub fn get_structs(&'env self) -> impl Iterator<Item = StructEnv<'env>> {
        self.clone().into_structs()
    }

    /// Gets an EnumEnv in this module by name.
    pub fn find_enum(&self, name: Symbol) -> Option<EnumEnv<'_>> {
        let id = DatatypeId(name);
        self.data.enum_data.get(&id).map(|data| EnumEnv {
            module_env: self.clone(),
            data,
        })
    }

    /// Gets an EnumEnv in this module by identifier
    pub fn find_enum_by_identifier(&self, identifier: Identifier) -> Option<DatatypeId> {
        let some_id = Some(identifier);
        for data in self.data.enum_data.values() {
            let eenv = EnumEnv {
                module_env: self.clone(),
                data,
            };
            if eenv.get_identifier() == some_id {
                return Some(eenv.get_id());
            }
        }
        None
    }

    /// Gets the enum id from a definition index which must be valid for this environment.
    pub fn get_enum_id(&self, idx: EnumDefinitionIndex) -> DatatypeId {
        *self
            .data
            .enum_idx_to_id
            .get(&idx)
            .unwrap_or_else(|| panic!("undefined enum definition index {:?}", idx))
    }

    /// Gets an EnumEnv by id.
    pub fn get_enum(&self, id: DatatypeId) -> EnumEnv<'_> {
        let data = self.data.enum_data.get(&id).expect("EnumId undefined");
        EnumEnv {
            module_env: self.clone(),
            data,
        }
    }

    pub fn get_enum_by_def_idx(&self, idx: EnumDefinitionIndex) -> EnumEnv<'_> {
        self.get_enum(self.get_enum_id(idx))
    }

    /// Gets an EnumEnv by id, consuming this module env.
    pub fn into_enum(self, id: DatatypeId) -> EnumEnv<'env> {
        let data = self.data.enum_data.get(&id).expect("EnumId undefined");
        EnumEnv {
            module_env: self,
            data,
        }
    }

    /// Gets the number of enums in this module.
    pub fn get_enum_count(&self) -> usize {
        self.data.enum_data.len()
    }

    /// Returns an iterator over structs in this module.
    pub fn get_enums(&'env self) -> impl Iterator<Item = EnumEnv<'env>> {
        self.clone().into_enums()
    }

    /// Gets a StructEnv or an EnumEnv by id.
    pub fn get_struct_or_enum(&self, id: DatatypeId) -> StructOrEnumEnv<'_> {
        self.find_struct(id.symbol())
            .map(|struct_env| StructOrEnumEnv::Struct(struct_env))
            .or_else(|| {
                self.find_enum(id.symbol())
                    .map(|enum_env| StructOrEnumEnv::Enum(enum_env))
            })
            .expect(&format!(
                "DatatypeId undefined: {}",
                QualifiedSymbol {
                    module_name: self.get_name().clone(),
                    symbol: id.symbol(),
                }
                .display_full(self.symbol_pool())
            ))
    }

    /// Gets a StructEnv or an EnumEnv by id, consuming this module env.
    pub fn into_struct_or_enum(self, id: DatatypeId) -> StructOrEnumEnv<'env> {
        match self.get_struct_or_enum(id) {
            StructOrEnumEnv::Struct { .. } => StructOrEnumEnv::Struct(self.into_struct(id)),
            StructOrEnumEnv::Enum { .. } => StructOrEnumEnv::Enum(self.into_enum(id)),
        }
    }

    /// Returns an iterator over all object types declared by this module
    pub fn get_objects(&'env self) -> impl Iterator<Item = StructEnv<'env>> {
        self.clone()
            .into_structs()
            .filter(|s| s.get_abilities().has_key())
    }

    /// Returns iterator over structs in this module.
    pub fn into_structs(self) -> impl Iterator<Item = StructEnv<'env>> {
        self.data.struct_data.values().map(move |data| StructEnv {
            module_env: self.clone(),
            data,
        })
    }

    /// Returns iterator over enums in this module.
    pub fn into_enums(self) -> impl Iterator<Item = EnumEnv<'env>> {
        self.data.enum_data.values().map(move |data| EnumEnv {
            module_env: self.clone(),
            data,
        })
    }

    /// Globalizes a signature local to this module.
    pub fn globalize_signature(&self, sig: &SignatureToken) -> Type {
        match sig {
            SignatureToken::Bool => Type::Primitive(PrimitiveType::Bool),
            SignatureToken::U8 => Type::Primitive(PrimitiveType::U8),
            SignatureToken::U16 => Type::Primitive(PrimitiveType::U16),
            SignatureToken::U32 => Type::Primitive(PrimitiveType::U32),
            SignatureToken::U64 => Type::Primitive(PrimitiveType::U64),
            SignatureToken::U128 => Type::Primitive(PrimitiveType::U128),
            SignatureToken::U256 => Type::Primitive(PrimitiveType::U256),
            SignatureToken::Address => Type::Primitive(PrimitiveType::Address),
            SignatureToken::Signer => Type::Primitive(PrimitiveType::Signer),
            SignatureToken::Reference(t) => {
                Type::Reference(false, Box::new(self.globalize_signature(t)))
            }
            SignatureToken::MutableReference(t) => {
                Type::Reference(true, Box::new(self.globalize_signature(t)))
            }
            SignatureToken::TypeParameter(index) => Type::TypeParameter(*index),
            SignatureToken::Vector(bt) => Type::Vector(Box::new(self.globalize_signature(bt))),
            SignatureToken::Datatype(handle_idx) => {
                let module = &self.data.module;
                let shandle = module.datatype_handle_at(*handle_idx);
                let sname = module.identifier_at(shandle.name).as_str();
                let declaring_module_handle = module.module_handle_at(shandle.module);
                let declaring_module = module.module_id_for_handle(declaring_module_handle);
                let declaring_module_env = self
                    .env
                    .find_module(&self.env.to_module_name(&declaring_module))
                    .expect("undefined module");
                let name = self.env.symbol_pool.make(sname);
                let datatype_id = declaring_module_env
                    .find_struct(name)
                    .map(|env| env.get_id())
                    .or_else(|| declaring_module_env.find_enum(name).map(|env| env.get_id()))
                    .expect("undefined datatype");
                Type::Datatype(declaring_module_env.data.id, datatype_id, vec![])
            }
            SignatureToken::DatatypeInstantiation(inst) => {
                let (handle_idx, args) = &**inst;
                let module = &self.data.module;
                let shandle = module.datatype_handle_at(*handle_idx);
                let sname = module.identifier_at(shandle.name).as_str();
                let declaring_module_handle = module.module_handle_at(shandle.module);
                let declaring_module = module.module_id_for_handle(declaring_module_handle);
                let declaring_module_env = self
                    .env
                    .find_module(&self.env.to_module_name(&declaring_module))
                    .expect("undefined module");
                let name = self.env.symbol_pool.make(sname);
                let datatype_id = declaring_module_env
                    .find_struct(name)
                    .map(|env| env.get_id())
                    .or_else(|| declaring_module_env.find_enum(name).map(|env| env.get_id()))
                    .expect("undefined datatype");
                Type::Datatype(
                    declaring_module_env.data.id,
                    datatype_id,
                    self.globalize_signatures(args),
                )
            }
        }
    }

    /// Globalizes a list of signatures.
    pub fn globalize_signatures(&self, sigs: &[SignatureToken]) -> Vec<Type> {
        sigs.iter()
            .map(|s| self.globalize_signature(s))
            .collect_vec()
    }

    /// Gets a list of type actuals associated with the index in the bytecode.
    pub fn get_type_actuals(&self, idx: Option<SignatureIndex>) -> Vec<Type> {
        match idx {
            Some(idx) => {
                let actuals = &self.data.module.signature_at(idx).0;
                self.globalize_signatures(actuals)
            }
            None => vec![],
        }
    }

    /// Retrieve a constant from the pool
    pub fn get_constant(&self, idx: ConstantPoolIndex) -> &VMConstant {
        &self.data.module.constant_pool()[idx.0 as usize]
    }

    /// Converts a constant to the specified type. The type must correspond to the expected
    /// cannonical representation as defined in `move_core_types::values`
    pub fn get_constant_value(&self, constant: &VMConstant) -> MoveValue {
        VMConstant::deserialize_constant(constant).unwrap()
    }

    /// Return the `AccountAdress` of this module
    pub fn self_address(&self) -> &AccountAddress {
        self.data.module.address()
    }

    /// Retrieve an address identifier from the pool
    pub fn get_address_identifier(&self, idx: AddressIdentifierIndex) -> BigUint {
        let addr = &self.data.module.address_identifiers()[idx.0 as usize];
        crate::addr_to_big_uint(addr)
    }

    /// Disassemble the module bytecode
    pub fn disassemble(&self) -> String {
        let disas = Disassembler::new(
            SourceMapping::new(self.data.source_map.clone(), self.get_verified_module()),
            DisassemblerOptions {
                only_externally_visible: false,
                print_code: true,
                print_basic_blocks: true,
                print_locals: true,
                max_output_size: None,
            },
        );
        disas
            .disassemble()
            .expect("Failed to disassemble a verified module")
    }

    fn match_module_name(&self, module_name: &str) -> bool {
        self.get_name()
            .name()
            .display(self.env.symbol_pool())
            .to_string()
            == module_name
    }

    fn is_module_in_std(&self, module_name: &str) -> bool {
        let addr = self.get_name().addr();
        *addr == self.env.get_stdlib_address() && self.match_module_name(module_name)
    }

    fn is_module_in_ext(&self, module_name: &str) -> bool {
        let addr = self.get_name().addr();
        *addr == self.env.get_extlib_address() && self.match_module_name(module_name)
    }

    pub fn is_std_vector(&self) -> bool {
        self.is_module_in_std("vector")
    }

    pub fn is_table(&self) -> bool {
        self.is_module_in_std("table")
            || self.is_module_in_std("table_with_length")
            || self.is_module_in_ext("table")
            || self.is_module_in_ext("table_with_length")
    }
}

pub enum StructOrEnumEnv<'env> {
    Struct(StructEnv<'env>),
    Enum(EnumEnv<'env>),
}

// =================================================================================================
/// # Enum Environment

#[derive(Debug)]
pub struct EnumData {
    /// The name of this enum.
    name: Symbol,

    /// The location of this enum.
    loc: Loc,

    /// Attributes attached to this enum.
    attributes: Vec<Attribute>,

    /// The definition index of this enum in its module.
    def_idx: EnumDefinitionIndex,

    /// The handle index of this enum in its module.
    handle_idx: DatatypeHandleIndex,

    /// Variant definitions
    variant_data: BTreeMap<VariantId, VariantData>,
}

#[derive(Debug, Clone)]
pub struct EnumEnv<'env> {
    /// Reference to enclosing module.
    pub module_env: ModuleEnv<'env>,

    /// Reference to the enum data.
    data: &'env EnumData,
}

impl<'env> EnumEnv<'env> {
    /// Returns the name of this enum.
    pub fn get_name(&self) -> Symbol {
        self.data.name
    }

    /// Gets full name as string.
    pub fn get_full_name_str(&self) -> String {
        format!(
            "{}::{}",
            self.module_env.get_name().display(self.symbol_pool()),
            self.get_name().display(self.symbol_pool())
        )
    }

    /// Gets full name with module address as string.
    pub fn get_full_name_with_address(&self) -> String {
        format!(
            "{}::{}",
            self.module_env.get_full_name_str(),
            self.get_name().display(self.symbol_pool())
        )
    }

    /// Returns the VM identifier for thisenum
    pub fn get_identifier(&self) -> Option<Identifier> {
        let handle_idx = self.data.handle_idx;
        let handle = self.module_env.data.module.datatype_handle_at(handle_idx);
        Some(
            self.module_env
                .data
                .module
                .identifier_at(handle.name)
                .to_owned(),
        )
    }

    /// Shortcut for accessing the symbol pool.
    pub fn symbol_pool(&self) -> &SymbolPool {
        self.module_env.symbol_pool()
    }

    /// Returns the location of this enum.
    pub fn get_loc(&self) -> Loc {
        self.data.loc.clone()
    }

    /// Returns the attributes of this enum.
    pub fn get_attributes(&self) -> &[Attribute] {
        &self.data.attributes
    }

    /// Gets the id associated with this enum.
    pub fn get_id(&self) -> DatatypeId {
        DatatypeId(self.data.name)
    }

    /// Gets the qualified id of this enum.
    pub fn get_qualified_id(&self) -> QualifiedId<DatatypeId> {
        self.module_env.get_id().qualified(self.get_id())
    }

    /// Get the abilities of this enum.
    pub fn get_abilities(&self) -> AbilitySet {
        let def = self.module_env.data.module.enum_def_at(self.data.def_idx);
        let handle = self
            .module_env
            .data
            .module
            .datatype_handle_at(def.enum_handle);
        handle.abilities
    }

    /// Determines whether memory-related operations needs to be declared for this enum.
    pub fn has_memory(&self) -> bool {
        self.get_abilities().has_key()
    }

    /// Get an iterator for the variants, ordered by tag.
    pub fn get_variants(&'env self) -> impl Iterator<Item = VariantEnv<'env>> {
        self.data
            .variant_data
            .values()
            .sorted_by_key(|data| data.tag)
            .map(move |data| VariantEnv {
                enum_env: self.clone(),
                data,
            })
    }

    pub fn get_all_fields(&'env self) -> impl Iterator<Item = FieldEnv<'env>> {
        self.data
            .variant_data
            .values()
            .sorted_by_key(|data| data.tag)
            .flat_map(move |data| {
                data.field_data
                    .values()
                    .sorted_by_key(|data| data.offset)
                    .map(move |fdata| FieldEnv {
                        parent_env: EnclosingEnv::Variant(VariantEnv {
                            enum_env: self.clone(),
                            data,
                        }),
                        data: fdata,
                    })
            })
    }

    /// Return the number of variants in the enum.
    pub fn get_variant_count(&self) -> usize {
        self.data.variant_data.len()
    }

    /// Gets a variant by its id.
    pub fn get_variant(&'env self, id: VariantId) -> VariantEnv<'env> {
        let data = self
            .data
            .variant_data
            .get(&id)
            .expect("VariantId undefined");
        VariantEnv {
            enum_env: self.clone(),
            data,
        }
    }

    /// Find a variann by its name.
    pub fn find_variant(&'env self, name: Symbol) -> Option<VariantEnv<'env>> {
        let id = VariantId(name);
        self.data.variant_data.get(&id).map(|data| VariantEnv {
            enum_env: self.clone(),
            data,
        })
    }

    /// Gets a variant by its tag.
    pub fn get_variant_by_tag(&'env self, tag: usize) -> VariantEnv<'env> {
        for data in self.data.variant_data.values() {
            if data.tag == tag {
                return VariantEnv {
                    enum_env: self.clone(),
                    data,
                };
            }
        }
        unreachable!("invalid variant lookup")
    }

    /// Whether the type parameter at position `idx` is declared as phantom.
    pub fn is_phantom_parameter(&self, idx: usize) -> bool {
        let def_idx = self.data.def_idx;

        let def = self.module_env.data.module.enum_def_at(def_idx);
        self.module_env
            .data
            .module
            .datatype_handle_at(def.enum_handle)
            .type_parameters[idx]
            .is_phantom
    }

    /// Returns the type parameters associated with this enum.
    pub fn get_type_parameters(&self) -> Vec<TypeParameter> {
        // TODO: we currently do not know the original names of those formals, so we generate them.
        let pool = &self.module_env.env.symbol_pool;
        let def_idx = self.data.def_idx;
        let module = &self.module_env.data.module;
        let edef = module.enum_def_at(def_idx);
        let ehandle = module.datatype_handle_at(edef.enum_handle);
        ehandle
            .type_parameters
            .iter()
            .enumerate()
            .map(|(i, k)| {
                TypeParameter(
                    pool.make(&format!("$tv{}", i)),
                    AbilityConstraint(k.constraints),
                )
            })
            .collect_vec()
    }

    /// Returns the type parameters associated with this enum, with actual names.
    pub fn get_named_type_parameters(&self) -> Vec<TypeParameter> {
        let def_idx = self.data.def_idx;
        let module = &self.module_env.data.module;
        let edef = module.enum_def_at(def_idx);
        let ehandle = module.datatype_handle_at(edef.enum_handle);
        ehandle
            .type_parameters
            .iter()
            .enumerate()
            .map(|(i, k)| {
                let name = self
                    .module_env
                    .data
                    .source_map
                    .get_enum_source_map(def_idx)
                    .ok()
                    .and_then(|smap| smap.type_parameters.get(i))
                    .map(|(s, _)| s.clone())
                    .unwrap_or_else(|| format!("unknown#{}", i));
                TypeParameter(
                    self.module_env.env.symbol_pool.make(&name),
                    AbilityConstraint(k.constraints),
                )
            })
            .collect_vec()
    }
}

// =================================================================================================
/// # Variant Environment

#[derive(Debug)]
pub struct VariantData {
    /// The name of this variant.
    name: Symbol,

    /// The location of this variant.
    loc: Loc,

    tag: usize,

    /// Field definitions.
    field_data: BTreeMap<FieldId, FieldData>,
}

#[derive(Debug, Clone)]
pub struct VariantEnv<'env> {
    /// Reference to enclosing module.
    pub enum_env: EnumEnv<'env>,

    /// Reference to the variant data.
    data: &'env VariantData,
}

impl<'env> VariantEnv<'env> {
    /// Returns the name of this variant.
    pub fn get_name(&self) -> Symbol {
        self.data.name
    }

    /// Gets full name as string.
    pub fn get_full_name_str(&self) -> String {
        format!(
            "{}::{}::{}",
            self.enum_env
                .module_env
                .get_name()
                .display(self.symbol_pool()),
            self.enum_env.get_name().display(self.symbol_pool()),
            self.get_name().display(self.symbol_pool())
        )
    }

    /// Gets full name with module address as string.
    pub fn get_full_name_with_address(&self) -> String {
        format!(
            "{}::{}",
            self.enum_env.get_full_name_str(),
            self.get_name().display(self.symbol_pool())
        )
    }

    /// Gets the tag associated with this variant.
    pub fn get_tag(&self) -> usize {
        self.data.tag
    }

    /// Returns the VM identifier for this variant
    pub fn get_identifier(&self) -> Option<Identifier> {
        let enum_def = self
            .enum_env
            .module_env
            .data
            .module
            .enum_def_at(self.enum_env.data.def_idx);
        let variant_def = &enum_def.variants[self.data.tag];
        Some(
            self.enum_env
                .module_env
                .data
                .module
                .identifier_at(variant_def.variant_name)
                .to_owned(),
        )
    }

    /// Shortcut for accessing the symbol pool.
    pub fn symbol_pool(&self) -> &SymbolPool {
        self.enum_env.symbol_pool()
    }

    /// Returns the location of this variant.
    pub fn get_loc(&self) -> Loc {
        self.data.loc.clone()
    }

    /// Gets the id associated with this variant.
    pub fn get_id(&self) -> VariantId {
        VariantId(self.data.name)
    }

    /// Get an iterator for the fields, ordered by offset.
    pub fn get_fields(&'env self) -> impl Iterator<Item = FieldEnv<'env>> {
        self.data
            .field_data
            .values()
            .sorted_by_key(|data| data.offset)
            .map(move |data| FieldEnv {
                parent_env: EnclosingEnv::Variant(self.clone()),
                data,
            })
    }

    /// Return the number of fields in the struct.
    pub fn get_field_count(&self) -> usize {
        self.data.field_data.len()
    }

    /// Gets a field by its id.
    pub fn get_field(&'env self, id: FieldId) -> FieldEnv<'env> {
        let data = self.data.field_data.get(&id).expect("FieldId undefined");
        FieldEnv {
            parent_env: EnclosingEnv::Variant(self.clone()),
            data,
        }
    }

    /// Find a field by its name.
    pub fn find_field(&'env self, name: Symbol) -> Option<FieldEnv<'env>> {
        let id = FieldId(name);
        self.data.field_data.get(&id).map(|data| FieldEnv {
            parent_env: EnclosingEnv::Variant(self.clone()),
            data,
        })
    }

    /// Gets a field by its offset.
    pub fn get_field_by_offset(&'env self, offset: usize) -> FieldEnv<'env> {
        for data in self.data.field_data.values() {
            if data.offset == offset {
                return FieldEnv {
                    parent_env: EnclosingEnv::Variant(self.clone()),
                    data,
                };
            }
        }
        unreachable!("invalid field lookup")
    }
}

// =================================================================================================
/// # Struct Environment

#[derive(Debug)]
pub struct StructData {
    /// The name of this struct.
    name: Symbol,

    /// The location of this struct.
    loc: Loc,

    /// Attributes attached to this structure.
    attributes: Vec<Attribute>,

    /// List of function argument names. Not in bytecode but obtained from AST.
    /// Information about this struct.
    info: StructInfo,

    /// Field definitions.
    field_data: BTreeMap<FieldId, FieldData>,
}

#[derive(Debug)]
enum StructInfo {
    /// Struct is declared in Move and info found in VM format.
    Declared {
        /// The definition index of this struct in its module.
        def_idx: StructDefinitionIndex,

        /// The handle index of this struct in its module.
        handle_idx: DatatypeHandleIndex,
    },
}

#[derive(Debug, Clone)]
pub struct StructEnv<'env> {
    /// Reference to enclosing module.
    pub module_env: ModuleEnv<'env>,

    /// Reference to the struct data.
    data: &'env StructData,
}

impl<'env> StructEnv<'env> {
    /// Returns the name of this struct.
    pub fn get_name(&self) -> Symbol {
        self.data.name
    }

    /// Gets full name as string.
    pub fn get_full_name_str(&self) -> String {
        format!(
            "{}::{}",
            self.module_env.get_name().display(self.symbol_pool()),
            self.get_name().display(self.symbol_pool())
        )
    }

    /// Gets full name with module address as string.
    pub fn get_full_name_with_address(&self) -> String {
        format!(
            "{}::{}",
            self.module_env.get_full_name_str(),
            self.get_name().display(self.symbol_pool())
        )
    }

    /// Returns the VM identifier for this struct
    pub fn get_identifier(&self) -> Option<Identifier> {
        match &self.data.info {
            StructInfo::Declared { handle_idx, .. } => {
                let handle = self.module_env.data.module.datatype_handle_at(*handle_idx);
                Some(
                    self.module_env
                        .data
                        .module
                        .identifier_at(handle.name)
                        .to_owned(),
                )
            }
        }
    }

    /// Shortcut for accessing the symbol pool.
    pub fn symbol_pool(&self) -> &SymbolPool {
        self.module_env.symbol_pool()
    }

    /// Returns the location of this struct.
    pub fn get_loc(&self) -> Loc {
        self.data.loc.clone()
    }

    /// Returns the attributes of this struct.
    pub fn get_attributes(&self) -> &[Attribute] {
        &self.data.attributes
    }

    /// Gets the id associated with this struct.
    pub fn get_id(&self) -> DatatypeId {
        DatatypeId(self.data.name)
    }

    /// Gets the qualified id of this struct.
    pub fn get_qualified_id(&self) -> QualifiedId<DatatypeId> {
        self.module_env.get_id().qualified(self.get_id())
    }

    /// Determines whether this struct is native.
    pub fn is_native(&self) -> bool {
        match &self.data.info {
            StructInfo::Declared { def_idx, .. } => {
                let def = self.module_env.data.module.struct_def_at(*def_idx);
                def.field_information == StructFieldInformation::Native
            }
        }
    }

    /// Determines whether this struct is intrinsic.
    pub fn is_intrinsic(&self) -> bool {
        self.module_env
            .env
            .intrinsic_datatype_ids()
            .contains(&self.get_qualified_id())
    }

    /// Get the abilities of this struct.
    pub fn get_abilities(&self) -> AbilitySet {
        match &self.data.info {
            StructInfo::Declared { def_idx, .. } => {
                let def = self.module_env.data.module.struct_def_at(*def_idx);
                let handle = self
                    .module_env
                    .data
                    .module
                    .datatype_handle_at(def.struct_handle);
                handle.abilities
            }
        }
    }

    /// Determines whether memory-related operations needs to be declared for this struct.
    pub fn has_memory(&self) -> bool {
        self.get_abilities().has_key()
    }

    /// Get an iterator for the fields, ordered by offset.
    pub fn get_fields(&'env self) -> impl Iterator<Item = FieldEnv<'env>> {
        self.data
            .field_data
            .values()
            .sorted_by_key(|data| data.offset)
            .map(move |data| FieldEnv {
                parent_env: EnclosingEnv::Struct(self.clone()),
                data,
            })
    }

    /// Return the number of fields in the struct.
    pub fn get_field_count(&self) -> usize {
        self.data.field_data.len()
    }

    /// Gets a field by its id.
    pub fn get_field(&'env self, id: FieldId) -> FieldEnv<'env> {
        let data = self.data.field_data.get(&id).expect("FieldId undefined");
        FieldEnv {
            parent_env: EnclosingEnv::Struct(self.clone()),
            data,
        }
    }

    /// Find a field by its name.
    pub fn find_field(&'env self, name: Symbol) -> Option<FieldEnv<'env>> {
        let id = FieldId(name);
        self.data.field_data.get(&id).map(|data| FieldEnv {
            parent_env: EnclosingEnv::Struct(self.clone()),
            data,
        })
    }

    /// Gets a field by its offset.
    pub fn get_field_by_offset(&'env self, offset: usize) -> FieldEnv<'env> {
        for data in self.data.field_data.values() {
            if data.offset == offset {
                return FieldEnv {
                    parent_env: EnclosingEnv::Struct(self.clone()),
                    data,
                };
            }
        }
        unreachable!("invalid field lookup")
    }

    /// Whether the type parameter at position `idx` is declared as phantom.
    pub fn is_phantom_parameter(&self, idx: usize) -> bool {
        match &self.data.info {
            StructInfo::Declared { def_idx, .. } => {
                let def = self.module_env.data.module.struct_def_at(*def_idx);
                self.module_env
                    .data
                    .module
                    .datatype_handle_at(def.struct_handle)
                    .type_parameters[idx]
                    .is_phantom
            }
        }
    }

    /// Returns the type parameters associated with this struct.
    pub fn get_type_parameters(&self) -> Vec<TypeParameter> {
        // TODO: we currently do not know the original names of those formals, so we generate them.
        let pool = &self.module_env.env.symbol_pool;
        match &self.data.info {
            StructInfo::Declared { def_idx, .. } => {
                let module = &self.module_env.data.module;
                let sdef = module.struct_def_at(*def_idx);
                let shandle = module.datatype_handle_at(sdef.struct_handle);
                shandle
                    .type_parameters
                    .iter()
                    .enumerate()
                    .map(|(i, k)| {
                        TypeParameter(
                            pool.make(&format!("$tv{}", i)),
                            AbilityConstraint(k.constraints),
                        )
                    })
                    .collect_vec()
            }
        }
    }

    /// Returns the type parameters associated with this struct, with actual names.
    pub fn get_named_type_parameters(&self) -> Vec<TypeParameter> {
        match &self.data.info {
            StructInfo::Declared { def_idx, .. } => {
                let module = &self.module_env.data.module;
                let sdef = module.struct_def_at(*def_idx);
                let shandle = module.datatype_handle_at(sdef.struct_handle);
                shandle
                    .type_parameters
                    .iter()
                    .enumerate()
                    .map(|(i, k)| {
                        let name = self
                            .module_env
                            .data
                            .source_map
                            .get_struct_source_map(*def_idx)
                            .ok()
                            .and_then(|smap| smap.type_parameters.get(i))
                            .map(|(s, _)| s.clone())
                            .unwrap_or_else(|| format!("unknown#{}", i));
                        TypeParameter(
                            self.module_env.env.symbol_pool.make(&name),
                            AbilityConstraint(k.constraints),
                        )
                    })
                    .collect_vec()
            }
        }
    }
}

// =================================================================================================
/// # Field Environment

#[derive(Debug)]
pub struct FieldData {
    /// The name of this field.
    name: Symbol,

    /// The offset of this field.
    offset: usize,

    /// More information about this field
    info: FieldInfo,
}

#[derive(Debug)]
enum FieldInfo {
    /// The field is declared in Move.
    DeclaredStruct {
        /// The struct definition index of this field in its VM module.
        def_idx: StructDefinitionIndex,
    },
    DeclaredEnum {
        /// The enum definition index of this field in its VM module.
        def_idx: EnumDefinitionIndex,
    },
}

#[derive(Debug)]
pub enum EnclosingEnv<'env> {
    Struct(StructEnv<'env>),
    Variant(VariantEnv<'env>),
}

impl<'env> EnclosingEnv<'env> {
    pub fn module_env(&self) -> &ModuleEnv<'env> {
        match self {
            EnclosingEnv::Struct(s) => &s.module_env,
            EnclosingEnv::Variant(v) => &v.enum_env.module_env,
        }
    }
}

#[derive(Debug)]
pub struct FieldEnv<'env> {
    /// Reference to enclosing env.
    pub parent_env: EnclosingEnv<'env>,

    /// Reference to the field data.
    data: &'env FieldData,
}

impl<'env> FieldEnv<'env> {
    /// Gets the name of this field.
    pub fn get_name(&self) -> Symbol {
        self.data.name
    }

    /// Gets the id of this field.
    pub fn get_id(&self) -> FieldId {
        FieldId(self.data.name)
    }

    /// Returns the VM identifier for this field
    pub fn get_identifier(&'env self) -> Option<Identifier> {
        match &self.data.info {
            FieldInfo::DeclaredStruct { def_idx } => {
                let module = &self.parent_env.module_env().data.module;
                let def = module.struct_def_at(*def_idx);
                let offset = self.data.offset;
                let field = def.field(offset).expect("Bad field offset");
                Some(module.identifier_at(field.name).to_owned())
            }
            FieldInfo::DeclaredEnum { def_idx } => {
                let EnclosingEnv::Variant(v) = &self.parent_env else {
                    unreachable!()
                };
                let m = &v.enum_env.module_env.data.module;
                let enum_def = m.enum_def_at(*def_idx);
                let variant_def = &enum_def.variants[v.data.tag];
                let offset = self.data.offset;
                let field = variant_def.fields.get(offset).expect("Bad field offset");
                Some(m.identifier_at(field.name).to_owned())
            }
        }
    }

    /// Gets the type of this field.
    pub fn get_type(&self) -> Type {
        match &self.data.info {
            FieldInfo::DeclaredStruct { def_idx } => {
                let struct_def = self
                    .parent_env
                    .module_env()
                    .data
                    .module
                    .struct_def_at(*def_idx);
                let field = match &struct_def.field_information {
                    StructFieldInformation::Declared(fields) => &fields[self.data.offset],
                    StructFieldInformation::Native => unreachable!(),
                };
                self.parent_env
                    .module_env()
                    .globalize_signature(&field.signature.0)
            }
            FieldInfo::DeclaredEnum { def_idx } => {
                let EnclosingEnv::Variant(v) = &self.parent_env else {
                    unreachable!()
                };
                let enum_def = v.enum_env.module_env.data.module.enum_def_at(*def_idx);
                let variant_def = &enum_def.variants[v.data.tag];
                let field = &variant_def.fields[self.data.offset];
                v.enum_env
                    .module_env
                    .globalize_signature(&field.signature.0)
            }
        }
    }

    /// Get field offset.
    pub fn get_offset(&self) -> usize {
        self.data.offset
    }
}

// =================================================================================================
/// # Named Constant Environment

#[derive(Debug)]
pub struct NamedConstantData {
    /// The name of this constant
    name: Symbol,

    /// The location of this constant
    loc: Loc,

    /// The type of this constant
    typ: Type,

    /// The value of this constant
    value: Value,

    /// Attributes attached to this constant
    attributes: Vec<Attribute>,
}

#[derive(Debug)]
pub struct NamedConstantEnv<'env> {
    /// Reference to enclosing module.
    pub module_env: ModuleEnv<'env>,

    data: &'env NamedConstantData,
}

impl NamedConstantEnv<'_> {
    /// Returns the name of this constant
    pub fn get_name(&self) -> Symbol {
        self.data.name
    }

    /// Returns the id of this constant
    pub fn get_id(&self) -> NamedConstantId {
        NamedConstantId(self.data.name)
    }

    /// Returns the location of this constant
    pub fn get_loc(&self) -> Loc {
        self.data.loc.clone()
    }

    /// Returns the type of the constant
    pub fn get_type(&self) -> Type {
        self.data.typ.clone()
    }

    /// Returns the value of this constant
    pub fn get_value(&self) -> Value {
        self.data.value.clone()
    }

    /// Returns the attributes attached to this constant
    pub fn get_attributes(&self) -> &[Attribute] {
        &self.data.attributes
    }
}

// =================================================================================================
// # Function Environment

/// Represents a type parameter.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeParameter(pub Symbol, pub AbilityConstraint);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct AbilityConstraint(pub AbilitySet);

/// Represents a parameter.
#[derive(Debug, Clone)]
pub struct Parameter(pub Symbol, pub Type);

#[derive(Debug)]
pub struct FunctionData {
    /// Name of this function.
    name: Symbol,

    /// Location of this function.
    loc: Loc,

    /// The definition index of this function in its module.
    def_idx: FunctionDefinitionIndex,

    /// The handle index of this function in its module.
    handle_idx: FunctionHandleIndex,

    /// Attributes attached to this function.
    attributes: Vec<Attribute>,

    /// Top-level attributes attached to this function.
    toplevel_attributes: expansion::ast::Attributes,

    /// List of function argument names. Not in bytecode but obtained from AST.
    arg_names: Vec<Symbol>,

    /// List of type argument names. Not in bytecode but obtained from AST.
    #[allow(unused)]
    type_arg_names: Vec<Symbol>,

    /// A cache for the called functions.
    called_funs: RefCell<Option<BTreeSet<QualifiedId<FunId>>>>,

    /// A cache for the calling functions.
    calling_funs: RefCell<Option<BTreeSet<QualifiedId<FunId>>>>,

    /// A cache for the transitive closure of the called functions.
    transitive_closure_of_called_funs: RefCell<Option<BTreeSet<QualifiedId<FunId>>>>,
}

impl FunctionData {
    pub fn stub(
        name: Symbol,
        def_idx: FunctionDefinitionIndex,
        handle_idx: FunctionHandleIndex,
    ) -> Self {
        FunctionData {
            name,
            loc: Loc::default(),
            attributes: Vec::default(),
            toplevel_attributes: expansion::ast::Attributes::default(),
            def_idx,
            handle_idx,
            arg_names: vec![],
            type_arg_names: vec![],
            called_funs: Default::default(),
            calling_funs: Default::default(),
            transitive_closure_of_called_funs: Default::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionEnv<'env> {
    /// Reference to enclosing module.
    pub module_env: ModuleEnv<'env>,

    /// Reference to the function data.
    data: &'env FunctionData,
}

impl<'env> FunctionEnv<'env> {
    /// Returns the name of this function.
    pub fn get_name(&self) -> Symbol {
        self.data.name
    }

    /// Gets full name as string.
    pub fn get_full_name_str(&self) -> String {
        format!(
            "{}::{}",
            self.module_env.get_name().display(self.symbol_pool()),
            self.get_name_str()
        )
    }

    pub fn get_name_str(&self) -> String {
        self.get_name().display(self.symbol_pool()).to_string()
    }

    /// Returns the VM identifier for this function
    pub fn get_identifier(&'env self) -> Identifier {
        let m = &self.module_env.data.module;
        m.identifier_at(m.function_handle_at(self.data.handle_idx).name)
            .to_owned()
    }

    /// Gets the id of this function.
    pub fn get_id(&self) -> FunId {
        FunId(self.data.name)
    }

    /// Gets the qualified id of this function.
    pub fn get_qualified_id(&self) -> QualifiedId<FunId> {
        self.module_env.get_id().qualified(self.get_id())
    }

    /// Gets the definition index of this function.
    pub fn get_def_idx(&self) -> FunctionDefinitionIndex {
        self.data.def_idx
    }

    /// Shortcut for accessing the symbol pool.
    pub fn symbol_pool(&self) -> &SymbolPool {
        self.module_env.symbol_pool()
    }

    /// Returns the location of this function.
    pub fn get_loc(&self) -> Loc {
        self.data.loc.clone()
    }

    /// Returns the attributes of this function.
    pub fn get_attributes(&self) -> &[Attribute] {
        &self.data.attributes
    }

    /// Returns the location of the bytecode at the given offset.
    pub fn get_bytecode_loc(&self, offset: u16) -> Loc {
        if let Ok(fmap) = self
            .module_env
            .data
            .source_map
            .get_function_source_map(self.data.def_idx)
        {
            if let Some(loc) = fmap.get_code_location(offset) {
                return self.module_env.env.to_loc(&loc);
            }
        }
        self.get_loc()
    }

    /// Returns the bytecode associated with this function.
    pub fn get_bytecode(&self) -> &[Bytecode] {
        let function_definition = self
            .module_env
            .data
            .module
            .function_def_at(self.get_def_idx());
        match &function_definition.code {
            Some(code) => &code.code,
            None => &[],
        }
    }

    /// Returns the variant jump tables for this function.
    pub fn get_jump_tables(&self) -> &[VariantJumpTable] {
        let function_definition = self
            .module_env
            .data
            .module
            .function_def_at(self.get_def_idx());
        &function_definition.code.as_ref().unwrap().jump_tables
    }

    /// Returns the top-level attributes for this function
    pub fn get_toplevel_attributes(&self) -> &expansion::ast::Attributes {
        &self.data.toplevel_attributes
    }

    /// Returns true if this function is native.
    pub fn is_native(&self) -> bool {
        self.definition().is_native()
    }

    pub fn is_intrinsic(&self) -> bool {
        self.module_env
            .env
            .intrinsic_fun_ids()
            .contains(&self.get_qualified_id())
    }

    /// Returns true if this is the well-known native or intrinsic function of the given name.
    /// The function must reside either in stdlib or extlib address domain.
    pub fn is_well_known(&self, name: &str) -> bool {
        let env = self.module_env.env;
        if !self.is_native() && !self.is_intrinsic() {
            return false;
        }
        let addr = self.module_env.get_name().addr();
        (addr == &env.get_stdlib_address() || addr == &env.get_extlib_address())
            && self.get_full_name_str() == name
    }

    /// Return the visibility of this function
    pub fn visibility(&self) -> FunctionVisibility {
        self.definition().visibility
    }

    /// Return true if the function is an entry fucntion
    pub fn is_entry(&self) -> bool {
        self.definition().is_entry
    }

    /// Return the visibility string for this function. Useful for formatted printing.
    pub fn visibility_str(&self) -> &str {
        match self.visibility() {
            Visibility::Public => "public ",
            Visibility::Friend => "public(friend) ",
            Visibility::Private => "",
        }
    }

    /// Return whether this function is exposed outside of the module.
    pub fn is_exposed(&self) -> bool {
        self.module_env.is_script_module()
            || self.definition().is_entry
            || match self.definition().visibility {
                Visibility::Public | Visibility::Friend => true,
                Visibility::Private => false,
            }
    }

    /// Return whether this function is exposed outside of the module.
    pub fn has_unknown_callers(&self) -> bool {
        self.module_env.is_script_module()
            || self.definition().is_entry
            || match self.definition().visibility {
                Visibility::Public => true,
                Visibility::Private | Visibility::Friend => false,
            }
    }

    /// Returns true if the function is a script function
    pub fn is_script(&self) -> bool {
        // The main function of a scipt is a script function
        self.module_env.is_script_module() || self.definition().is_entry
    }

    /// Return true if this function is a friend function
    pub fn is_friend(&self) -> bool {
        self.definition().visibility == Visibility::Friend
    }

    /// Returns true if this function mutates any references (i.e. has &mut parameters).
    pub fn is_mutating(&self) -> bool {
        self.get_parameters()
            .iter()
            .any(|Parameter(_, ty)| ty.is_mutable_reference())
    }

    /// Returns the type parameters associated with this function.
    pub fn get_type_parameters(&self) -> Vec<TypeParameter> {
        // TODO: currently the translation scheme isn't working with using real type
        //   parameter names, so use indices instead.
        let fdef = self.definition();
        let fhandle = self
            .module_env
            .data
            .module
            .function_handle_at(fdef.function);
        fhandle
            .type_parameters
            .iter()
            .enumerate()
            .map(|(i, k)| {
                TypeParameter(
                    self.module_env.env.symbol_pool.make(&format!("$tv{}", i)),
                    AbilityConstraint(*k),
                )
            })
            .collect_vec()
    }

    /// Returns the type parameters with the real names.
    pub fn get_named_type_parameters(&self) -> Vec<TypeParameter> {
        let fdef = self.definition();
        let fhandle = self
            .module_env
            .data
            .module
            .function_handle_at(fdef.function);
        fhandle
            .type_parameters
            .iter()
            .enumerate()
            .map(|(i, k)| {
                let name = self
                    .module_env
                    .data
                    .source_map
                    .get_function_source_map(self.data.def_idx)
                    .ok()
                    .and_then(|fmap| fmap.type_parameters.get(i))
                    .map(|(s, _)| s.clone())
                    .unwrap_or_else(|| format!("unknown#{}", i));
                TypeParameter(
                    self.module_env.env.symbol_pool.make(&name),
                    AbilityConstraint(*k),
                )
            })
            .collect_vec()
    }

    pub fn get_parameter_count(&self) -> usize {
        let fdef = self.definition();
        let module = &self.module_env.data.module;
        let fhandle = module.function_handle_at(fdef.function);
        module.signature_at(fhandle.parameters).0.len()
    }

    /// Return the number of type parameters for self
    pub fn get_type_parameter_count(&self) -> usize {
        let fdef = self.definition();
        let fhandle = self
            .module_env
            .data
            .module
            .function_handle_at(fdef.function);
        fhandle.type_parameters.len()
    }

    /// Return `true` if idx is a formal parameter index
    pub fn is_parameter(&self, idx: usize) -> bool {
        idx < self.get_parameter_count()
    }

    /// Return true if this is a named parameter of this function.
    pub fn is_named_parameter(&self, name: &str) -> bool {
        self.get_parameters()
            .iter()
            .any(|p| self.symbol_pool().string(p.0).as_ref() == name)
    }

    /// Returns the parameter types associated with this function
    pub fn get_parameter_types(&self) -> Vec<Type> {
        let fdef = self.definition();
        let module = &self.module_env.data.module;
        let fhandle = module.function_handle_at(fdef.function);
        module
            .signature_at(fhandle.parameters)
            .0
            .iter()
            .map(|tv: &SignatureToken| self.module_env.globalize_signature(tv))
            .collect()
    }

    /// Returns the regular parameters associated with this function.
    pub fn get_parameters(&self) -> Vec<Parameter> {
        let fdef = self.definition();
        let module = &self.module_env.data.module;
        let fhandle = module.function_handle_at(fdef.function);
        module
            .signature_at(fhandle.parameters)
            .0
            .iter()
            .map(|tv: &SignatureToken| self.module_env.globalize_signature(tv))
            .zip(self.data.arg_names.iter())
            .map(|(s, i)| Parameter(*i, s))
            .collect_vec()
    }

    /// Returns return types of this function.
    pub fn get_return_types(&self) -> Vec<Type> {
        let fdef = self.definition();
        let module = &self.module_env.data.module;
        let fhandle = module.function_handle_at(fdef.function);
        module
            .signature_at(fhandle.return_)
            .0
            .iter()
            .map(|tv: &SignatureToken| self.module_env.globalize_signature(tv))
            .collect_vec()
    }

    /// Returns return type at given index.
    pub fn get_return_type(&self, idx: usize) -> Type {
        self.get_return_types()[idx].clone()
    }

    /// Returns the number of return values of this function.
    pub fn get_return_count(&self) -> usize {
        let fdef = self.definition();
        let module = &self.module_env.data.module;
        let fhandle = module.function_handle_at(fdef.function);
        module.signature_at(fhandle.return_).0.len()
    }

    /// Get the name to be used for a local. If the local is an argument, use that for naming,
    /// otherwise generate a unique name.
    pub fn get_local_name(&self, idx: usize) -> Symbol {
        if idx < self.data.arg_names.len() {
            return self.data.arg_names[idx];
        }
        // Try to obtain name from source map.
        if let Ok(fmap) = self
            .module_env
            .data
            .source_map
            .get_function_source_map(self.data.def_idx)
        {
            if let Some((ident, _)) = fmap.get_parameter_or_local_name(idx as u64) {
                // The Move compiler produces temporary names of the form `<foo>%#<num>`,
                // where <num> seems to be generated non-deterministically.
                // Substitute this by a deterministic name which the backend accepts.
                let clean_ident = if ident.contains("%#") {
                    format!("tmp#${}", idx)
                } else {
                    ident
                };
                return self.module_env.env.symbol_pool.make(clean_ident.as_str());
            }
        }
        self.module_env.env.symbol_pool.make(&format!("$t{}", idx))
    }

    /// Returns true if the index is for a temporary, not user declared local.
    pub fn is_temporary(&self, idx: usize) -> bool {
        if idx >= self.get_local_count() {
            return true;
        }
        let name = self.get_local_name(idx);
        self.symbol_pool().string(name).contains("tmp#$")
    }

    /// Gets the number of proper locals of this function. Those are locals which are declared
    /// by the user and also have a user assigned name which can be discovered via `get_local_name`.
    /// Note we may have more anonymous locals generated e.g by the 'stackless' transformation.
    pub fn get_local_count(&self) -> usize {
        let fdef = self.definition();
        let module = &self.module_env.data.module;
        let num_params = self.get_parameter_count();
        let num_locals = fdef
            .code
            .as_ref()
            .map(|code| module.signature_at(code.locals).0.len())
            .unwrap_or(0);
        num_params + num_locals
    }

    /// Gets the type of the local at index. This must use an index in the range as determined by
    /// `get_local_count`.
    pub fn get_local_type(&self, idx: usize) -> Type {
        let fdef = self.definition();
        let module = &self.module_env.data.module;
        let fhandle = module.function_handle_at(fdef.function);
        let parameters = &module.signature_at(fhandle.parameters).0;
        let st = if idx < parameters.len() {
            &parameters[idx]
        } else {
            let locals = &module.signature_at(fdef.code.as_ref().unwrap().locals).0;
            &locals[idx - parameters.len()]
        };
        self.module_env.globalize_signature(st)
    }

    /// Returns the acquired global resource types.
    pub fn get_acquires_global_resources(&'env self) -> Vec<DatatypeId> {
        let function_definition = self
            .module_env
            .data
            .module
            .function_def_at(self.get_def_idx());
        function_definition
            .acquires_global_resources
            .iter()
            .map(|x| self.module_env.get_struct_id(*x))
            .collect()
    }

    /// Determine whether the function is target of verification.
    pub fn should_verify(&self, default_scope: &VerificationScope) -> bool {
        if let VerificationScope::Only(function_name) = default_scope {
            // Overrides pragmas.
            return self.matches_name(function_name);
        }
        if !self.module_env.is_target() {
            // Don't generate verify method for functions from dependencies.
            return false;
        }

        match default_scope {
            // By using `is_exposed`, we essentially mark all of Public, Script, Friend to be
            // in the verification scope because they are "exposed" functions in this module.
            // We may want to change `VerificationScope::Public` to `VerificationScope::Exposed` as
            // well for consistency.
            VerificationScope::Public => self.is_exposed(),
            VerificationScope::All => true,
            VerificationScope::Only(_) => unreachable!(),
            VerificationScope::OnlyModule(module_name) => self.module_env.matches_name(module_name),
            VerificationScope::None => false,
        }
    }

    /// Returns true if either the name or simple name of this function matches the given string
    pub fn matches_name(&self, name: &str) -> bool {
        name.eq(&*self.get_simple_name_string()) || name.eq(&*self.get_name_string())
    }

    /// Determine whether this function is explicitly deactivated for verification.
    pub fn is_explicitly_not_verified(&self, scope: &VerificationScope) -> bool {
        if let VerificationScope::Only(function_name) = scope {
            // Overrides pragmas.
            return !self.matches_name(function_name);
        } else {
            false
        }
    }

    /// Get the functions that call this one
    pub fn get_calling_functions(&self) -> BTreeSet<QualifiedId<FunId>> {
        if let Some(calling) = &*self.data.calling_funs.borrow() {
            return calling.clone();
        }
        let mut set: BTreeSet<QualifiedId<FunId>> = BTreeSet::new();
        for module_env in self.module_env.env.get_modules() {
            for fun_env in module_env.get_functions() {
                if fun_env
                    .get_called_functions()
                    .contains(&self.get_qualified_id())
                {
                    set.insert(fun_env.get_qualified_id());
                }
            }
        }
        *self.data.calling_funs.borrow_mut() = Some(set.clone());
        set
    }

    /// Get the functions that this one calls
    pub fn get_called_functions(&self) -> BTreeSet<QualifiedId<FunId>> {
        if let Some(called) = &*self.data.called_funs.borrow() {
            return called.clone();
        }
        let called: BTreeSet<_> = self
            .get_bytecode()
            .iter()
            .flat_map(|c| match c {
                Bytecode::Call(i) => vec![self.module_env.get_used_function(*i).get_qualified_id()],
                Bytecode::CallGeneric(i) => {
                    let handle_idx = self
                        .module_env
                        .data
                        .module
                        .function_instantiation_at(*i)
                        .handle;
                    vec![self
                        .module_env
                        .get_used_function(handle_idx)
                        .get_qualified_id()]
                }
                Bytecode::VecPack { .. } => vec![
                    self.module_env.env.get_fun_qid("vector", "empty"),
                    self.module_env.env.get_fun_qid("vector", "push_back"),
                ],
                Bytecode::VecLen { .. } => {
                    vec![self.module_env.env.get_fun_qid("vector", "length")]
                }
                Bytecode::VecImmBorrow { .. } => {
                    vec![self.module_env.env.get_fun_qid("vector", "borrow")]
                }
                Bytecode::VecMutBorrow { .. } => {
                    vec![self.module_env.env.get_fun_qid("vector", "borrow_mut")]
                }
                Bytecode::VecPushBack { .. } => {
                    vec![self.module_env.env.get_fun_qid("vector", "push_back")]
                }
                Bytecode::VecPopBack { .. } => {
                    vec![self.module_env.env.get_fun_qid("vector", "pop_back")]
                }
                Bytecode::VecUnpack { .. } => vec![
                    self.module_env.env.get_fun_qid("vector", "destroy_empty"),
                    self.module_env.env.get_fun_qid("vector", "pop_back"),
                ],
                Bytecode::VecSwap { .. } => vec![self.module_env.env.get_fun_qid("vector", "swap")],
                _ => vec![],
            })
            .collect();
        *self.data.called_funs.borrow_mut() = Some(called.clone());
        called
    }

    /// Get the transitive closure of the called functions
    pub fn get_transitive_closure_of_called_functions(&self) -> BTreeSet<QualifiedId<FunId>> {
        if let Some(trans_called) = &*self.data.transitive_closure_of_called_funs.borrow() {
            return trans_called.clone();
        }

        let mut set = BTreeSet::new();
        let mut reachable_funcs = VecDeque::new();
        reachable_funcs.push_back(self.clone());

        // BFS in reachable_funcs to collect all reachable functions
        while !reachable_funcs.is_empty() {
            let current_fnc = reachable_funcs.pop_front();
            if let Some(fnc) = current_fnc {
                for callee in fnc.get_called_functions() {
                    let f = self.module_env.env.get_function(callee);
                    let qualified_id = f.get_qualified_id();
                    if !set.contains(&qualified_id) {
                        set.insert(qualified_id);
                        reachable_funcs.push_back(f.clone());
                    }
                }
            }
        }
        *self.data.transitive_closure_of_called_funs.borrow_mut() = Some(set.clone());
        set
    }

    /// Returns the function name excluding the address and the module name
    pub fn get_simple_name_string(&self) -> Rc<String> {
        self.symbol_pool().string(self.get_name())
    }

    /// Returns the function name with the module name excluding the address
    pub fn get_name_string(&self) -> Rc<str> {
        if self.module_env.is_script_module() {
            Rc::from(format!("Script::{}", self.get_simple_name_string()))
        } else {
            let module_name = self
                .module_env
                .get_name()
                .display(self.module_env.symbol_pool());
            Rc::from(format!(
                "{}::{}",
                module_name,
                self.get_simple_name_string()
            ))
        }
    }

    fn definition(&'env self) -> &'env FunctionDefinition {
        self.module_env
            .data
            .module
            .function_def_at(self.data.def_idx)
    }

    /// Produce a TypeDisplayContext to print types within the scope of this env
    pub fn get_type_display_ctx(&self) -> TypeDisplayContext {
        let type_param_names = self
            .get_type_parameters()
            .iter()
            .map(|param| param.0)
            .collect();
        TypeDisplayContext::WithEnv {
            env: self.module_env.env,
            type_param_names: Some(type_param_names),
        }
    }

    /// Produce a TypeDisplayContext to print types within the scope of this env,
    /// with source names for type parameters
    pub fn get_named_type_display_ctx(&self) -> TypeDisplayContext {
        let type_param_names = self
            .get_named_type_parameters()
            .iter()
            .map(|param| param.0)
            .collect();
        TypeDisplayContext::WithEnv {
            env: self.module_env.env,
            type_param_names: Some(type_param_names),
        }
    }
}

// =================================================================================================
// # Expression Environment

/// Represents context for an expression.
#[derive(Debug, Clone)]
pub struct ExpInfo {
    /// The associated location of this expression.
    loc: Loc,
    /// The type of this expression.
    ty: Type,
    /// The associated instantiation of type parameters for this expression, if applicable
    instantiation: Option<Vec<Type>>,
}

impl ExpInfo {
    pub fn new(loc: Loc, ty: Type) -> Self {
        ExpInfo {
            loc,
            ty,
            instantiation: None,
        }
    }
}

// =================================================================================================
// # Formatting

pub struct LocDisplay<'env> {
    loc: &'env Loc,
    env: &'env GlobalEnv,
    only_line: bool,
}

impl Loc {
    pub fn display<'env>(&'env self, env: &'env GlobalEnv) -> LocDisplay<'env> {
        LocDisplay {
            loc: self,
            env,
            only_line: false,
        }
    }

    pub fn display_line_only<'env>(&'env self, env: &'env GlobalEnv) -> LocDisplay<'env> {
        LocDisplay {
            loc: self,
            env,
            only_line: true,
        }
    }
}

impl fmt::Display for LocDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((fname, pos)) = self.env.get_file_and_location(self.loc) {
            if self.only_line {
                write!(f, "at {}:{}", fname, pos.line + LineOffset(1))
            } else {
                let offset = self.loc.span.end() - self.loc.span.start();
                write!(
                    f,
                    "at {}:{}:{}+{}",
                    fname,
                    pos.line + LineOffset(1),
                    pos.column + ColumnOffset(1),
                    offset,
                )
            }
        } else {
            write!(f, "{:?}", self.loc)
        }
    }
}

pub trait GetNameString {
    fn get_name_for_display(&self, env: &GlobalEnv) -> String;
}

impl GetNameString for QualifiedId<DatatypeId> {
    fn get_name_for_display(&self, env: &GlobalEnv) -> String {
        match env.get_struct_or_enum_qid(*self) {
            StructOrEnumEnv::Struct(struct_env) => struct_env.get_full_name_str(),
            StructOrEnumEnv::Enum(enum_env) => enum_env.get_full_name_str(),
        }
    }
}

impl GetNameString for QualifiedId<FunId> {
    fn get_name_for_display(&self, env: &GlobalEnv) -> String {
        env.get_function_qid(*self).get_full_name_str()
    }
}

impl<Id: Clone> fmt::Display for EnvDisplay<'_, QualifiedId<Id>>
where
    QualifiedId<Id>: GetNameString,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(&self.val.get_name_for_display(self.env))
    }
}

impl<Id: Clone> fmt::Display for EnvDisplay<'_, QualifiedInstId<Id>>
where
    QualifiedId<Id>: GetNameString,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.env.display(&self.val.to_qualified_id()))?;
        if !self.val.inst.is_empty() {
            let tctx = TypeDisplayContext::WithEnv {
                env: self.env,
                type_param_names: None,
            };
            write!(f, "<")?;
            let mut sep = "";
            for ty in &self.val.inst {
                write!(f, "{}{}", sep, ty.display(&tctx))?;
                sep = ", ";
            }
            write!(f, ">")?;
        }
        Ok(())
    }
}

fn filter_out_sensetives(input: &str) -> String {
    if input.is_empty() {
        return input.to_string();
    }

    let filter_regex =
        Regex::new(r"/(?:Users|home)/[^/]+/\.move/[^/]+/(?:crates|packages)/([^/]+)/").unwrap();

    filter_regex.replace_all(input, "$1/").to_string()
}
