use smallvec::SmallVec;

use crate::generic::context_object::*;

pub trait NamedObject {
    fn get_name(&self) -> Option<&str>;
}

pub trait VarAccessor<ParamType: NamedObject> {
    fn get_var(&self, idx: VarIndex) -> &ParamType;
    fn get_var_index(&self, name: &str, occurrence: usize) -> Option<VarIndex>;
    fn get_name_occurrence(&self, idx: VarIndex, param: &ParamType) -> usize;
}

impl<ParamType: NamedObject> VarAccessor<ParamType> for [ParamType] {
    fn get_var(&self, idx: VarIndex) -> &ParamType {
        &self[idx as usize]
    }

    fn get_var_index(&self, name: &str, mut occurrence: usize) -> Option<VarIndex> {
        let mut idx: VarIndex = self.len() as VarIndex;
        for param in self.iter().rev() {
            idx -= 1;
            if param.get_name() == Some(name) {
                if occurrence == 0 {
                    return Some(idx);
                }
                occurrence -= 1;
            }
        }
        None
    }

    fn get_name_occurrence(&self, mut idx: VarIndex, idx_param: &ParamType) -> usize {
        let name = idx_param.get_name();
        let mut occurrence = 0;
        idx -= self.len() as VarIndex;
        for param in self.iter().rev() {
            idx += 1;
            if idx == 0 {
                return occurrence;
            }
            if param.get_name() == name {
                occurrence += 1;
            }
        }
        panic!("invalid DeBruijn level");
    }
}

impl<ParamType: NamedObject> VarAccessor<ParamType> for Vec<ParamType> {
    fn get_var(&self, idx: VarIndex) -> &ParamType {
        self.as_slice().get_var(idx)
    }

    fn get_var_index(&self, name: &str, occurrence: usize) -> Option<VarIndex> {
        self.as_slice().get_var_index(name, occurrence)
    }

    fn get_name_occurrence(&self, idx: VarIndex, idx_param: &ParamType) -> usize {
        self.as_slice().get_name_occurrence(idx, idx_param)
    }
}

impl<ParamType: NamedObject, const LEN: usize> VarAccessor<ParamType>
    for SmallVec<[ParamType; LEN]>
{
    fn get_var(&self, idx: VarIndex) -> &ParamType {
        self.as_slice().get_var(idx)
    }

    fn get_var_index(&self, name: &str, occurrence: usize) -> Option<VarIndex> {
        self.as_slice().get_var_index(name, occurrence)
    }

    fn get_name_occurrence(&self, idx: VarIndex, idx_param: &ParamType) -> usize {
        self.as_slice().get_name_occurrence(idx, idx_param)
    }
}

#[derive(Clone, Copy, Debug)]
enum LocalContextStack<'a, 'b, ParamType: NamedObject> {
    Root,
    Param {
        param: &'a ParamType,
        parent: &'b LocalContextStack<'a, 'b, ParamType>,
    },
    Params {
        params: &'a [ParamType],
        parent: &'b LocalContextStack<'a, 'b, ParamType>,
    },
}

/// To get some idea what a context should look like, see the documentation of `VarIndex`.
///
/// We want global indices to resolve fast, but since we want to be able to treat variables as
/// global temporarily, we cannot just reference a slice. Instead, a trait object to access globals
/// is provided when creating a context.
///
/// Locals are a bit tricky because each local variable can have its own temporary lifetime, so we
/// cannot just push references to them into a single vector in safe Rust. Instead, each context
/// references its parent, which usually lives in a parent frame on the Rust call stack. As a
/// consequence, we need to iterate over frames when accessing locals by index.
#[derive(Clone, Copy)]
pub struct Context<'a, 'b: 'a, 'c, ParamType: NamedObject> {
    globals: &'b dyn VarAccessor<ParamType>,
    locals: LocalContextStack<'a, 'c, ParamType>,
    locals_start: VarIndex,
}

impl<'a, 'b, 'c, ParamType: NamedObject> Context<'a, 'b, 'c, ParamType> {
    pub fn new(globals: &'b dyn VarAccessor<ParamType>) -> Self {
        Context {
            globals,
            locals: LocalContextStack::Root,
            locals_start: 0,
        }
    }

    pub fn with_local<'d, 'e>(&'e self, param: &'d ParamType) -> Context<'d, 'b, 'e, ParamType>
    where
        'a: 'd,
        'c: 'e,
    {
        Context {
            globals: self.globals,
            locals: LocalContextStack::Param {
                param,
                parent: &self.locals,
            },
            locals_start: self.locals_start - 1,
        }
    }

    pub fn with_locals<'d, 'e>(&'e self, params: &'a [ParamType]) -> Context<'d, 'b, 'e, ParamType>
    where
        'a: 'd,
        'c: 'e,
    {
        Context {
            globals: self.globals,
            locals: LocalContextStack::Params {
                params,
                parent: &self.locals,
            },
            locals_start: self.locals_start - (params.len() as VarIndex),
        }
    }

    pub fn get_var(&self, mut idx: VarIndex) -> &'a ParamType {
        if idx < 0 {
            /* The recursive version is much nicer, but Rust has no tail recursion guarantee. */
            let mut locals = &self.locals;
            loop {
                match locals {
                    LocalContextStack::Root => panic!("invalid De Bruijn index"),
                    LocalContextStack::Param { param, parent } => {
                        idx += 1;
                        if idx == 0 {
                            return param;
                        }
                        locals = parent;
                    }
                    LocalContextStack::Params { params, parent } => {
                        let len = params.len() as VarIndex;
                        idx += len;
                        if idx >= 0 {
                            return &params[idx as usize];
                        }
                        locals = parent;
                    }
                }
            }
        } else {
            self.globals.get_var(idx)
        }
    }

    pub fn get_var_index(&self, name: &str, mut occurrence: usize) -> Option<VarIndex> {
        let mut locals = &self.locals;
        let mut idx: VarIndex = 0;
        loop {
            match locals {
                LocalContextStack::Root => break,
                LocalContextStack::Param { param, parent } => {
                    idx -= 1;
                    if param.get_name() == Some(name) {
                        if occurrence == 0 {
                            return Some(idx);
                        }
                        occurrence -= 1;
                    }
                    locals = parent;
                }
                LocalContextStack::Params { params, parent } => {
                    for param in params.iter().rev() {
                        idx -= 1;
                        if param.get_name() == Some(name) {
                            if occurrence == 0 {
                                return Some(idx);
                            }
                            occurrence -= 1;
                        }
                    }
                    locals = parent;
                }
            }
        }
        self.globals.get_var_index(name, occurrence)
    }

    pub fn get_name_occurrence(&self, mut idx: VarIndex, idx_param: &ParamType) -> usize {
        if idx < 0 {
            let name = idx_param.get_name();
            let mut occurrence = 0;
            let mut locals = &self.locals;
            loop {
                match locals {
                    LocalContextStack::Root => panic!("invalid De Bruijn index"),
                    LocalContextStack::Param { param, parent } => {
                        idx += 1;
                        if idx == 0 {
                            return occurrence;
                        }
                        if param.get_name() == name {
                            occurrence += 1;
                        }
                        locals = parent;
                    }
                    LocalContextStack::Params { params, parent } => {
                        for param in params.iter().rev() {
                            idx += 1;
                            if idx == 0 {
                                return occurrence;
                            }
                            if param.get_name() == name {
                                occurrence += 1;
                            }
                        }
                        locals = parent;
                    }
                }
            }
        } else {
            self.globals.get_name_occurrence(idx, idx_param)
        }
    }

    pub fn locals_start(&self) -> VarIndex {
        self.locals_start
    }

    pub fn shifted_to_context<T: ContextObject>(&self, obj: &T, var_idx: VarIndex) -> T {
        if var_idx < 0 {
            obj.with_shifted_vars(self.locals_start() - var_idx, 0, var_idx)
        } else {
            obj.clone()
        }
    }
}
