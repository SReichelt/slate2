use smallvec::SmallVec;

/// A De Bruijn level if nonnegative, or a bitwise negated De Bruijn index if negative.
///
/// We can regard nonnegative indices as referring to "globals" or "free variables", and negative
/// indices as referring to "locals" or "bound variables". Both have their uses: An expression that
/// refers to globals but is closed with respect to locals (i.e. does not have any loose bound
/// variables) can be reused without modification at all places where those globals are in scope.
///
/// So when working inside a specific context, we generally want to make sure that the condition
/// above is satisfied, which means that whenever we "enter" a binder, we may want to shift the
/// variable indices referring to that binder from local to global. (We often avoid this because we
/// prefer to keep expressions constant, but then we need to shift their loose bound variables when
/// transferring them to another context.)
///
/// The encoding is chosen so that array indices become the most convenient, in cases where a
/// binder contains multiple parameters. We can think of the indices as referencing either the
/// bottom or the top of the context stack:
///
///  locals  | -1  (top of stack depends on current expression)
///          | -2
/// /\/\/\/\/\/\/\
///          |  1
///  globals |  0  (bottom of stack stays fixed)
///
/// (Interestingly, this is exactly how array indexing works in some programming languages.)
pub type VarIndex = isize;

/// The most essential data of a context is merely the number of loose bound variables. We
/// frequently compare De Bruijn indices against this number to make sure they are in range.
/// Moreover, whenever we have two contexts where one is a subcontext of the other, the difference
/// between their number of loose bound variables indicates their exact relationship, i.e. how far
/// we have to shift De Bruijn indices to transfer an expression from one context to the other.
pub trait Context {
    /// Returns the lowest valid De Bruijn index in this context.
    fn locals_start(&self) -> VarIndex;

    /// Returns the required shift value in order to transfer an expression from this context to
    /// the given subcontext.
    fn subcontext_shift(&self, subctx: &Self) -> VarIndex {
        subctx.locals_start() - self.locals_start()
    }

    /// Checks whether the given variable index refers to a local variable in the given
    /// supercontext.
    fn is_local_in_supercontext(&self, idx: VarIndex, superctx: &Self) -> bool {
        idx < superctx.subcontext_shift(self)
    }

    fn as_minimal(&self) -> MinimalContext {
        MinimalContext {
            locals_start: self.locals_start(),
        }
    }
}

/// A context where local variables of type `ParamType` can be added.
pub trait ParamContext<ParamType>: Context {
    /// Temporarily creates a new context with `param` added on top, and calls `f` with this
    /// context.
    fn with_local<R>(&self, param: &ParamType, f: impl FnOnce(&Self) -> R) -> R;

    /// Temporarily creates a new context with `params` added on top, and calls `f` with this
    /// context.
    fn with_locals<R>(&self, params: &[ParamType], f: impl FnOnce(&Self) -> R) -> R;
}

#[derive(Clone, Copy, Debug)]
pub struct MinimalContext {
    locals_start: VarIndex,
}

impl MinimalContext {
    pub fn new() -> Self {
        MinimalContext { locals_start: 0 }
    }
}

impl Context for MinimalContext {
    fn locals_start(&self) -> VarIndex {
        self.locals_start
    }
}

impl<ParamType> ParamContext<ParamType> for MinimalContext {
    fn with_local<R>(&self, _param: &ParamType, f: impl FnOnce(&Self) -> R) -> R {
        let local_ctx = MinimalContext {
            locals_start: self.locals_start - 1,
        };
        f(&local_ctx)
    }

    fn with_locals<R>(&self, params: &[ParamType], f: impl FnOnce(&Self) -> R) -> R {
        let local_ctx = MinimalContext {
            locals_start: self.locals_start - (params.len() as VarIndex),
        };
        f(&local_ctx)
    }
}

/// A trait that is often used in combination with `ParamContext` to retrieve variables in the
/// context. It is also implemented for ranges and vectors so that these can be used directly to
/// provide globals.
pub trait VarAccessor<ParamType> {
    /// Returns the variable with the given De Bruijn index or level. Panics if the index is out
    /// of range.
    fn get_var(&self, idx: VarIndex) -> &ParamType;

    /// Iterates over all variables in reverse order, i.e. starting with the nearest in scope.
    /// The method returns as soon as `f` returns `Some(...)`.
    fn for_each_var<R>(&self, f: impl FnMut(VarIndex, &ParamType) -> Option<R>) -> Option<R>;
}

impl<ParamType> VarAccessor<ParamType> for [ParamType] {
    fn get_var(&self, idx: VarIndex) -> &ParamType {
        &self[idx as usize]
    }

    fn for_each_var<R>(&self, mut f: impl FnMut(VarIndex, &ParamType) -> Option<R>) -> Option<R> {
        let mut idx = self.len() as VarIndex;
        for param in self.iter().rev() {
            idx -= 1;
            let result = f(idx, param);
            if result.is_some() {
                return result;
            }
        }
        None
    }
}

impl<ParamType> VarAccessor<ParamType> for Vec<ParamType> {
    fn get_var(&self, idx: VarIndex) -> &ParamType {
        self.as_slice().get_var(idx)
    }

    fn for_each_var<R>(&self, f: impl FnMut(VarIndex, &ParamType) -> Option<R>) -> Option<R> {
        self.as_slice().for_each_var(f)
    }
}

impl<ParamType, const LEN: usize> VarAccessor<ParamType> for SmallVec<[ParamType; LEN]> {
    fn get_var(&self, idx: VarIndex) -> &ParamType {
        self.as_slice().get_var(idx)
    }

    fn for_each_var<R>(&self, f: impl FnMut(VarIndex, &ParamType) -> Option<R>) -> Option<R> {
        self.as_slice().for_each_var(f)
    }
}

impl<ParamType, T: VarAccessor<ParamType>> VarAccessor<ParamType> for &T {
    fn get_var(&self, idx: VarIndex) -> &ParamType {
        (*self).get_var(idx)
    }

    fn for_each_var<R>(&self, f: impl FnMut(VarIndex, &ParamType) -> Option<R>) -> Option<R> {
        (*self).for_each_var(f)
    }
}

enum LocalContextStack<ParamType> {
    Root,
    Params {
        params: *const ParamType,
        params_len: usize,
        parent: *const LocalContextStack<ParamType>,
    },
}

/// To get some idea what a context should look like, see the documentation of `VarIndex`.
///
/// We want global indices to resolve fast, but since we want to be able to treat variables as
/// global temporarily, we cannot just reference a single slice. Instead, a trait object to access
/// globals is provided when creating a context.
///
/// Locals are a bit tricky because each local variable can have its own temporary lifetime, and
/// because creating a subcontext should not invalidate the parent context. So locals are managed
/// as a series of stack frames living on the Rust call stack, with parent pointers. As a
/// consequence, we need to iterate over frames when accessing locals by index.
pub struct ParamContextImpl<ParamType, GlobalsType: VarAccessor<ParamType> + Copy> {
    pub globals: GlobalsType,
    locals: LocalContextStack<ParamType>,
    locals_start: VarIndex,
}

impl<ParamType, GlobalsType: VarAccessor<ParamType> + Copy>
    ParamContextImpl<ParamType, GlobalsType>
{
    pub fn new(globals: GlobalsType) -> Self {
        ParamContextImpl {
            globals,
            locals: LocalContextStack::Root,
            locals_start: 0,
        }
    }
}

impl<ParamType, GlobalsType: VarAccessor<ParamType> + Copy> Context
    for ParamContextImpl<ParamType, GlobalsType>
{
    fn locals_start(&self) -> VarIndex {
        self.locals_start
    }
}

impl<ParamType, GlobalsType: VarAccessor<ParamType> + Copy> ParamContext<ParamType>
    for ParamContextImpl<ParamType, GlobalsType>
{
    fn with_local<R>(&self, param: &ParamType, f: impl FnOnce(&Self) -> R) -> R {
        let local_ctx = ParamContextImpl {
            globals: self.globals,
            locals: LocalContextStack::Params {
                params: param,
                params_len: 1,
                parent: &self.locals,
            },
            locals_start: self.locals_start - 1,
        };
        f(&local_ctx)
    }

    fn with_locals<R>(&self, params: &[ParamType], f: impl FnOnce(&Self) -> R) -> R {
        let params_len = params.len();
        if params_len > VarIndex::MAX as usize {
            // A little pedantic, but the unsafe block relies on it.
            panic!("too many params");
        }
        let local_ctx = ParamContextImpl {
            globals: self.globals,
            locals: LocalContextStack::Params {
                params: params.as_ptr(),
                params_len,
                parent: &self.locals,
            },
            locals_start: self.locals_start - (params_len as VarIndex),
        };
        f(&local_ctx)
    }
}

impl<ParamType, GlobalsType: VarAccessor<ParamType> + Copy> VarAccessor<ParamType>
    for ParamContextImpl<ParamType, GlobalsType>
{
    fn get_var(&self, mut idx: VarIndex) -> &ParamType {
        if idx < 0 {
            /* The recursive version is much nicer, but Rust has no tail recursion guarantee. */
            let mut locals = &self.locals;
            loop {
                match locals {
                    LocalContextStack::Root => panic!("invalid De Bruijn index"),
                    LocalContextStack::Params {
                        params,
                        params_len,
                        parent,
                    } => {
                        idx += *params_len as VarIndex;

                        // Safety:
                        // * The only way to create a new nonempty context is via `with_local` or
                        //   `with_locals`, and the only way to access that context is via the
                        //   closure argument of type `&Self`, which has a temporary lifetime.
                        //   Therefore, we can rely on being inside the closure, so that the borrows
                        //   of `with_local`/`with_locals`, where the pointers originated from, are
                        //   still in scope.
                        // * The reference returned by `get_var` cannot escape the closure because
                        //   its lifetime is restricted to the temporary lifetime of the closure
                        //   argument.
                        // * `idx` is guaranteed to be < `params_len`, as it was previously < 0.
                        //
                        // It would be nice if we could implement everything in safe Rust instead,
                        // but it seems that the `ParamContext` trait cannot be defined in a way
                        // that would allow this, except by cloning the argument to `with_local`
                        // (which would be quite expensive both in time and in stack space). The
                        // problem is that there does not seem to be an obvious way to parameterize
                        // the closure argument with the lifetimes of `self` and `param`: its type
                        // needs to be something similar to `&Self`, but currently there is no such
                        // thing as "Self but with different lifetimes".
                        unsafe {
                            if idx >= 0 {
                                return &*params.offset(idx);
                            }
                            locals = &**parent;
                        }
                    }
                }
            }
        } else {
            self.globals.get_var(idx)
        }
    }

    fn for_each_var<R>(&self, mut f: impl FnMut(VarIndex, &ParamType) -> Option<R>) -> Option<R> {
        let mut locals = &self.locals;
        let mut idx: VarIndex = 0;
        loop {
            match locals {
                LocalContextStack::Root => break,
                LocalContextStack::Params {
                    params,
                    params_len,
                    parent,
                } => {
                    // Safety: see above.
                    unsafe {
                        let mut param_idx = *params_len;
                        while param_idx > 0 {
                            idx -= 1;
                            param_idx -= 1;
                            let param = &*params.add(param_idx);
                            let result = f(idx, param);
                            if result.is_some() {
                                return result;
                            }
                        }
                        locals = &**parent;
                    }
                }
            }
        }

        self.globals.for_each_var(f)
    }
}

pub trait NamedObject {
    fn get_name(&self) -> Option<&str>;
}

pub trait NamedVarAccessor<ParamType: NamedObject>: VarAccessor<ParamType> {
    fn get_var_index(&self, name: &str, occurrence: usize) -> Option<VarIndex>;
    fn get_name_occurrence(&self, idx: VarIndex, param: &ParamType) -> usize;
}

impl<ParamType: NamedObject, T: VarAccessor<ParamType> + ?Sized> NamedVarAccessor<ParamType> for T {
    fn get_var_index(&self, name: &str, mut occurrence: usize) -> Option<VarIndex> {
        self.for_each_var(|idx, param| {
            if param.get_name() == Some(name) {
                if occurrence == 0 {
                    return Some(idx);
                }
                occurrence -= 1;
            }
            None
        })
    }

    fn get_name_occurrence(&self, idx: VarIndex, idx_param: &ParamType) -> usize {
        let name = idx_param.get_name();
        let mut occurrence = 0;
        self.for_each_var(|iter_idx, param| {
            if iter_idx == idx {
                return Some(occurrence);
            }
            if param.get_name() == name {
                occurrence += 1;
            }
            None
        })
        .unwrap()
    }
}
