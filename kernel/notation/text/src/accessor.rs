use std::marker::PhantomData;

pub trait Accessor<Parent, Child> {
    fn access(parent: &Parent) -> &Child;
}

pub trait AccessorMut<Parent, Child>: Accessor<Parent, Child> {
    fn access_mut(parent: &mut Parent) -> &mut Child;
}

pub struct IdAccessor;

impl<T> Accessor<T, T> for IdAccessor {
    fn access(parent: &T) -> &T {
        parent
    }
}

impl<T> AccessorMut<T, T> for IdAccessor {
    fn access_mut(parent: &mut T) -> &mut T {
        parent
    }
}

pub struct ComposedAccessor<Fst, T2, Snd>(Fst, PhantomData<T2>, Snd);

impl<T1, T2: 'static, T3, Fst: Accessor<T1, T2>, Snd: Accessor<T2, T3>> Accessor<T1, T3>
    for ComposedAccessor<Fst, T2, Snd>
{
    fn access(parent: &T1) -> &T3 {
        Snd::access(Fst::access(parent))
    }
}

impl<T1, T2: 'static, T3, Fst: AccessorMut<T1, T2>, Snd: AccessorMut<T2, T3>> AccessorMut<T1, T3>
    for ComposedAccessor<Fst, T2, Snd>
{
    fn access_mut(parent: &mut T1) -> &mut T3 {
        Snd::access_mut(Fst::access_mut(parent))
    }
}

pub struct TupleFstAccessor;
pub struct TupleSndAccessor;

impl<Fst, Snd> Accessor<(Fst, Snd), Fst> for TupleFstAccessor {
    fn access(parent: &(Fst, Snd)) -> &Fst {
        &parent.0
    }
}

impl<Fst, Snd> AccessorMut<(Fst, Snd), Fst> for TupleFstAccessor {
    fn access_mut(parent: &mut (Fst, Snd)) -> &mut Fst {
        &mut parent.0
    }
}

impl<Fst, Snd> Accessor<(Fst, Snd), Snd> for TupleSndAccessor {
    fn access(parent: &(Fst, Snd)) -> &Snd {
        &parent.1
    }
}

impl<Fst, Snd> AccessorMut<(Fst, Snd), Snd> for TupleSndAccessor {
    fn access_mut(parent: &mut (Fst, Snd)) -> &mut Snd {
        &mut parent.1
    }
}
