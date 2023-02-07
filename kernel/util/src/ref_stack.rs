use std::ptr::null;

/// A cheap stack data structure that lives on the Rust call stack, in the form of frames that
/// point to their parent frame. "Pushing" to the stack does not modify the stack but creates a new
/// frame, i.e. a new stack that includes the original one.
///
/// The items on the stack are references with arbitrary lifetimes. However, no lifetime parameters
/// are required on the stack itself, a property that is especially useful when each individual item
/// may have a different lifetime originally. To ensure the validity of references on the stack,
/// each stack that is created by pushing an item can only be used temporarily while the original
/// reference to that item is still in scope.
///
/// The stack can be queried by iterating over it, which happens in reverse order compared to push
/// operations.
/// To improve iteration performance, references to slices can be pushed as a single frame, instead
/// of pushing each item individually.
pub struct RefStack<Item, ExtraData: Copy = ()> {
    // Null if this is the root; in that case `items` is also guaranteed to be null.
    parent: *const RefStack<Item, ExtraData>,
    len: usize,

    items: *const Item,
    items_len: usize,

    // User-provided data per stack frame. Since newly created stack frames are only available in
    // borrowed form, users cannot include them inside larger objects; they have to store the
    // references instead, requiring a lifetime parameter. By including additional data in each
    // frame, the reference to a frame can be used to query that additional data without such
    // additional complexity.
    extra_data: ExtraData,
}

impl<Item, ExtraData: Copy> RefStack<Item, ExtraData> {
    pub fn new(extra_data: ExtraData) -> Self {
        RefStack {
            parent: null(),
            len: 0,
            items: null(),
            items_len: 0,
            extra_data,
        }
    }

    /// Temporarily creates a new stack with `item` pushed to it, and calls `f` with this stack.
    pub fn with_item<R>(&self, item: &Item, f: impl FnOnce(&Self) -> R) -> R {
        let new_stack = RefStack {
            parent: self,
            len: self.len + 1,
            items: item,
            items_len: 1,
            extra_data: self.extra_data,
        };

        // Note: for safety, it is important that neither ownership nor a reference to `new_stack`
        // escapes this method.
        f(&new_stack)
    }

    /// Temporarily creates a new stack with `items` pushed to it, and calls `f` with this stack.
    pub fn with_items<R>(&self, items: &[Item], f: impl FnOnce(&Self) -> R) -> R {
        let items_len = items.len();
        let new_stack = RefStack {
            parent: self,
            len: self.len + items_len,
            items: items.as_ptr(),
            items_len,
            extra_data: self.extra_data,
        };

        // Note: for safety, it is important that neither ownership nor a reference to `new_stack`
        // escapes this method.
        f(&new_stack)
    }

    /// Temporarily creates a new stack that contains the same items but its own copy of
    /// `extra_data`, and calls `f` with this stack.
    pub fn with_new_extra_data<R>(&self, extra_data: ExtraData, f: impl FnOnce(&Self) -> R) -> R {
        let new_stack = RefStack {
            parent: self,
            len: self.len,
            items: null(),
            items_len: 0,
            extra_data,
        };

        // Note: for safety, it is important that neither ownership nor a reference to `new_stack`
        // escapes this method.
        f(&new_stack)
    }

    pub fn len(&self) -> usize {
        self.len
    }

    /// Iterates over the items on the stack, with the most-recently-pushed item returned first.
    pub fn iter<'a>(&'a self) -> RefStackIter<'a, Item, ExtraData> {
        RefStackIter {
            frame: self,
            item_idx: self.items_len,
        }
    }

    pub fn extra_data(&self) -> &ExtraData {
        &self.extra_data
    }
}

impl<'a, Item, ExtraData: Copy> IntoIterator for &'a RefStack<Item, ExtraData> {
    type Item = &'a Item;
    type IntoIter = RefStackIter<'a, Item, ExtraData>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct RefStackIter<'a, Item, ExtraData: Copy = ()> {
    frame: &'a RefStack<Item, ExtraData>,
    item_idx: usize,
}

impl<'a, Item, ExtraData: Copy> Iterator for RefStackIter<'a, Item, ExtraData> {
    type Item = &'a Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.nth(0)
    }

    fn nth(&mut self, mut n: usize) -> Option<Self::Item> {
        while !self.frame.parent.is_null() {
            if n < self.item_idx {
                self.item_idx -= n + 1;
                debug_assert!(self.item_idx < self.frame.items_len);

                // SAFETY:
                // * The only way to create a new nonempty stack is via `with_item` or `with_items`,
                //   and the only way to access that stack is via the closure argument of type
                //   `&Self`, which has a temporary lifetime, and of course the iterator inherits
                //   that lifetime.
                //   Therefore, we can rely on being inside the closure, so that the reference
                //   passed to `with_item`/`with_items`, which the pointer originated from, is
                //   still in scope.
                // * The reference we return cannot escape the closure because its lifetime is the
                //   same as the temporary lifetime of the closure argument.
                // * `item_idx` is guaranteed to be < `items_len`, as it is always initialized to
                //   `items_len` and we just decreased it by at least 1.
                unsafe {
                    let item = self.frame.items.add(self.item_idx);
                    return Some(&*item);
                }
            } else {
                n -= self.item_idx;

                // SAFETY:
                // * For reasons analogous to above, the parent frame is still in scope.
                // * The loop condition checked whether it was null.
                unsafe {
                    self.frame = &*self.frame.parent;
                }

                self.item_idx = self.frame.items_len;
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.frame.len - self.frame.items_len + self.item_idx;
        (remaining, Some(remaining))
    }
}

// SAFETY:
// * Only an empty context can ever be owned.
// * As long as a reference to a context is valid, we can safely share it between threads.
unsafe impl<Item, ExtraData: Copy + Send> Send for RefStack<Item, ExtraData> {}
unsafe impl<Item: Sync, ExtraData: Copy + Sync> Sync for RefStack<Item, ExtraData> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_stack_is_empty() {
        let stack = RefStack::<()>::new(());
        assert!(stack.iter().next().is_none());
    }

    #[test]
    fn single_item_is_returned() {
        let stack = RefStack::<u32>::new(());
        stack.with_item(&1, |stack2| {
            assert!(stack.iter().next().is_none());
            assert_eq!(stack2.iter().collect::<Vec<&u32>>(), [&1]);
        });
    }

    #[test]
    fn two_items_are_returned() {
        let stack = RefStack::<u32>::new(());
        stack.with_item(&1, |stack2| {
            stack2.with_item(&2, |stack3| {
                assert!(stack.iter().next().is_none());
                assert_eq!(stack2.iter().next(), Some(&1));
                assert!(stack2.iter().nth(1).is_none());
                assert!(stack2.iter().nth(2).is_none());
                assert_eq!(stack3.iter().skip(1).collect::<Vec<&u32>>(), [&1]);
                assert_eq!(stack3.iter().collect::<Vec<&u32>>(), [&2, &1]);
            });
        });
    }

    #[test]
    fn slice_is_returned_in_reverse() {
        let stack = RefStack::<u32>::new(());
        stack.with_items(&[1, 2], |stack2| {
            assert_eq!(stack2.iter().collect::<Vec<&u32>>(), [&2, &1]);
            assert_eq!(stack2.iter().next(), Some(&2));
            assert_eq!(stack2.iter().nth(1), Some(&1));
            assert!(stack2.iter().nth(2).is_none());
        });
    }

    #[test]
    fn two_slices_are_returned() {
        let stack = RefStack::<u32>::new(());
        stack.with_items(&[1, 2], |stack2| {
            stack2.with_items(&[3, 4, 5], |stack3| {
                assert_eq!(stack3.iter().collect::<Vec<&u32>>(), [&5, &4, &3, &2, &1]);
                assert_eq!(stack3.iter().next(), Some(&5));
                assert_eq!(stack3.iter().nth(3), Some(&2));
                assert_eq!(stack3.iter().nth(4), Some(&1));
                assert!(stack3.iter().nth(5).is_none());
            });
        });
    }

    #[test]
    fn stack_with_empty_slice_is_empty() {
        let stack = RefStack::<u32>::new(());
        stack.with_items(&[], |stack2| {
            assert!(stack2.iter().next().is_none());
        });
    }

    #[test]
    #[cfg(feature = "test_lifetime")] // Uncomment to see compiler error.
    fn item_ref_cannot_escape() {
        let stack = RefStack::<u32>::new(());
        stack.with_item(&42, |stack2| stack2.iter().next());
    }

    #[test]
    fn copied_item_can_be_returned() {
        let stack = RefStack::<u32>::new(());
        let result = stack.with_item(&42, |stack2| *stack2.iter().next().unwrap());
        assert_eq!(result, 42);
    }
}
