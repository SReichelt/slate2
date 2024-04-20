//! A helper data structure that can be used to implement structures with "bookmarks", which act as
//! references into the structure that can be kept across mutations. The main use case is a text
//! rope implementation, where bookmarks can be placed at arbitrary locations in the text and will
//! then be tracked across text modifications.
//!
//! The containing data structure is responsible for actually storing the bookmarks, as the most
//! performant way of storing them may depend on the specifics of that data structure. As a result,
//! the bookmark helper data structure has an unsafe interface, but its safety requirements are
//! easily satisfied by the containing data structure, which can then offer a safe interface to its
//! clients.
//!
//! The helper structure is split into `BookmarkRoot`, which represents the location where data
//! is stored, and `BookmarkAccess`, which exclusively borrows `BookmarkRoot`, with the intention
//! that `BookmarkAccess` exists for essentially the entire lifetime of the `BookmarkRoot`.
//! Consequently, the containing data structure must be split in the same manner. The client of the
//! containing data structure can then keep bookmark references along with the "access" object
//! because both share the same lifetime parameter.
//!
//! A usage example called `StackWithBookmarks` is given inside the test code below.

use std::{
    cell::UnsafeCell,
    marker::{PhantomData, PhantomPinned},
    pin::Pin,
    ptr::NonNull,
};

// Dummy field required for unique address; see `BookmarkAccess::contains_bookmark_impl`.
#[allow(dead_code)]
pub struct BookmarkRoot(u8);

impl BookmarkRoot {
    pub fn new() -> Self {
        BookmarkRoot(0)
    }

    pub fn access<'a>(&'a mut self) -> BookmarkAccess<'a> {
        BookmarkAccess(self)
    }
}

pub struct BookmarkAccess<'a>(&'a mut BookmarkRoot);

impl<'a> BookmarkAccess<'a> {
    /// Creates a bookmark along with a reference to it.
    ///
    /// # Safety
    ///
    /// The caller must not drop the bookmark before the end of the lifetime `'a`, except by calling
    /// `destroy_bookmark`. This can be achieved by storing the bookmark in the same object as the
    /// bookmark root and making sure that it cannot be moved out.
    pub unsafe fn create_bookmark<M>(&self, data: M) -> (Bookmark<M>, BookmarkRef<'a, M>) {
        let bookmark_data = Box::pin(BookmarkData {
            root: NonNull::from(self.0 as &BookmarkRoot),
            data: UnsafeCell::new(data),
            _pin: PhantomPinned,
        });
        let bookmark_ref = BookmarkRef {
            _phantom_root: PhantomData,
            bookmark: NonNull::from(&*bookmark_data),
        };
        (Bookmark(bookmark_data), bookmark_ref)
    }

    /// Destroys a bookmark along with its corresponding reference.
    ///
    /// # Panics
    ///
    /// Panics if the reference does not correspond to the given bookmark.
    pub fn destroy_bookmark<M>(&self, bookmark: Bookmark<M>, bookmark_ref: BookmarkRef<'a, M>) {
        assert!(bookmark_ref.references(&bookmark));
        // There isn't really anything to do besides checking for consistency. After consuming the
        // bookmark reference, we know the bookmark can be dropped safely.
    }

    pub fn bookmark_data<M>(&self, bookmark: &Bookmark<M>) -> &M {
        // SAFETY: We require the caller of `create_bookmark` not to drop the bookmark.
        unsafe { self.bookmark_data_impl(NonNull::from(&*bookmark.0)) }
    }

    pub fn bookmark_data_mut<M>(&mut self, bookmark: &Bookmark<M>) -> &mut M {
        // SAFETY: We require the caller of `create_bookmark` not to drop the bookmark.
        unsafe { self.bookmark_data_mut_impl(NonNull::from(&*bookmark.0)) }
    }

    pub fn bookmark_ref_data<M>(&self, bookmark_ref: &BookmarkRef<'a, M>) -> &M {
        // SAFETY: We require the caller of `create_bookmark` not to drop the bookmark.
        unsafe { self.bookmark_data_impl(bookmark_ref.bookmark) }
    }

    pub fn bookmark_ref_data_mut<M>(&mut self, bookmark_ref: &BookmarkRef<'a, M>) -> &mut M {
        // SAFETY: We require the caller of `create_bookmark` not to drop the bookmark.
        unsafe { self.bookmark_data_mut_impl(bookmark_ref.bookmark) }
    }

    unsafe fn contains_bookmark_impl<M>(&self, bookmark_data: NonNull<BookmarkData<M>>) -> bool {
        (*bookmark_data.as_ptr()).root == NonNull::from(self.0 as &BookmarkRoot)
    }

    unsafe fn bookmark_data_impl<M>(&self, bookmark_data: NonNull<BookmarkData<M>>) -> &M {
        assert!(self.contains_bookmark_impl(bookmark_data));
        // SAFETY: Bookmark data can only be accessed via `BookmarkAccess`, which can only exist
        // once for a given `BookmarkRoot`. Therefore, if `self` is borrowed for the returned
        // lifetime, the returned reference is guaranteed to stay valid for that lifetime.
        &*bookmark_data.as_ref().data.get()
    }

    unsafe fn bookmark_data_mut_impl<M>(
        &mut self,
        bookmark_data: NonNull<BookmarkData<M>>,
    ) -> &mut M {
        assert!(self.contains_bookmark_impl(bookmark_data));
        // SAFETY: Bookmark data can only be accessed via `BookmarkAccess`, which can only exist
        // once for a given `BookmarkRoot`. Therefore, if `self` is borrowed for the returned
        // lifetime, the returned reference is guaranteed to stay valid for that lifetime.
        &mut *bookmark_data.as_ref().data.get()
    }
}

pub struct Bookmark<M>(Pin<Box<BookmarkData<M>>>);

struct BookmarkData<M> {
    root: NonNull<BookmarkRoot>,
    data: UnsafeCell<M>,
    _pin: PhantomPinned,
}

pub struct BookmarkRef<'a, M> {
    _phantom_root: PhantomData<&'a BookmarkRoot>,
    bookmark: NonNull<BookmarkData<M>>,
}

impl<'a, M> BookmarkRef<'a, M> {
    pub fn belongs_to(&self, root_access: &BookmarkAccess<'a>) -> bool {
        // SAFETY: We require the caller of `create_bookmark` not to drop the bookmark.
        unsafe { root_access.contains_bookmark_impl(self.bookmark) }
    }

    pub fn references(&self, bookmark: &Bookmark<M>) -> bool {
        self.bookmark.as_ptr().cast_const() == &*bookmark.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_create_and_destroy_bookmark() {
        let mut root = BookmarkRoot::new();
        let mut access = root.access();

        let (bookmark, bookmark_ref) = unsafe { access.create_bookmark(42) };
        assert!(bookmark_ref.belongs_to(&access));
        assert!(bookmark_ref.references(&bookmark));

        assert_eq!(*access.bookmark_ref_data(&bookmark_ref), 42);
        *access.bookmark_data_mut(&bookmark) = 23;
        assert_eq!(*access.bookmark_ref_data(&bookmark_ref), 23);

        access.destroy_bookmark(bookmark, bookmark_ref);
    }

    /// An example data structure with bookmarks.
    /// The actual data is simply a stack of arbitrary objects, and each bookmark references a
    /// location somewhere in the stack, including directly after the last element. When an object
    /// is popped from the stack, all bookmarks that previously pointed after this element are
    /// updated to point to the new end of the stack.
    pub struct StackWithBookmarks<T> {
        stack: Vec<T>,
        bookmark_root: BookmarkRoot,
        bookmarks: Vec<Bookmark<usize>>,
    }

    impl<T> StackWithBookmarks<T> {
        pub fn new() -> Self {
            StackWithBookmarks {
                stack: Vec::new(),
                bookmark_root: BookmarkRoot::new(),
                bookmarks: Vec::new(),
            }
        }

        pub fn access<'a>(&'a mut self) -> StackWithBookmarksAccess<'a, T> {
            StackWithBookmarksAccess {
                stack: &mut self.stack,
                bookmark_access: self.bookmark_root.access(),
                bookmarks: &mut self.bookmarks,
            }
        }
    }

    pub struct StackWithBookmarksAccess<'a, T> {
        stack: &'a mut Vec<T>,
        bookmark_access: BookmarkAccess<'a>,
        bookmarks: &'a mut Vec<Bookmark<usize>>,
    }

    impl<'a, T> StackWithBookmarksAccess<'a, T> {
        pub fn push(&mut self, obj: T) {
            self.stack.push(obj);
        }

        pub fn pop(&mut self) -> Option<T> {
            let obj = self.stack.pop();
            if obj.is_some() {
                let new_len = self.stack.len();
                for bookmark in self.bookmarks.iter() {
                    let idx = self.bookmark_access.bookmark_data_mut(bookmark);
                    if *idx > new_len {
                        *idx = new_len;
                    }
                }
            }
            obj
        }

        pub fn create_bookmark(&mut self) -> StackBookmarkRef<'a> {
            // SAFETY: We store the returned bookmark in `self.bookmarks`, which we have borrowed
            // for `'a`. We only remove it in `destroy_bookmark`.
            let (bookmark, bookmark_ref) =
                unsafe { self.bookmark_access.create_bookmark(self.stack.len()) };
            self.bookmarks.push(bookmark);
            StackBookmarkRef(bookmark_ref)
        }

        pub fn destroy_bookmark(&mut self, bookmark_ref: StackBookmarkRef<'a>) {
            for (cur_bookmark_idx, cur_bookmark) in self.bookmarks.iter().enumerate() {
                if bookmark_ref.0.references(cur_bookmark) {
                    let cur_bookmark = self.bookmarks.remove(cur_bookmark_idx);
                    self.bookmark_access
                        .destroy_bookmark(cur_bookmark, bookmark_ref.0);
                    return;
                }
            }
            panic!("bookmark to destroy not found")
        }

        // Returns the object on the stack that directly follows the bookmark.
        pub fn read_bookmark(&self, bookmark_ref: &StackBookmarkRef<'a>) -> Option<&T> {
            let idx = *self.bookmark_access.bookmark_ref_data(&bookmark_ref.0);
            self.stack.get(idx)
        }
    }

    pub struct StackBookmarkRef<'a>(BookmarkRef<'a, usize>);

    #[test]
    fn can_keep_bookmarks_across_modification() {
        let mut stack = StackWithBookmarks::new();
        let mut stack_access = stack.access();

        // Modifications to the stack can be interleaved with creating bookmarks.
        let bookmark0 = stack_access.create_bookmark();
        assert_eq!(stack_access.read_bookmark(&bookmark0), None);
        stack_access.push(42);
        let bookmark1 = stack_access.create_bookmark();

        // `bookmark0` stays at the beginning of the stack, so reading it returns the first object
        // on the stack now.
        assert_eq!(stack_access.read_bookmark(&bookmark0), Some(&42));
        assert_eq!(stack_access.read_bookmark(&bookmark1), None);

        // Once we push another object, `bookmark1` will return it as well.
        stack_access.push(23);
        assert_eq!(stack_access.read_bookmark(&bookmark0), Some(&42));
        assert_eq!(stack_access.read_bookmark(&bookmark1), Some(&23));

        // Popping the last object again returns to the previous state.
        stack_access.pop();
        assert_eq!(stack_access.read_bookmark(&bookmark0), Some(&42));
        assert_eq!(stack_access.read_bookmark(&bookmark1), None);

        // After popping once more, the stack is empty. `bookmark1` has been updated now, but this
        // is not immediately visible.
        stack_access.pop();
        assert_eq!(stack_access.read_bookmark(&bookmark0), None);
        assert_eq!(stack_access.read_bookmark(&bookmark1), None);

        // Pushing a new object keeps the bookmarks at the same location, which is the start of the
        // stack for both bookmarks now. So reading them returns the new object in both cases.
        stack_access.push(123);
        assert_eq!(stack_access.read_bookmark(&bookmark0), Some(&123));
        assert_eq!(stack_access.read_bookmark(&bookmark1), Some(&123));

        // Check that we can safely destroy bookmarks.
        stack_access.destroy_bookmark(bookmark0);
        assert_eq!(stack_access.read_bookmark(&bookmark1), Some(&123));
        stack_access.destroy_bookmark(bookmark1);
    }
}
