use {
    crate::CircularList,
    alloc::boxed::Box,
    core::{cell::UnsafeCell, ptr},
};

pub mod cursor;

struct Pointers<T> {
    next: *mut ListHead<T>,
    prev: *mut ListHead<T>,
}
impl<T> Default for Pointers<T> {
    fn default() -> Self {
        Self {
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
        }
    }
}
impl<T> Pointers<T> {
    fn set(&mut self, next: *mut ListHead<T>, prev: *mut ListHead<T>) {
        self.next = next;
        self.prev = prev;
    }
    fn set_both(&mut self, link: *mut ListHead<T>) {
        self.next = link;
        self.prev = link;
    }
    fn set_next(&mut self, link: *mut ListHead<T>) {
        self.next = link;
    }
    fn set_prev(&mut self, link: *mut ListHead<T>) {
        self.prev = link;
    }
}

/// List element for a doubly linked list.
pub struct ListHead<T> {
    pointers: UnsafeCell<Pointers<T>>,
    value: T,
}

/// The present implementation aims to preserve the following invariant (3):
/// * The `next` and `prev` pointers are always valid
/// * Following the `next` field recursively must always end up to the original `Self`
/// * Following the `prev` field recursively must give the exact reverse path as the `next` one
impl<T> ListHead<T> {
    /// Creates a new element with value `val`.
    /// The created element is its own previous and next element.
    /// # Layout
    /// ```text
    /// ┌───┐
    /// │   │
    /// │ ┌─▼──┐
    /// └─┤val ├─┐
    ///   └──▲─┘ │
    ///      │   │
    ///      └───┘
    /// ```
    pub fn new(val: T) -> *mut Self {
        let mut new = Box::new(Self {
            pointers: Default::default(),
            value: val,
        });

        // Preserving invariant (3)
        unsafe {
            let ptr = &raw mut *new;
            new.pointers_mut().set_both(ptr);
        }

        Box::into_raw(new)
    }

    unsafe fn pointers(&self) -> &Pointers<T> {
        unsafe { &*self.pointers.get() }
    }

    unsafe fn pointers_mut<'a>(&self) -> &'a mut Pointers<T> {
        unsafe { &mut *self.pointers.get() }
    }

    pub fn next(&self) -> &Self {
        unsafe { &*self.pointers().next }
    }

    /// Gets a mutable pointer to the next element.
    pub fn next_mut_ptr(&self) -> *mut Self {
        unsafe { self.pointers_mut().next }
    }

    pub fn next_ptr(&self) -> *const Self {
        unsafe { self.pointers().next }
    }

    /// Gets a pointer to the previous element.
    pub fn prev_mut_ptr(&self) -> *mut Self {
        unsafe { self.pointers_mut().prev }
    }

    /// Gets a pointer to the previous element.
    pub fn prev_ptr(&self) -> *const Self {
        unsafe { self.pointers().prev }
    }

    /// Gets a shared reference to the value of the list head.
    pub fn value(&self) -> &T {
        &self.value
    }

    /// Gets an exclusive reference to the value of the list head.
    pub fn value_mut(&mut self) -> &mut T {
        &mut self.value
    }

    /// Inserts `new` between `prev` and `next`.
    ///
    /// # Sketch
    /// ```text
    /// ┌────┬──►┌────┬──►┌────┐
    /// │prev│   │new │   │next│
    /// └────┘◄──┴────┘◄──┴────┘
    /// ```
    ///
    /// # Safety
    /// * `next`, `new` and `prev` must be valid pointers
    /// * `next` should be the next of `prev` and `prev` should be the
    ///   previous of `next`
    /// * `new` must be disconnected from its old place (i.e. with
    ///   `__del` or `__replace`) before calling this function otherwise it
    ///   would break [`INVARIANT_3`](`crate::invariants::INVARIANT_3`).
    unsafe fn __add(new: *mut Self, prev: *mut Self, next: *mut Self) {
        if prev == next {
            unsafe {
                // SAFETY: See the caller contract.
                (*next).pointers_mut().set_both(new);
            }
        } else {
            unsafe {
                // SAFETY: See the caller contract.
                (*next).pointers_mut().set_prev(new);
                (*prev).pointers_mut().set_next(new);
            }
        }
        unsafe {
            // SAFETY: See the caller contract.
            (*new).pointers_mut().set(next, prev);
        }
    }

    /// Disconnects element(s) by connecting the previous and next elements
    /// together.
    ///
    /// # Sketch
    /// ```text
    ///      ┌────┬──┐
    ///      │list│  │
    ///  ┌───┴────┘  │
    /// ┌▼───┬──►┌───▼┐
    /// │prev│   │next│
    /// └────┘◄──┴────┘
    /// ```
    /// # Safety
    /// * `next` and `prev` must be valid pointers.
    /// * the element(s) between `next` and `prev` must be dropped or
    ///   connected somewhere else after calling this function in order to
    ///   preserve [`INVARIANT_3`](`crate::invariants::INVARIANT_3`).
    unsafe fn __del(prev: *mut Self, next: *mut Self) {
        unsafe {
            // SAFETY: See the caller contract.
            (*next).pointers_mut().set_prev(prev);
            (*prev).pointers_mut().set_next(next);
        }
    }

    /// Disconnects an element from the list then returns its value and a pointer to the
    /// next element. The `ListHead` is dropped in the process.
    ///
    /// # Safety
    /// `to_del` must be a valid pointer to a `ListHead` with valid pointers to its next
    /// and previous elements.
    pub unsafe fn del_entry(to_del: *mut Self) -> (*mut Self, T) {
        unsafe {
            // `to_del.prev` and `to_del.next` should be valid according to invariant (3).
            let prev = (*to_del).prev_mut_ptr();
            let next = (*to_del).next_mut_ptr();

            Self::__del(prev, next);

            // SAFETY `to_del` is valid as promised by the caller.
            // `to_del` has to be dropped in order to preserve invariant (3).
            let to_del = Box::from_raw(to_del);

            (next, to_del.value)
        }
    }

    /// Inserts an element before this one.
    ///
    /// # Safety
    /// `new` must be a valid pointer to a `ListHead` a must not be connected to other `ListHead`s.
    /// `this` must be a valid pointer to a `ListHead`.
    pub unsafe fn add(this: *mut Self, new: *mut Self) {
        unsafe {
            // SAFETY: `this` is is a valid pointer as claimed by the caller.
            // The caller promises us that `new` is valid.
            // As for the `prev` parameter, it is the same as `this` or
            // another valid pointer according to invariant (3).
            Self::__add(new, (*this).prev_mut_ptr(), this);
        }
    }

    /// Inserts an element after this one.
    ///
    /// # Safety
    /// `new` must be a valid pointer to a `ListHead` a must not be connected to other `ListHead`s.
    pub unsafe fn add_after(this: *mut Self, new: *mut Self) {
        unsafe {
            // SAFETY: `this` is claimed to be valid by the caller.
            // The caller promises us that `new` is valid.
            // As for the `prev` parameter, it is the same as `self` or
            // another valid pointer according to invariant (3).
            Self::__add(new, this, (*this).next_mut_ptr());
        }
    }

    /// Connects `new` in place of `old` in the list.
    ///
    /// # Sketch
    ///
    /// ## Before
    /// ```text
    ///     ┌────┬──►?
    ///     │new │
    /// ?◄──┴────┘
    /// ┌────┬──►┌────┬──►┌────┐
    /// │prev│   │old │   │next│
    /// └────┘◄──┴────┘◄──┴────┘
    /// ```
    ///
    /// ## After
    /// ```text
    /// ┌───────►┌────┬───────┐
    /// │        │new │       │
    /// │   ┌────┴────┘◄──┐   │
    /// │   │             │   │
    /// ├───▼┐   ┌────┬──►├───▼┐
    /// │prev│   │old │   │next│
    /// └────┘◄──┴────┘   └────┘
    /// ```
    ///
    /// # Safety
    /// * `old` and `new` must be valid pointers
    /// * `old` has to be dropped or connected somewhere else after calling this function in
    ///   order to preserve [`INVARIANT_3`](`crate::invariants::INVARIANT_3`).
    unsafe fn __replace(old: *mut Self, new: *mut Self) {
        if old == new {
            return;
        }
        unsafe {
            // SAFETY: The caller garantee that `old` and
            // `new` are valid pointers and that `old` will
            // be dropped or connected somewhere else.
            (*(*old).next_mut_ptr()).pointers_mut().set_prev(new);
            (*(*old).prev_mut_ptr()).pointers_mut().set_next(new);
            (*new)
                .pointers_mut()
                .set((*old).next_mut_ptr(), (*old).prev_mut_ptr());
            (*old).pointers_mut().set_both(ptr::null_mut());
        }
    }

    /// Exchanges 2 elements by interchanging their connection to their list (which could be not
    /// the same).
    ///
    /// # Safety
    /// `entry1` and `entry2` must be valid pointers to valid circular linked lists.
    pub unsafe fn swap(entry1: *mut Self, entry2: *mut Self) {
        unsafe {
            // `entry2` is valid as promised by the caller.
            // `(*entry2).prev` and `(*entry2).next` should be valid according to invariant (3)
            let mut pos = (*entry2).prev_mut_ptr();
            Self::__del(pos, (*entry2).next_mut_ptr());

            // `entry1` is valid as promised by the caller.
            // `entry2` is connected in place of `entry1` which preserve invariant (3).
            Self::__replace(entry1, entry2);

            // in case `entry1` was already behind `entry2`, it is place next to it.
            if pos == entry1 {
                pos = entry2;
            }

            // `pos` and `(*pos).next` are valid according to invariant (3) and `entry1` was just
            // disconnected from its old place.
            Self::__add(entry1, pos, (*pos).next_mut_ptr());
        }
    }

    /// Moves out `entry` and inserts it between `prev` and `next`.
    ///
    /// # Safety
    /// The caller must give valid pointers and make sure `next` is the next element of `prev`
    /// otherwise there could be memory leaks.
    pub unsafe fn move_entry(entry: *mut Self, prev: *mut Self, next: *mut Self) {
        unsafe {
            // `(*entry).prev` and `(*entry).next` should be valid according to invariant (3)
            Self::__del((*entry).prev_mut_ptr(), (*entry).next_mut_ptr());
            // We know `entry` is valid and `next` and `prev` are consecutive (because of course the
            // caller is cautious)
            Self::__add(entry, prev, next);
        }
    }

    /// Insert `list` before `next`.
    ///
    /// # Safety
    /// * `list` must be a valid pointer and be part of a valid circular list
    /// * Idem for `next`
    /// * `list` **must not** be an element of the same circular list as `next` without defining a
    ///   new head for the orphaned list, otherwise it would cause a memory leak.
    pub unsafe fn add_list(list: *mut Self, next: *mut Self) {
        unsafe {
            // `last_of_list` should be valid according to invariant (3)
            let last_of_list = (*list).prev_mut_ptr();
            // idem
            let prev = (*next).prev_mut_ptr();

            // Preserving invariant (3): as soon as `list` is part of a valid circular list as well as
            // `next`, the connections made here will create 1 or 2 valid circular list(s).

            // The end of `list` is connected to `next`
            Self::__del(last_of_list, next);

            // The beginning of `list` is connected to the element before `next`
            Self::__del(prev, list);
        }
    }

    /// Cuts a circular list in two parts.
    ///
    /// # Safety
    /// * `head` and `new_head` must be valid pointers
    /// * `new_head` **must** be the head of a newly created `CircularList` after the call
    pub unsafe fn split(head: *mut Self, new_head: *mut Self) {
        unsafe {
            // The last element of the list where `new_head` is the head.
            let new_tail = (*head).prev_mut_ptr();

            // close the list where `head` is the head
            Self::__del((*new_head).prev_mut_ptr(), head);

            // close the list where `new_head` is the head
            Self::__del(new_tail, new_head);
        }
    }

    pub unsafe fn into_value(this: *mut Self) -> T {
        let this = unsafe { Box::from_raw(this) };
        this.value
    }
}

/// Circular list iterator.
pub struct Iter<'life, T> {
    _list: &'life CircularList<T>,
    next: *const ListHead<T>,
}
impl<'life, T> Iterator for Iter<'life, T> {
    type Item = &'life T;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: the lifetime `'life` of `self` is bound to the lifetime of the list. We
        // return a `'life` shared reference to the current value which is bound to the list.
        // Plus, the list is circular so next should always be non null if the list is non empty.
        let (current, next) = unsafe {
            let r = &*self.next;
            (r.value(), r.next())
        };
        self.next = next;
        Some(current)
    }
}
impl<'life, T> Iter<'life, T> {
    pub fn new(list: &'life CircularList<T>) -> Self {
        let first = list.head;
        Self {
            _list: list,
            next: first,
        }
    }
}

/// Circular list iterator with mutability.
pub struct IterMut<'life, T> {
    _list: &'life mut CircularList<T>,
    next: *mut ListHead<T>,
}
impl<'life, T> Iterator for IterMut<'life, T> {
    type Item = &'life mut T;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: the lifetime `'life` of `self` is bound to the lifetime of the list. We
        // return a `'life` shared reference to the current value which is bound to the list.
        // Plus, the list is circular so next should always be non null if the list is non empty.
        let (current, next) = unsafe {
            let r = &mut *self.next;
            let next = r.next_mut_ptr();
            (r.value_mut(), next)
        };
        self.next = next;
        Some(current)
    }
}
impl<'life, T> IterMut<'life, T> {
    pub fn new(list: &'life mut CircularList<T>) -> Self {
        let first = list.head as *mut _;
        Self {
            _list: list,
            next: first,
        }
    }
}

impl<T: PartialEq> PartialEq for ListHead<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
    }
}

impl<T: PartialOrd> PartialOrd for ListHead<T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.value.partial_cmp(&other.value)
    }
}
