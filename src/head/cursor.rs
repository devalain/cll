use {super::ListHead, crate::CircularList};

/// A `Cursor` is like an iterator, except that it can freely seek back-and-forth.
/// This `struct` is constructed by the [`CircularList::cursor`](crate::CircularList::cursor)
/// function.
#[derive(Clone, Copy)]
pub struct Cursor<'life, T> {
    list: &'life CircularList<T>,
    // Invariant (4): `current` is a valid pointer.
    current: *const ListHead<T>,
}

impl<'life, T> std::cmp::PartialEq for Cursor<'life, T> {
    fn eq(&self, other: &Self) -> bool {
        self.list.head == other.list.head && self.current == other.current
    }
}

impl<'life, T> Cursor<'life, T> {
    /// Builds a `Cursor` from a (valid) pointer to a `ListHead<T>`.
    /// # Panics
    /// This function panics if the list is empty.
    pub(crate) fn from_list(list: &'life CircularList<T>) -> Self {
        if list.is_empty() {
            // Preserving the invariant (4)
            panic!("Cannot build a `Cursor` from an empty list.");
        }
        Self {
            list,
            current: list.head,
        }
    }

    /// Returns to its initial position (the head of the list).
    pub fn reset(&mut self) {
        self.current = self.list.head;
    }

    /// Moves the cursor to the next element of the `CircularList`.
    pub fn move_next(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (4) assert that `self.current` is a valid pointer to
            // a valid circular linked list
            self.current = (*self.current).next;
        }
    }

    /// Moves the cursor to the previous element of the `CircularList`.
    pub fn move_prev(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (4) assert that `self.current` is a valid pointer to
            // a valid circular linked list
            self.current = (*self.current).prev;
        }
    }

    /// Returns the value of the list element behind the cursor.
    pub fn value(&self) -> &T {
        // SAFETY: Invariant (4) asserts that `current` is a valid pointer to a `ListHead<T>`.
        unsafe { &(*self.current).value }
    }
}

impl<'life, T: std::fmt::Debug> std::fmt::Debug for Cursor<'life, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value().fmt(f)
    }
}

impl<'life, T: std::fmt::Display> std::fmt::Display for Cursor<'life, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value().fmt(f)
    }
}

/// A `DoubleCursor` is a `struct` that points to 2 elements 'a' and 'b' of a [`CircularList`].
/// One can then [`swap`](`Self::swap`) the 2 elements or put the first after the second etc.
#[derive(Debug)]
pub struct DoubleCursor<'life, T> {
    list: &'life mut CircularList<T>,
    // Invariant (5): `a` and `b` are always valid pointers
    a: *const ListHead<T>,
    b: *const ListHead<T>,
    stack: Vec<*const ListHead<T>>,
}

impl<'life, T> DoubleCursor<'life, T> {
    /// Builds a `DoubleCursor` from a [`CircularList`].
    /// # Panics
    /// This function panics if the list is empty.
    pub(crate) fn from_list(list: &'life mut CircularList<T>) -> Self {
        if list.is_empty() {
            // Preserving the invariant (5)
            panic!("Cannot build a `DoubleCursor` from an empty list.");
        }
        let head = list.head;
        Self {
            list,
            a: head,
            b: head,
            stack: Vec::new(),
        }
    }

    /// Returns `true` if the 'a' cursor points to the same element as the 'b cursor.
    pub fn a_is_b(&self) -> bool {
        self.a == self.b
    }

    /// Moves the 'a' cursor to the next element of the `CircularList`.
    pub fn move_next_a(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (5) assert that `self.a` is a valid pointer to
            // a valid circular linked list
            self.a = (*self.a).next;
        }
    }

    /// Moves the 'b' cursor to the next element of the `CircularList`.
    pub fn move_next_b(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (5) assert that `self.b` is a valid pointer to
            // a valid circular linked list
            self.b = (*self.b).next;
        }
    }

    /// Moves the 'a' cursor to the previous element of the `CircularList`.
    pub fn move_prev_a(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (5) assert that `self.a` is a valid pointer to
            // a valid circular linked list
            self.a = (*self.a).prev;
        }
    }

    /// Moves the 'b' cursor to the previous element of the `CircularList`.
    pub fn move_prev_b(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (5) assert that `self.b` is a valid pointer to
            // a valid circular linked list
            self.b = (*self.b).prev;
        }
    }

    /// Returns the value of the list element behind the 'a' cursor.
    pub fn value_a(&self) -> &T {
        // SAFETY: Invariant (5) asserts that `self.a` is a valid pointer to a `ListHead<T>`.
        unsafe { &(*self.a).value }
    }

    /// Returns the value of the list element behind the 'b' cursor.
    pub fn value_b(&self) -> &T {
        // SAFETY: Invariant (5) asserts that `self.b` is a valid pointer to a `ListHead<T>`.
        unsafe { &(*self.b).value }
    }

    /// Swaps the 'a' and 'b' cursors of this `DoubleCursor`.
    pub fn swap_cursors(&mut self) {
        (self.a, self.b) = (self.b, self.a)
    }

    /// Sets the position of the 'a' cursor to the head of the list.
    pub fn reset_a(&mut self) {
        self.a = self.list.head;
    }

    /// Sets the position of the 'b' cursor to the head of the list.
    pub fn reset_b(&mut self) {
        self.b = self.list.head;
    }

    /// Sets the position of the 'b' cursor to the same as the 'a' cursor.
    pub fn set_b_to_a(&mut self) {
        self.b = self.a;
    }

    /// Sets the position of the 'a' cursor to the same as the 'b' cursor.
    pub fn set_a_to_b(&mut self) {
        self.a = self.b;
    }

    /// Saves the position of the 'a' cursor on a stack (internal to `Self`).
    pub fn push_a(&mut self) {
        self.stack.push(self.a);
    }

    /// Saves the position of the 'b' cursor on a stack (internal to `Self`).
    pub fn push_b(&mut self) {
        self.stack.push(self.b);
    }

    /// Load the position of the 'a' cursor to the last saved position of 'b' or 'a'.
    pub fn pop_a(&mut self) {
        if let Some(a) = self.stack.pop() {
            self.a = a;
        }
    }

    /// Load the position of the 'b' cursor to the last saved position of 'b' or 'a'.
    pub fn pop_b(&mut self) {
        if let Some(b) = self.stack.pop() {
            self.b = b;
        }
    }

    /// Swaps the list nodes pointed by the 'a' and 'b' cursors. It is a `O(1)` operation.
    pub fn swap(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (5) assert that `self.a` and `self.b` are part of
            // a valid circular linked list.
            ListHead::<T>::swap(self.a as *mut _, self.b as *mut _);
        }
        if self.a == self.list.head {
            self.list.head = self.b;
        } else if self.b == self.list.head {
            self.list.head = self.a;
        }
    }

    /// Displaces the element pointed by the 'a' cursor next to the element pointed by the 'b'
    /// cursor.
    pub fn insert_a_after_b(&mut self) {
        unsafe {
            // SAFETY: Invariant (5) asserts that `self.a` and `self.b` are valid. Invariant (3)
            // asserts that it is part of a valid circular linked list.
            if (*self.a).prev == self.b || self.a == self.b {
                // `self.a` is already in the good place.
                return;
            }
            if self.a == self.list.head {
                self.list.head = (*self.a).next;
            }
            ListHead::<T>::move_entry(self.a as *mut _, self.b as *mut _, (*self.b).next as *mut _);
        }
    }

    /// Displaces the element pointed by the 'b' cursor before the element pointed by the 'a'
    /// cursor.
    pub fn insert_b_before_a(&mut self) {
        unsafe {
            // SAFETY: Invariant (5) asserts that `self.a` and `self.b` are valid. Invariant (3)
            // asserts that it is part of a valid circular linked list.
            if (*self.a).prev == self.b || self.a == self.b {
                // `self.b` is already in the good place.
                return;
            }
            if self.b == self.list.head {
                self.list.head = (*self.b).next;
            }
            if self.a == self.list.head {
                self.list.head = self.b;
            }
            ListHead::<T>::move_entry(self.b as *mut _, (*self.a).prev as *mut _, self.a as *mut _);
        }
    }
}
