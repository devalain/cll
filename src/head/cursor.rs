use {super::ListHead, crate::CircularList, alloc::vec::Vec};

/// A `Cursor` is like an iterator, except that it can freely seek back-and-forth.
/// This `struct` is constructed by the [`CircularList::cursor`](CircularList::cursor)
/// function.
#[derive(Clone, Copy)]
pub struct Cursor<'life, T> {
    list: &'life CircularList<T>,
    // Invariant (4): `current` is a valid pointer.
    current: *const ListHead<T>,
}

impl<'life, T> PartialEq for Cursor<'life, T> {
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

    /// Returns a reference of the underlying list.
    pub fn list(&self) -> &CircularList<T> {
        self.list
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
            self.current = (*self.current).next_ptr();
        }
    }

    /// Moves the cursor to the previous element of the `CircularList`.
    pub fn move_prev(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (4) assert that `self.current` is a valid pointer to
            // a valid circular linked list
            self.current = (*self.current).prev_ptr();
        }
    }

    /// Returns the value of the list element behind the cursor.
    pub fn value(&self) -> &T {
        // SAFETY: Invariant (4) asserts that `current` is a valid pointer to a `ListHead<T>`.
        unsafe { (*self.current).value() }
    }
}

impl<'life, T: core::fmt::Debug> core::fmt::Debug for Cursor<'life, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.value().fmt(f)
    }
}

impl<'life, T: core::fmt::Display> core::fmt::Display for Cursor<'life, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.value().fmt(f)
    }
}

/// A `DoubleCursor` is a `struct` that points to 2 elements 'a' and 'b' of a [`CircularList`].
/// One can then [`swap`](`Self::swap`) the 2 elements or put the first after the second etc.
#[derive(Debug)]
pub struct DoubleCursor<'life, T> {
    list: &'life mut CircularList<T>,
    // Invariant (5):
    // * `a` and `b` are always valid pointers
    // * The `idx_a` and `idx_b` are always equal to the number of (forward) steps between the
    // head and the position of `a` and `b` respectively
    a: *mut ListHead<T>,
    b: *mut ListHead<T>,
    idx_a: usize,
    idx_b: usize,
    stack: Vec<(*mut ListHead<T>, usize)>,
}

// Private functions
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
            idx_a: 0,
            idx_b: 0,
            stack: Vec::new(),
        }
    }

    /// Returns a reference of the underlying list.
    pub fn list(&self) -> &CircularList<T> {
        self.list
    }

    /// Cuts the list at `new_head` and create a new list from there.
    ///
    /// # Note
    /// The `DoubleCursor` is consumed in the operation.
    ///
    /// # Safety
    /// The caller must assert that `new_head` is a valid pointer to a `ListHead` that is a member
    /// of the same list as `self.list`. The `idx` must correspond to the index of `new_head` in
    /// `self.list`.
    unsafe fn split_at(self, new_head: *mut ListHead<T>, idx: usize) -> CircularList<T> {
        let head = self.list.head;
        if head == new_head {
            return core::mem::take(self.list);
        }

        // SAFETY: `head` must be a valid pointer since a double cursor cannot be created from
        // an empty list.
        ListHead::<T>::split(head, new_head);

        // The `new_head` is wrapped in a new `CircularList` to satisfy the safety condition of
        // `ListHead::split`.
        let new_list = CircularList {
            head: new_head,
            length: self.list.length - idx,
        };
        self.list.length = idx;
        new_list
    }
}

impl<'life, T> DoubleCursor<'life, T> {
    /// Returns `true` if the 'a' cursor points to the same element as the 'b cursor.
    pub fn a_is_b(&self) -> bool {
        self.a == self.b
    }

    /// Moves the 'a' cursor to the next element of the `CircularList`.
    pub fn move_next_a(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (5) assert that `self.a` is a valid pointer to
            // a valid circular linked list
            self.a = (*self.a).next_mut_ptr();
        }
        self.idx_a = (self.idx_a + 1) % self.list.len();
    }

    /// Moves the 'b' cursor to the next element of the `CircularList`.
    pub fn move_next_b(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (5) assert that `self.b` is a valid pointer to
            // a valid circular linked list
            self.b = (*self.b).next_mut_ptr();
        }
        self.idx_b = (self.idx_b + 1) % self.list.len();
    }

    /// Moves the 'a' cursor to the previous element of the `CircularList`.
    pub fn move_prev_a(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (5) assert that `self.a` is a valid pointer to
            // a valid circular linked list
            self.a = (*self.a).prev_mut_ptr();
        }
        let len = self.list.len();
        self.idx_a = (len + self.idx_a - 1) % len;
    }

    /// Moves the 'b' cursor to the previous element of the `CircularList`.
    pub fn move_prev_b(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (5) assert that `self.b` is a valid pointer to
            // a valid circular linked list
            self.b = (*self.b).prev_mut_ptr();
        }
        let len = self.list.len();
        self.idx_b = (len + self.idx_b - 1) % len;
    }

    /// Returns the value of the list element behind the 'a' cursor.
    pub fn value_a(&self) -> &T {
        // SAFETY: Invariant (5) asserts that `self.a` is a valid pointer to a `ListHead<T>`.
        unsafe { (*self.a).value() }
    }

    /// Returns the value of the list element behind the 'b' cursor.
    pub fn value_b(&self) -> &T {
        // SAFETY: Invariant (5) asserts that `self.b` is a valid pointer to a `ListHead<T>`.
        unsafe { (*self.b).value() }
    }

    /// Swaps the 'a' and 'b' cursors of this `DoubleCursor`.
    pub fn swap_cursors(&mut self) {
        (self.a, self.b) = (self.b, self.a);
        (self.idx_a, self.idx_b) = (self.idx_b, self.idx_a);
    }

    /// Sets the position of the 'a' cursor to the head of the list.
    pub fn reset_a(&mut self) {
        self.a = self.list.head;
        self.idx_a = 0;
    }

    /// Sets the position of the 'b' cursor to the head of the list.
    pub fn reset_b(&mut self) {
        self.b = self.list.head;
        self.idx_b = 0;
    }

    /// Sets the position of the 'b' cursor to the same as the 'a' cursor.
    pub fn set_b_to_a(&mut self) {
        self.b = self.a;
        self.idx_b = self.idx_a;
    }

    /// Sets the position of the 'a' cursor to the same as the 'b' cursor.
    pub fn set_a_to_b(&mut self) {
        self.a = self.b;
        self.idx_a = self.idx_b;
    }

    /// Saves the position of the 'a' cursor on a stack (internal to `Self`).
    pub fn push_a(&mut self) {
        self.stack.push((self.a, self.idx_a));
    }

    /// Saves the position of the 'b' cursor on a stack (internal to `Self`).
    pub fn push_b(&mut self) {
        self.stack.push((self.b, self.idx_b));
    }

    /// Load the position of the 'a' cursor to the last saved position of 'b' or 'a'.
    pub fn pop_a(&mut self) {
        if let Some((a, idx_a)) = self.stack.pop() {
            (self.a, self.idx_a) = (a, idx_a);
        }
    }

    /// Load the position of the 'b' cursor to the last saved position of 'b' or 'a'.
    pub fn pop_b(&mut self) {
        if let Some((b, idx_b)) = self.stack.pop() {
            (self.b, self.idx_b) = (b, idx_b);
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

    /// Cuts the list at the position pointing on the 'a' cursor.
    ///
    /// # Note
    /// The `DoubleCursor` is consumed in the operation.
    pub fn split_at_a(self) -> CircularList<T> {
        let a = self.a;
        let idx_a = self.idx_a;
        unsafe {
            // SAFETY: `self.a` is valid and `self.idx_a` is the index of `self.a` in `self.list`
            // according to (5).
            self.split_at(a, idx_a)
        }
    }

    /// Cuts the list at the position pointing on the 'b' cursor.
    ///
    /// # Note
    /// The `DoubleCursor` is consumed in the operation.
    pub fn split_at_b(self) -> CircularList<T> {
        let b = self.b;
        let idx_b = self.idx_b;
        unsafe {
            // SAFETY: `self.b` is valid and `self.idx_b` is the index of `self.b` in `self.list`
            // according to (5).
            self.split_at(b, idx_b)
        }
    }

    /// Displaces the element pointed by the 'a' cursor next to the element pointed by the 'b'
    /// cursor.
    pub fn insert_a_after_b(&mut self) {
        unsafe {
            // SAFETY: Invariant (5) asserts that `self.a` and `self.b` are valid. Invariant (3)
            // asserts that it is part of a valid circular linked list.
            if (*self.a).prev_ptr() == self.b || self.a == self.b {
                // `self.a` is already in the good place.
                return;
            }
            if self.a == self.list.head {
                // keep the head in its place
                self.list.head = (*self.a).next_mut_ptr();
            }
            ListHead::<T>::move_entry(self.a, self.b, (*self.b).next_mut_ptr());
        }
    }

    /// Displaces the element pointed by the 'b' cursor before the element pointed by the 'a'
    /// cursor.
    pub fn insert_b_before_a(&mut self) {
        unsafe {
            // SAFETY: Invariant (5) asserts that `self.a` and `self.b` are valid. Invariant (3)
            // asserts that it is part of a valid circular linked list.
            if (*self.a).prev_ptr() == self.b || self.a == self.b {
                // `self.b` is already in the good place.
                return;
            }
            if self.b == self.list.head {
                // keep the head in its place
                self.list.head = (*self.b).next_mut_ptr();
            }
            if self.a == self.list.head {
                // Inserting before the head means not at the end of the list
                self.list.head = self.b;
            }
            ListHead::<T>::move_entry(self.b, (*self.a).prev_mut_ptr(), self.a);
        }
    }

    /// Creates a new list node with value `val` and places it after the element pointed by the
    /// cursor 'a'.
    pub fn insert_value_after_a(&mut self, val: T) {
        unsafe {
            // SAFETY: According to invariant (5), `self.a` is a valid pointer. Moreover, `self.a`
            // points to a member of `self.list`.
            self.list.insert_after(val, self.a)
        }
        // Preserving invariant (5)
        if self.idx_a < self.idx_b {
            self.idx_b += 1;
        }
    }

    /// Creates a new list node with value `val` and places it after the element pointed by the
    /// cursor 'b'.
    pub fn insert_value_after_b(&mut self, val: T) {
        unsafe {
            // SAFETY: According to invariant (5), `self.b` is a valid pointer. Moreover, `self.b`
            // points to a member of `self.list`.
            self.list.insert_after(val, self.b)
        }
        // Preserving invariant (5)
        if self.idx_b < self.idx_a {
            self.idx_a += 1;
        }
    }
}

/// Like a [`Cursor`] but with mutative operations on the list.
/// This `struct` is constructed by the [`CircularList::cursor_mut`](CircularList::cursor_mut)
/// function.
pub struct CursorMut<'life, T> {
    list: &'life mut CircularList<T>,
    // Invariant (6): `current` is a valid pointer to an element of `list`.
    current: *mut ListHead<T>,
}

impl<'life, T> CursorMut<'life, T> {
    /// Builds a `CursorMut` from a (valid) pointer to a `ListHead<T>`.
    /// # Panics
    /// This function panics if the list is empty.
    pub(crate) fn from_list(list: &'life mut CircularList<T>) -> Self {
        if list.is_empty() {
            // Preserving the invariant (6)
            panic!("Cannot build a `Cursor` from an empty list.");
        }
        let current = list.head;
        Self { list, current }
    }

    /// Returns a reference of the underlying list.
    pub fn list(&self) -> &CircularList<T> {
        self.list
    }

    /// Returns to its initial position (the head of the list).
    pub fn reset(&mut self) {
        self.current = self.list.head;
    }

    /// Moves the cursor to the next element of the `CircularList`.
    pub fn move_next(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (6) assert that `self.current` is a valid pointer to
            // a valid circular linked list
            self.current = (*self.current).next_mut_ptr();
        }
    }

    /// Moves the cursor to the previous element of the `CircularList`.
    pub fn move_prev(&mut self) {
        unsafe {
            // SAFETY: Invariants (3) and (6) assert that `self.current` is a valid pointer to
            // a valid circular linked list
            self.current = (*self.current).prev_mut_ptr();
        }
    }

    /// Returns the (mutable reference to the) value of the list element behind the cursor.
    pub fn value(&mut self) -> &mut T {
        // SAFETY: Invariant (6) asserts that `current` is a valid pointer to a `ListHead<T>`.
        unsafe { (*self.current).value_mut() }
    }

    /// Removes the current element from the list and returns its value. The new current element is
    /// the next element. Use [`remove_final`](Self::remove_final) function to remove the last
    /// element.
    ///
    /// # Panics
    /// The function panics if it is called on a cursor to a list with only 1 element because there
    /// cannot be a `Cursor` or `CursorMut` to an empty list.
    pub fn remove(&mut self) -> T {
        if self.list.len() == 1 {
            panic!("Cannot remove the last element with this function");
        }
        if self.list.head == self.current {
            let val = self.list.remove().unwrap();

            // Preserve invariant (6).
            self.current = self.list.head;

            val
        } else {
            unsafe {
                // SAFETY: Invariant (6) asserts that `current` is a valid pointer to a `ListHead<T>`.
                let (next, val) = ListHead::del_entry(self.current);

                // Preserve invariant (6).
                self.current = next;

                // Preserving invariant (2).
                self.list.length -= 1;

                val
            }
        }
    }

    /// Removes the current element from the list, returns its value and consumes the cursor. To be
    /// used when the list contains only 1 element.
    pub fn remove_final(self) -> T {
        if self.list.head == self.current {
            // Invariant (6) does not need to be preserved here as the cursor is consumed.
            self.list.remove().unwrap()
        } else {
            unsafe {
                // SAFETY: Invariant (6) asserts that `current` is a valid pointer to a `ListHead<T>`.
                let (_next, val) = ListHead::del_entry(self.current);

                // Preserving invariant (2).
                self.list.length -= 1;

                val
            }
        }
    }

    /// Inserts an element before the current one.
    pub fn insert_before(&mut self, val: T) {
        unsafe {
            // SAFETY: Invariant (6) asserts that `current` is a valid pointer to a `ListHead<T>`
            // and it is part of the list.
            self.list.insert_after(val, (*self.current).prev_mut_ptr());
        }
    }

    /// Inserts an element after the current one.
    pub fn insert_after(&mut self, val: T) {
        unsafe {
            // SAFETY: Invariant (6) asserts that `current` is a valid pointer to a `ListHead<T>`
            // and it is part of the list.
            self.list.insert_after(val, self.current);
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        crate::{list, CircularList},
        alloc::vec::Vec,
    };

    #[test]
    fn cursor_empty_list() {
        assert_eq!(CircularList::<()>::default().cursor(), None)
    }

    #[test]
    fn cursor() {
        let list = list![1, 2, 3, 4, 5];
        let mut c1 = list
            .cursor()
            .expect("A cursor should always be available on a non empty list");

        assert_eq!(c1.value(), &1);

        c1.move_prev();
        assert_eq!(c1.value(), &5);

        for _ in 0..5 {
            c1.move_next();
        }
        assert_eq!(c1.value(), &5);

        c1.move_next();
        c1.move_next();
        assert_eq!(c1.value(), &2);
    }

    #[test]
    fn double_cursor_empty_list() {
        assert!(matches!(
            CircularList::<()>::default().double_cursor(),
            None
        ))
    }

    #[test]
    fn double_cursor_swap() {
        let mut list = list![1, 2, 3, 4, 5];
        let mut dc = list
            .double_cursor()
            .expect("A cursor should always be available on a non empty list");

        dc.move_next_b();
        dc.swap();
        assert_eq!(list.into_iter().collect::<Vec<i32>>(), &[2, 1, 3, 4, 5]);

        let mut list = list![0];
        let mut dc = list.double_cursor().unwrap();
        dc.swap();
        assert_eq!(list.into_iter().collect::<Vec<i32>>(), &[0]);
    }

    #[test]
    fn double_cursor_move() {
        let mut list = list![1, 2, 3, 4, 5];
        let mut dc = list
            .double_cursor()
            .expect("A cursor should always be available on a non empty list");

        dc.move_next_b();
        dc.insert_a_after_b();
        // This function is idempotent
        dc.insert_a_after_b();
        assert_eq!(list.into_iter().collect::<Vec<i32>>(), &[2, 1, 3, 4, 5]);
    }

    #[test]
    fn double_cursor_sort() {
        let mut list = list![3, 1, 8, 21, 5, 9, 12, 5, 2, 6, 6, 6, 13, 2, 17];
        let len = list.len();
        let mut dc = list
            .double_cursor()
            .expect("A cursor should always be available on a non empty list");

        let mut min = *dc.value_a();
        for i in 1..len {
            dc.set_b_to_a();
            dc.push_a();
            for _ in i..len {
                dc.move_next_a();
                let val = *dc.value_a();
                if val < min {
                    min = val;
                    dc.set_b_to_a();
                }
            }
            dc.pop_a();
            dc.insert_b_before_a();
            if dc.a_is_b() {
                dc.move_next_a();
            }
            min = *dc.value_a();
        }
        assert_eq!(
            list.into_iter().collect::<Vec<i32>>(),
            &[1, 2, 2, 3, 5, 5, 6, 6, 6, 8, 9, 12, 13, 17, 21]
        );
    }

    #[test]
    fn double_cursor_split_empty() {
        let mut list = list![1, 2, 3, 4, 5];
        let dc = list.double_cursor().unwrap();

        let list2 = dc.split_at_a();
        let v2 = list2.into_iter().collect::<Vec<i32>>();

        assert_eq!(v2, &[1, 2, 3, 4, 5]);
        assert!(list.is_empty());
    }

    #[test]
    fn double_cursor_split() {
        let mut list = list![1, 2, 3, 4, 5];
        let mut dc = list.double_cursor().unwrap();

        dc.move_next_a();
        dc.move_next_a();
        let list2 = dc.split_at_a();

        let v1 = list.into_iter().collect::<Vec<i32>>();
        let v2 = list2.into_iter().collect::<Vec<i32>>();
        assert_eq!(v1, &[1, 2]);
        assert_eq!(v2, &[3, 4, 5]);
    }

    #[test]
    fn double_cursor_insert_val_after_a() {
        let mut list = list![1, 2, 3, 4, 5];
        let mut dc = list.double_cursor().unwrap();

        dc.move_next_a();
        dc.move_next_a();

        dc.insert_value_after_a(42);
        let v1 = list.into_iter().collect::<Vec<i32>>();
        assert_eq!(v1, &[1, 2, 3, 42, 4, 5]);
    }

    #[test]
    fn cursor_mut_remove() {
        let mut list = list![1, 2, 3, 4, 5];
        let mut c = list.cursor_mut().unwrap();

        c.move_next();
        assert_eq!(c.remove(), 2);
        assert_eq!(c.remove(), 3);
        assert_eq!(c.remove(), 4);
        assert_eq!(c.remove(), 5);
        assert_eq!(c.remove_final(), 1);
    }

    #[test]
    fn cursor_mut_insert() {
        let mut list = list![1, 2, 3, 4, 5];
        let mut c = list.cursor_mut().unwrap();

        c.move_next();
        assert_eq!(c.remove(), 2);
        c.insert_before(2);
        let v1 = list.into_iter().collect::<Vec<i32>>();
        assert_eq!(v1, &[1, 2, 3, 4, 5]);
    }
}
