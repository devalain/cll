//! Circular doubly linked list.
//! The implementation is inspired by the [linux implementation in `C`
//! ](https://github.com/torvalds/linux/blob/master/include/linux/list.h).
//!
//! # Basic usage
//! ```
//! use cdll::CircularList;
//!
//! let mut my_list = CircularList::default();
//! for x in 1..=5 {
//!     my_list.add(x);
//! }
//!
//! assert_eq!(my_list.remove(), Some(1));
//! assert_eq!(my_list.pop(), Some(5));
//!
//! my_list.iter_mut().for_each(|x: &mut i32| *x -= 1);
//! assert_eq!(my_list.into_iter().collect::<Vec<i32>>(), &[1, 2, 3])
//! ```
//!
//! # Safety considerations
//! This crate uses `unsafe` code to dereference raw pointers. In order for it to be *sound*, one
//! has to preserve some invariants (e.g. pointers must be valid). To achieve this, the source code
//! is commented with careful justifications to *prove* correctness (at least it is a try).

#![no_std]
extern crate alloc;

mod head;
mod invariants;
mod sort;

pub use head::cursor::{Cursor, CursorMut, DoubleCursor};

use {
    crate::head::{Iter, IterMut, ListHead},
    core::{iter::FromIterator, ops::Not, ptr},
};

/// Create a list with provided elements.
/// # Example
/// ```
/// # use cdll::list;
/// let primes = list![2, 3, 5, 7, 11];
/// println!("{:?}", primes);
/// ```
/// It can also be used with whatever expression that is an `IntoIterator`
/// ```
/// # use cdll::list;
/// let first_hundred_numbers = list![@each 1_i32..=100];
/// let sum: i32 = first_hundred_numbers.into_iter().sum();
/// assert_eq!(sum, 5050);
/// ```
#[macro_export]
macro_rules! list {
    [$($elem:expr),* $(,)?] => {{
        #[allow(unused_mut)]
        let mut l = $crate::CircularList::default();
        $(
            l.add($elem);
        )*
        l
    }};
    [@each $iter:expr] => {{
        $iter.collect::<$crate::CircularList<_>>()
    }};
}

/// A circular doubly linked list.
pub struct CircularList<T> {
    /// The `head` field is a pointer to a `ListHead<T>`. The code try to preserve the following
    /// invariant (1): If the list is empty, it is null, otherwise it is a valid pointer that one
    /// can safely dereference. (See also [`INVARIANT_1`](`crate::invariants::INVARIANT_1`))
    head: *mut ListHead<T>,

    /// Obviously the number of elements in the list.
    /// Invariant (2): It is updated each time an element is added to the list or removed from it.
    /// (See also [`INVARIANT_1`](`crate::invariants::INVARIANT_2`))
    length: usize,
}

// private functions
impl<T> CircularList<T> {
    /// Creates a new `ListHead` with value `val` and places it after the element pointed by
    /// `element`.
    ///
    /// # Safety
    /// The caller must assert that `element` is a valid pointer to a `ListHead` that is a
    /// member of `self`.
    pub(crate) unsafe fn insert_after(&mut self, val: T, element: *mut ListHead<T>) {
        let new = ListHead::<T>::new(val);

        unsafe {
            // SAFETY: The caller promises us that `element` is valid and
            // belongs to `self`. The `new` pointer is obviously valid
            // since it was returned form `Box::into_raw`.
            ListHead::add_after(element, new);
        }

        // Preserving invariant (2)
        self.length += 1;
    }
}

impl<T> CircularList<T> {
    /// Gets the size of the list.
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns `true` if the list contains no element.
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Adds an element to the end of the list.
    ///
    /// # Exemple
    /// ```
    /// # use cdll::list;
    /// # let mut my_list = list!["Follow the white rabbit"];
    /// my_list.add("Hello");
    /// assert_eq!(my_list.pop(), Some("Hello"))
    ///
    pub fn add(&mut self, val: T) {
        let new = ListHead::<T>::new(val);

        // If `self.head` is null (which means `self.length == 0` by (2)) then
        // it is assigned to a valid pointer to the `new` element,
        // preserving (1).
        if self.head.is_null() {
            debug_assert_eq!(self.length, 0);
            self.head = new;
        } else {
            unsafe {
                // SAFETY: At this point, `head` must be valid since it was
                // initialized to `new` if it was null. The `new` pointer is
                // obviously valid since it was returned form `Box::into_raw`.
                ListHead::add(self.head, new);
            }
        }

        // Preserving invariant (2)
        self.length += 1;
    }

    /// Returns a shared reference to the value of the list head.
    /// # Panic
    /// Panics if the list is empty.
    pub fn peek(&self) -> &T {
        if self.is_empty() {
            panic!("Cannot peek when list is empty");
        }
        unsafe {
            // SAFETY: Invariant (1) guarantee the pointer head to be valid
            // when the list is not empty.
            (*self.head).value()
        }
    }

    /// Removes the first element of the list and returns it if any.
    pub fn remove(&mut self) -> Option<T> {
        // If `self.head` is null (which means `self.length == 0` by (2))
        // then there is nothing to do.
        if self.head.is_null() {
            debug_assert_eq!(self.length, 0);
            None
        } else if self.length == 1 {
            let value = unsafe { ListHead::into_value(self.head) };
            self.head = ptr::null_mut();

            // Preserving invariant (2)
            self.length -= 1;
            Some(value)
        } else {
            let (new_head, old_val) = unsafe {
                // SAFETY: Since `head` is not null, it must be valid as we try to preserve (1).
                // Furthermore, it must be true that it has pointers to its next and previous
                // elements because of the invariant (3) (see the `head` module).
                ListHead::<T>::del_entry(self.head)
            };
            // If there is a next element, it is the new head, otherwise `self.head` is null.
            // Invariant (1) is preserved since de `ListHead::del` function returns either null
            // or a valid pointer by invariant (3).
            self.head = new_head;

            // Preserving invariant (2)
            self.length -= 1;

            debug_assert_eq!(self.head.is_null(), self.length == 0);
            Some(old_val)
        }
    }

    /// Removes the last element of the list and returns it if any.
    pub fn pop(&mut self) -> Option<T> {
        // If there is only 1 element in the list,
        // the first and the last are the same.
        if self.length == 1 {
            self.remove()
        } else if self.head.is_null() {
            // The list is empty so we check the invariant (2).
            debug_assert_eq!(self.length, 0);
            None
        } else {
            let (_, old_val) = unsafe {
                // SAFETY: Since `head` is not null, it must be valid because of (1).
                // Furthermore, it must be true that it has pointers to its next and previous
                // elements because of invariant (3).
                ListHead::<T>::del_entry((*self.head).prev_mut_ptr())
            };

            // Preserving invariant (2)
            self.length -= 1;
            Some(old_val)
        }
    }

    /// Exchanges the place of the element at position `i` and the element at position `j`.
    /// This operation has `O(n)` complexity. For a constant time swap operation, see
    /// [`double_cursor`](`Self::double_cursor`) and [`DoubleCursor::swap`].
    pub fn exchange(&mut self, i: usize, j: usize) {
        // Do nothing if list is empty
        if self.is_empty() {
            return;
        }

        let i = i % self.length;
        let j = j % self.length;

        // Swaping an element with itself is a no-op.
        if i == j {
            return;
        }

        let from = i.min(j);
        let count = i.max(j) - from;
        let mut item1 = self.head;
        for _ in 0..from {
            item1 = unsafe {
                // SAFETY: The invariant (3) asserts that the pointer to the next element
                // of a `ListHead` is always valid.
                (*item1).next_mut_ptr()
            };
        }
        let mut item2 = item1;
        for _ in 0..count {
            item2 = unsafe {
                // SAFETY: The invariant (3) asserts that the pointer to the next element
                // of a `ListHead` is always valid.
                (*item2).next_mut_ptr()
            };
        }
        unsafe {
            // SAFETY: According to invariant (3), `item1` and `item2` are part of a valid circular
            // linked list.
            ListHead::<T>::swap(item1, item2);
        }
        if item1 == self.head {
            self.head = item2;
        } else if item2 == self.head {
            self.head = item1;
        }
    }

    /// Assembles this list with another by putting all its elements at the end the list.
    pub fn append(&mut self, mut other: Self) {
        if self.head.is_null() {
            self.head = other.head;
        } else if !other.head.is_null() {
            unsafe {
                // SAFETY: `head` is not null, so it must be a valid pointer because of (1)
                // `other_head` is not null, so it must be a valid pointer for the same reason.
                // `head` is obviously not in the same list as `other_head` since `head` comes from
                // an exclusive reference of `Self` and `other_head` comes from an owned `Self`.
                ListHead::<T>::add_list(other.head, self.head);
            }
        }

        // Preserving invariant (1)
        self.length += other.length;

        // `other` must be in valid state when being dropped.
        other.head = ptr::null_mut();
        other.length = 0;
    }

    /// Assembles this list with another by keeping the elements sorted.
    /// It is assumed that the 2 lists are sorted.
    pub fn merge(&mut self, mut other: Self)
    where
        T: PartialOrd,
    {
        if self.is_empty() {
            self.append(other);
        } else if other.is_empty().not() {
            let mut s = self.head;
            let mut s_head = s;
            let mut o = other.head;
            unsafe {
                let mut s_next = (*s).next_mut_ptr();
                let mut o_next = (*o).next_mut_ptr();
                let o_end = (*o).prev_mut_ptr();
                if *o < *s {
                    self.head = o;
                    s_head = o;
                }
                let mut reached_end_of_s = false;
                loop {
                    if reached_end_of_s {
                        ListHead::add_list(o, s_head);
                        break;
                    } else if *o < *s {
                        ListHead::move_entry(o, (*s).prev_mut_ptr(), s);
                        if o == o_end {
                            // We reached the last element of `other`
                            break;
                        }
                        o = o_next;
                        o_next = (*o).next_mut_ptr();
                    } else {
                        s = s_next;
                        s_next = (*s).next_mut_ptr();
                        reached_end_of_s = s == s_head;
                    }
                }
            }

            // Preserving invariant (1)
            self.length += other.length;

            // `other` must be in valid state when being dropped.
            other.head = ptr::null_mut();
            other.length = 0;
        }
    }

    /// Sorts the list.
    pub fn sort(&mut self)
    where
        T: PartialOrd,
    {
        sort::sort::<T, sort::MergeSort<T>>(self)
    }

    /// Moves the head `count` steps to the left.
    ///
    /// # Example
    /// ```
    /// # use cdll::CircularList;
    /// let mut yoda_says: CircularList<_> = "ready you are not ".chars().collect();
    /// yoda_says.left_rot(6);
    /// assert_eq!("you are not ready ", yoda_says.into_iter().collect::<String>())
    /// ```
    pub fn left_rot(&mut self, count: usize) {
        // Do nothing if list is empty
        if self.is_empty() {
            return;
        }
        let count = count % self.length;
        for _ in 0..count {
            self.head = unsafe {
                // SAFETY: Since the list is non empty and according to invariants (1) and (3),
                // `head` is a valid pointer to a valid circular linked list. So it must be true
                // that its next element is also valid.
                (*self.head).next_mut_ptr()
            };
        }
    }

    /// Rotate the head of the list `count` times to the left if `count > 0` or `-count` times to
    /// the right if `count < 0`. Do nothing if `count == 0`.  
    pub fn rotate(&mut self, count: isize) {
        // Do nothing if list is empty
        if self.is_empty() {
            return;
        }
        let count = count.rem_euclid(self.length as isize);
        for _ in 0..count {
            self.head = unsafe {
                // SAFETY: Since the list is non empty and according to invariants (1) and (3),
                // `head` is a valid pointer to a valid circular linked list. So it must be true
                // that its next element is also valid.
                (*self.head).next_mut_ptr()
            };
        }
    }

    /// Rotate the head until the given condition is true. Do nothing on empty lists.
    pub fn rotate_until<F: Fn(&T) -> bool>(&mut self, f: F) {
        if self.is_empty() {
            // nothing to do then
            return;
        }
        loop {
            if f(self.peek()) {
                break;
            }
            self.left_rot(1);
        }
    }

    /// Moves the head `count` steps to the right.
    ///
    /// # Example
    /// ```
    /// # use cdll::CircularList;
    /// let mut yoda_says: CircularList<_> = "the greatest teacher failure is ".chars().collect();
    /// yoda_says.right_rot(11);
    /// assert_eq!("failure is the greatest teacher ", yoda_says.into_iter().collect::<String>())
    /// ```
    pub fn right_rot(&mut self, count: usize) {
        // Do nothing if list is empty
        if self.is_empty() {
            return;
        }
        let count = count % self.length;
        for _ in 0..count {
            self.head = unsafe {
                // SAFETY: Since the list is non empty and according to invariants (1) and (3),
                // `head` is a valid pointer to a valid circular linked list. So it must be true
                // that its previous element is also valid.
                (*self.head).prev_mut_ptr()
            };
        }
    }

    /// Returns an infinite iterator over the list except if it is empty, in which case the
    /// returned iterator is also empty.
    pub fn iter_forever(&self) -> impl Iterator<Item = &T> {
        self.is_empty()
            .not()
            .then(|| Iter::new(self))
            .into_iter()
            .flatten()
    }

    /// Returns an iterator over the list.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.iter_forever().take(self.len())
    }

    /// Returns an infinite iterator that allows modifying each value. The returned iterator is
    /// empty if the list is empty.
    pub fn iter_mut_forever(&mut self) -> impl Iterator<Item = &mut T> {
        self.is_empty()
            .not()
            .then(|| IterMut::new(self))
            .into_iter()
            .flatten()
    }

    /// Returns an iterator that allows modifying each value.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        let len = self.len();
        self.iter_mut_forever().take(len)
    }

    /// Returns some [`Cursor`] pointing to the first element of the list (if any).
    pub fn cursor(&self) -> Option<Cursor<T>> {
        self.is_empty().not().then(|| Cursor::from_list(self))
    }

    /// Returns some [`CursorMut`] pointing to the first element of the list (if any).
    pub fn cursor_mut(&mut self) -> Option<CursorMut<T>> {
        self.is_empty().not().then(|| CursorMut::from_list(self))
    }

    /// Returns some [`DoubleCursor`] where the 'a' and the 'b' parts are pointing both to the
    /// first element of the list (if any).
    pub fn double_cursor(&mut self) -> Option<DoubleCursor<T>> {
        self.is_empty().not().then(|| DoubleCursor::from_list(self))
    }
}

impl<T> Default for CircularList<T> {
    fn default() -> Self {
        Self {
            head: ptr::null_mut(),
            length: 0,
        }
    }
}

impl<T: Clone> Clone for CircularList<T> {
    fn clone(&self) -> Self {
        let mut clone: Self = Default::default();
        for x in self.iter() {
            clone.add(x.clone());
        }
        clone
    }
}

impl<T> FromIterator<T> for CircularList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut new: Self = Default::default();
        for x in iter {
            new.add(x);
        }
        new
    }
}

impl<T> Drop for CircularList<T> {
    fn drop(&mut self) {
        while self.remove().is_some() {}
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for CircularList<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// An owning iterator over the elements of a `CircularList`.
/// This `struct` is created by [`CircularList::into_iter()`].
pub struct IntoIter<T>(CircularList<T>);
impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.remove()
    }
}
impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}
impl<T> IntoIterator for CircularList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::<T>(self)
    }
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        alloc::{vec, vec::Vec},
    };

    #[test]
    fn empty() {
        let l = CircularList::default();
        assert_eq!(l.iter().copied().collect::<Vec<i32>>(), &[]);
    }

    #[test]
    fn add() {
        let l = list![42, 43, 44, 45, 46];
        assert_eq!(l.into_iter().collect::<Vec<i32>>(), &[42, 43, 44, 45, 46])
    }

    #[test]
    fn remove() {
        let mut l = list![42, 43, 44, 45, 46];
        assert_eq!(Some(42), l.remove());
        assert_eq!(Some(43), l.remove());
        assert_eq!(Some(44), l.remove());
        assert_eq!(Some(45), l.remove());
        assert_eq!(Some(46), l.remove());
    }

    #[test]
    fn mutating() {
        let mut l = list![42, 43, 44, 45, 46];
        for x in l.iter_mut() {
            *x += 1;
        }
        assert_eq!(
            l.iter().copied().collect::<Vec<i32>>(),
            &[43, 44, 45, 46, 47]
        );
    }

    #[test]
    fn exchange() {
        for (i, j, expected) in [
            (1, 3, &[42, 45, 44, 43, 46]),
            (0, 1, &[43, 42, 44, 45, 46]),
            (1, 2, &[42, 44, 43, 45, 46]),
            (3, 4, &[42, 43, 44, 46, 45]),
            (2, 2, &[42, 43, 44, 45, 46]),
            (0, 4, &[46, 43, 44, 45, 42]),
        ] {
            let mut l = list![42, 43, 44, 45, 46];
            l.exchange(i, j);
            assert_eq!(l.into_iter().collect::<Vec<i32>>(), expected);
        }

        let mut l = list![42, 43];
        l.exchange(0, 1);
        assert_eq!(l.into_iter().collect::<Vec<i32>>(), &[43, 42]);
    }

    #[test]
    fn left_rotate() {
        let mut l = list![42, 43, 44, 45, 46];
        l.left_rot(3);
        assert_eq!(l.into_iter().collect::<Vec<i32>>(), &[45, 46, 42, 43, 44]);
    }

    #[test]
    fn right_rotate() {
        let mut l = list![42, 43, 44, 45, 46];
        l.right_rot(3);
        assert_eq!(l.into_iter().collect::<Vec<i32>>(), &[44, 45, 46, 42, 43]);
    }

    #[test]
    fn into_iter_double_ended_iterator() {
        let numbers = list![1, 2, 3, 4, 5, 6];

        let mut iter = numbers.into_iter();

        assert_eq!(Some(1), iter.next());
        assert_eq!(Some(6), iter.next_back());
        assert_eq!(Some(5), iter.next_back());
        assert_eq!(Some(2), iter.next());
        assert_eq!(Some(3), iter.next());
        assert_eq!(Some(4), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next_back());
    }

    #[test]
    fn iter_forever() {
        let numbers = list![1, 2, 3, 4, 5, 6];
        let double_sum = numbers
            .iter_forever()
            .take(2 * numbers.len())
            .copied()
            .sum();
        assert_eq!(42, double_sum);
    }

    #[test]
    fn from_iterator() {
        let mut numbers: CircularList<_> = vec![4, 5, 6, 7].into_iter().collect();
        assert_eq!(Some(7), numbers.pop());
        assert_eq!(Some(6), numbers.pop());
        assert_eq!(Some(5), numbers.pop());
        assert_eq!(Some(4), numbers.pop());
        assert_eq!(None, numbers.pop());
    }

    #[test]
    fn into_iter_rev() {
        let numbers = list![1, 2, 3];
        let mut iter = numbers.into_iter().rev();
        assert_eq!(Some(3), iter.next());
        assert_eq!(Some(2), iter.next());
        assert_eq!(Some(1), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn append() {
        let mut a = list![1, 2, 3];
        let b = list![4, 5, 6, 7];
        a.append(b);
        assert_eq!(a.len(), 7);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[1, 2, 3, 4, 5, 6, 7]);

        let mut a = list![1, 2, 3];
        a.append(list![]);
        assert_eq!(a.len(), 3);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[1, 2, 3]);

        let mut a = list![];
        a.append(list![1, 2, 3]);
        assert_eq!(a.len(), 3);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[1, 2, 3]);

        let mut a = list![];
        a.append(list![]);
        assert_eq!(a.len(), 0);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[]);
    }

    #[test]
    fn merge() {
        for (mut a, b, c) in [
            (list![1, 2, 3], list![], vec![1, 2, 3]),
            (list![], list![1, 2, 3], vec![1, 2, 3]),
            (list![1], list![0], vec![0, 1]),
            (list![1], list![0], vec![0, 1]),
            (list![1, 2, 3], list![4, 5, 6], vec![1, 2, 3, 4, 5, 6]),
            (list![1, 3, 5], list![2, 4, 6], vec![1, 2, 3, 4, 5, 6]),
            (list![1, 3, 5], list![0, 2, 4, 6], vec![0, 1, 2, 3, 4, 5, 6]),
            (list![1, 3, 5], list![2, 4], vec![1, 2, 3, 4, 5]),
            (list![1, 3, 5], list![2, 2, 4, 4], vec![1, 2, 2, 3, 4, 4, 5]),
            (list![1, 3], list![0, 0, 4, 8], vec![0, 0, 1, 3, 4, 8]),
            (list![7, 8, 9], list![1, 2, 8], vec![1, 2, 7, 8, 8, 9]),
            (list![5, 5, 6], list![5, 8, 9], vec![5, 5, 5, 6, 8, 9]),
            (list![1, 2, 3], list![1, 2, 3], vec![1, 1, 2, 2, 3, 3]),
        ] {
            a.merge(b);
            assert_eq!(a.into_iter().collect::<Vec<i32>>(), c);
        }
    }
}
