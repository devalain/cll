#![allow(dead_code)]
//! This module is used to documents the invariants that are meant to be
//! preserved in this crate.

/// If a [`CircularList<T>`](`crate::CircularList<T>`) is empty,
/// its `head` (which is a [`ListHead<T>`](`crate::head::ListHead<T>`)) is
/// null, otherwise it is a valid pointer that one can safely dereference.
pub const INVARIANT_1: () = ();

/// The `length` attribute of a [`CircularList<T>`](`crate::CircularList<T>`)
/// is updated each time an element is added to the list or removed from it.
pub const INVARIANT_2: () = ();

/// Within a [`ListHead<T>`](`crate::head::ListHead<T>`):
/// * The `next` and `prev` pointers are always valid
/// * Following the `next` field recursively must always end up to the original `Self`
/// * Following the `prev` field recursively must give the exact reverse path as the `next` one
pub const INVARIANT_3: () = ();

/// The `current` attribute of a [`Cursor<T>`](`crate::Cursor<T>`) is a valid pointer.
pub const INVARIANT_4: () = ();

/// Within a [`DoubleCursor<T>`](`crate::DoubleCursor<T>`):
/// * `a` and `b` are always valid pointers
/// * The `idx_a` and `idx_b` are always equal to the number of (forward) steps between the
/// head and the position of `a` and `b` respectively
pub const INVARIANT_5: () = ();
