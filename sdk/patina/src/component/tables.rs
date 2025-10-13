//! TODO: When creating a new table, actually create the columns immediately.
//!
//! This crate provides a way to store data in a Data-Oriented way rather than an Object-Oriented way.
//!
//! That is to say, instead of having a struct with many fields, you now have a table with many columns where each
//! column represents a field of the struct.

extern crate alloc;
use core::{alloc::Layout, any::TypeId, borrow::Borrow, fmt::Debug, num::NonZeroUsize, ptr::NonNull};

use alloc::{
    alloc::{Allocator, Global},
    boxed::Box,
    collections::btree_map::BTreeMap,
    vec::Vec,
};

pub trait Fields {
    /// Adds the fields in this bundle to the specified table at the specified row.
    fn add_fields_to_table(self, row: usize, table: &mut Table);

    fn ids() -> Box<[core::any::TypeId]>;
}

pub trait Field: 'static + Sized {}

// A macro that implements the bundle trait for a tuple of fields, based off of
// the number of things passed to the macro
macro_rules! impl_field_bundle {
    ($($field:ident),+) => {
        #[allow(unused_parens)]
        #[allow(non_snake_case)]
        impl<$( $field: Field ),+> Fields for ( $( $field ),+ ) {
            fn add_fields_to_table(self, row: usize, table: &mut Table) {
                let ( $( $field ),+ ) = self;
                $(
                    table.write_value_to_row(row, $field);
                )+
            }

            fn ids() -> Box<[core::any::TypeId]> {
                Box::new([ $( core::any::TypeId::of::<$field>() ),+ ])
            }
        }
    };
}

impl_field_bundle!(A);
impl_field_bundle!(A, B);
impl_field_bundle!(A, B, C);
impl_field_bundle!(A, B, C, D);
impl_field_bundle!(A, B, C, D, E);

/// A way to refer to a unique row in a unique table.
///
/// A handle is a way to add or remove fields
#[derive(Clone, Copy, Debug)]
pub struct Handle {
    /// The index of this handle in the handle metadata list.
    index: usize,
    /// The generation of this handle, incremented each time the handle is reused.
    generation: u32,
}

/// Metadata associated with a handle to verify it's validity and quickly locate it's fields.
#[derive(Clone, Copy)]
struct HandleMeta {
    /// The current generation of this handle. If a [Handle] has a different generation, it is invalid.
    generation: u32,
    /// The index of the [Table] that holds the data of the [Handle] in [Tables::tables].
    table_index: usize,
    /// The row in the [Table] that holds the data of the [Handle].
    row: usize,
}

/// A wrapper around the column ID's, so that a custom [Borrow] implementation can be provided for easier lookups in
/// the [BTreeMap] in [Tables].
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct Columns(Box<[TypeId]>);

impl Borrow<[TypeId]> for Columns {
    fn borrow(&self) -> &[TypeId] {
        &self.0
    }
}

// pub struct DebugTables<'a, F: Fields> {
//     tables: &'a Tables,
//     _marker: core::marker::PhantomData<F>,
// }

// impl<F: Fields> Debug for DebugTables<'_, F> {
//     d
// }
/// A collection of [Table]s where each table has a unique, ordered, set of columns.
///
/// When a handle is created with a set of fields, it is placed in a table that has exactly those fields as columns.
/// When fields are added or removed from a handle, the row is moved to a new table that has exactly the new set of
/// fields as columns.
///
/// Note that a handle with no fields is still valid, and will be placed in a table with no columns.
pub struct Tables {
    /// A [Handle] is an index into this list, which contains the metadata necessary to validate and locate the
    /// handle's data.
    handles: Vec<HandleMeta>,
    /// A list of indices into [Tables::handles] that should be reused when creating a new handle.
    free_handles: Vec<usize>,
    /// The actual tables, each with a unique set of columns
    tables: Vec<Table>,
    /// A mapping of the Columns a table contains to the index of that table in [Tables::tables]
    table_ids: BTreeMap<Columns, usize>,
}

impl Tables {
    /// Creates a new, empty collection of tables.
    pub const fn new() -> Self {
        Self {
            handles: Vec::new(),
            free_handles: Vec::new(),
            tables: Vec::new(),
            table_ids: BTreeMap::new(),
        }
    }

    /// Returns the metadata for the specified handle, or None if the handle is outdated.
    fn metadata(&self, handle: Handle) -> Option<HandleMeta> {
        let meta = &self.handles[handle.index];
        if meta.generation == handle.generation {
            Some(*meta)
        } else {
            None
        }
    }

    /// Inserts a new entity with the specified fields, returning a handle to it.
    ///
    /// If a table with the specified fields does not exist, it will be created.
    pub fn insert_new<F: Fields>(&mut self, fields: F) -> Handle {
        let handle = self.new_handle();

        //2. Lookup the table, creating it if necessary
        let mut ids = F::ids();
        ids.sort();
        let table_index = self.get_or_create_table(&ids);

        // SAFETY: table_index is guaranteed to be valid by the code above.
        let table = unsafe { self.tables.get_unchecked_mut(table_index) };
        let row = table.handles.len();

        if row == table.capacity() {
            table.grow()
        }

        table.handles.push(handle.index);
        fields.add_fields_to_table(row, table);

        self.handles[handle.index].table_index = table_index;
        self.handles[handle.index].row = row;

        handle
    }

    /// Creates a new handle, reusing a freed handle if possible.
    fn new_handle(&mut self) -> Handle {
        if let Some(index) = self.free_handles.pop() {
            Handle {
                index,
                generation: self.handles[index].generation,
            }
        } else {
            let index = self.handles.len();
            self.handles.push(HandleMeta {
                generation: 0,
                table_index: 0,
                row: 0,
            });
            Handle {
                index,
                generation: 0,
            }
        }
    }

    /// Adds the specified field(s) to the handle, moving it to a new table if necessary.
    pub fn add_fields<F: Fields>(&mut self, handle: Handle, fields: F) {
        let Some(meta) = self.metadata(handle) else {
            return;
        };

        // Get the table index for the new set of fields. If it doesn't exist, we create it based off the old table.
        let mut ids = F::ids()
            .iter()
            .chain(self.tables[meta.table_index].columns.keys())
            .copied()
            .collect::<Vec<_>>();
        ids.sort();

        let table_index = self.get_or_create_table(&ids);

        // Copy fields to the new table
        let (old, new) = self.get_2_tables_mut(meta.table_index, table_index);
        old.move_row_to(meta.row, new, ids.as_ref());

        // Add the new fields to the new table
        fields.add_fields_to_table(new.handles.len() - 1, new);

        let row = new.handles.len() - 1;
        // Update the handle metadata
        if let Some(index) = old.handles.get(meta.row).cloned() {
            let to_update = &mut self.handles[index];
            to_update.row = meta.row;
        }
        self.handles[handle.index].table_index = table_index;
        self.handles[handle.index].row = row;
    }

    /// Removes the specified field(s) from the handle, moving it to a new table.
    pub fn remove_fields<F: Fields>(&mut self, handle: Handle) {
        let Some(meta) = self.metadata(handle) else {
            return;
        };

        let old = F::ids();
        let mut ids = self.tables[meta.table_index]
            .columns
            .keys()
            .filter(|id| !old.contains(id))
            .copied()
            .collect::<Vec<_>>();
        ids.sort();

        let table_index = self.get_or_create_table(&ids);

        // Copy fields to the new table
        let (old, new) = self.get_2_tables_mut(meta.table_index, table_index);
        old.move_row_to(meta.row, new, ids.as_ref());

        let row = new.handles.len() - 1;

        // Update the handle metadata
        if let Some(index) = old.handles.get(meta.row).cloned() {
            let to_update = &mut self.handles[index];
            to_update.row = meta.row;
        }
        // self.apply_row_move(row_move);
        self.handles[handle.index].table_index = table_index;
        self.handles[handle.index].row = row;
    }

    /// Removes the specified handle and all its associated data from the tables.
    pub fn remove(&mut self, handle: Handle) {
        let Some(meta) = self.metadata(handle) else {
            return;
        };

        let idx = self.tables[meta.table_index].handles.len().checked_sub(1);
        self.tables[meta.table_index].swap_remove(meta.row);

        // Update the removed handle's metadata
        self.handles[handle.index].generation += 1;
        self.free_handles.push(handle.index);

        // A swap occurred, so we need to updated the moved handle's metadata
        if let Some(idx) = idx {
            self.handles[idx].row = meta.row;
        }
    }

    /// Returns the index of the table that contains the specified fields, creating it if necessary.
    fn get_or_create_table(&mut self, fields: &[TypeId]) -> usize {
        self.table_ids.get(fields).copied().unwrap_or_else(|| {
            // SAFETY: hardcoded `4` is non-zero.
            let table = unsafe { Table::with_capacity(NonZeroUsize::new_unchecked(4)) };
            let table_idx = self.tables.len();
            self.table_ids
                .insert(Columns(fields.to_vec().into_boxed_slice()), table_idx);
            self.tables.push(table);
            table_idx
        })
    }

    /// Returns mutable references to two different tables.
    ///
    /// This is used to move rows between tables when fields are added or removed from a handle.
    fn get_2_tables_mut(&mut self, a: usize, b: usize) -> (&mut Table, &mut Table) {
        debug_assert!(a != b);
        if a < b {
            let (left, right) = self.tables.split_at_mut(b);
            (&mut left[a], &mut right[0])
        } else {
            let (left, right) = self.tables.split_at_mut(a);
            (&mut right[0], &mut left[b])
        }
    }
}

impl Default for Tables {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for Tables {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Tables").finish()
    }
}

/// A type-erased table of data where each column is a different type.
///
/// Conceptually, this table represents the layout of a struct, where each column would be a field in the struct, and
/// each row would be an instance of the struct. In memory, however, the data is stored by lists of fields (columns)
/// rather than lists of structs (rows). This is a more cache-friendly way to operate on data.
///
/// See [Tables] for a collection of tables, and how it manages the layout of each table and moves rows between them as
/// columns are added or removed from an entity
///
/// ## Invariants
///
/// - The size and capacity of each column is always the same as `Table::handles`, ensuring that indexes into a column
///   are always valid for all columns.
pub struct Table {
    /// The handles in this table.
    handles: Vec<usize>,
    /// The columns in the table, searchable by their [TypeId].
    columns: BTreeMap<TypeId, Column>,
}

impl Table {
    /// Creates a new table with the specified capacity.
    ///
    /// The capacity must be non-zero, but no allocation is performed until the first insertion.
    fn with_capacity(capacity: NonZeroUsize) -> Self {
        Self {
            handles: Vec::with_capacity(capacity.get()),
            columns: BTreeMap::new(),
        }
    }

    /// Returns the capacity of this table.
    fn capacity(&self) -> usize {
        self.handles.capacity()
    }

    /// Returns true if this table contains the specified column.
    fn has_column(&self, column_id: TypeId) -> bool {
        self.columns.contains_key(&column_id)
    }

    /// Adds a new column to the table to store values with the specified layout.
    ///
    /// A new column can only be added if the table is empty (or in the process of being created, i.e. has 0 or 1
    /// rows). This is considered a logic error and will panic in debug builds.
    fn add_column(&mut self, column_id: TypeId, layout: Layout, drop_fn: fn(NonNull<u8>)) {
        debug_assert!(
            !self.columns.contains_key(&column_id),
            "Column already exists in table. A logic error has occurred."
        );
        debug_assert!(
            self.handles.len() < 2,
            "Can only add a new column on an empty table (has {} rows). This is a logic error.",
            self.handles.len()
        );
        self.columns.insert(
            column_id,
            Column::with_capacity(layout, self.handles.capacity(), drop_fn),
        );
    }

    /// Writes the value to the specified row, adding a new column if necessary.
    ///
    /// A new column can only be added if the table is empty (or in the process of being created, i.e. has 0 or 1
    /// rows). This is considered a logic error and will panic in debug builds.
    ///
    /// ## Panics
    ///
    /// - Panics if `row` is out of bounds.
    fn write_value_to_row<F: Field>(&mut self, row: usize, value: F) {
        let id = TypeId::of::<F>();
        if !self.has_column(id) {
            let layout = core::alloc::Layout::new::<F>();
            let drop = |ptr: core::ptr::NonNull<u8>| {
                // SAFETY: `ptr` is valid for both reads and writes, as it is owned by this struct, and this method
                //  takes self by mutable reference.
                // SAFETY: `ptr` is properly aligned by the nature of `Column`'s grow method using the same layout.
                // SAFETY: `ptr` is is non-null by the nature of `NonNull` ownership.
                // SAFETY: `ptr` is valid for dropping by the nature of this structs invariants.
                unsafe { ptr.cast::<F>().drop_in_place() };
            };
            self.add_column(id, layout, drop);
        }

        let data = core::mem::ManuallyDrop::new(value);
        let ptr = core::ptr::NonNull::from_ref(&data).cast::<u8>();

        // SAFETY: `value` is the correct type for the column by the nature of the TypeId lookup above.
        // SAFETY: `value` is wrapped in a ManuallyDrop, so it will not be dropped after this call.
        unsafe { self.write_value_to_column_and_row(id, row, ptr) };
    }

    /// Writes the value to the specified column and row.
    ///
    /// ## Safety
    ///
    /// - value must point to a valid instance of the type represented by column_id.
    /// - value must not have it's `drop` method called after this call, as this method takes ownership of the value.
    unsafe fn write_value_to_column_and_row(
        &mut self,
        column_id: TypeId,
        row: usize,
        value: NonNull<u8>,
    ) {
        #[cold]
        fn column_assert_failed(id: TypeId) -> ! {
            panic!("Table does not contain column with id {id:?}");
        }

        if !self.has_column(column_id) {
            column_assert_failed(column_id);
        }

        if row >= self.handles.len() {
            Self::index_assert_failed(row, self.handles.len());
        }

        // SAFETY: `column_id` is validated to exist above
        let column = unsafe { self.columns.get_mut(&column_id).unwrap_unchecked() };

        // SAFETY: `row` is validated to be in bounds above
        // SAFETY: caller must uphold the safety contract for this method.
        unsafe { column.write(row, value) };
    }

    /// Removes the specified row from the table, swapping the last row into its place.
    ///
    /// ## Panics
    ///
    /// - Panics if `row` is out of bounds.
    fn swap_remove(&mut self, row: usize) {
        if row >= self.handles.len() {
            Self::index_assert_failed(row, self.handles.len());
        }

        let last = self.handles.len() - 1;
        for column in self.columns.values_mut() {
            // SAFETY: `row`` is validated in the bounds check above.
            // SAFETY: by the nature of the documented struct invariants, `last` is always a valid index.
            unsafe { column.swap(row, last) };

            // SAFETY: by nature of the documented struct invariants, `last` is always a valid index.
            unsafe { column.drop_row(last) };
        }

        self.handles.swap_remove(row);
    }

    // Moves the specified row to the target table, copying only the specified columns.
    //
    // The last row in `self` is swapped into the `row` position, and the row is removed from `self`. This function
    // will automatically grow the target table if necessary, as the row is always appended to the end of the target
    // table.
    //
    // ## Panics
    //
    // - Panics if `row` is out of bounds.
    fn move_row_to(&mut self, row: usize, target: &mut Table, columns: &[TypeId]) {
        if row >= self.handles.len() {
            Self::index_assert_failed(row, self.handles.len());
        }

        let target_row = target.handles.len();

        // Update the entity metadata in both tables.
        if target.handles.capacity() == target_row {
            target.grow();
        }

        target.handles.push(self.handles.swap_remove(row));

        // Calculate the last row index in self once, for the swap_remove operation
        let self_last_row = self.handles.len().saturating_sub(1);

        for (id, column) in self
            .columns
            .iter_mut()
            .filter(|(id, _)| columns.contains(id))
        {
            let target = target.columns.entry(*id).or_insert_with(|| {
                Column::with_capacity(
                    *column.layout(),
                    target.handles.capacity(),
                    *column.drop_fn(),
                )
            });

            // SAFETY: `row` is validated in the bounds check above. By the nature of the documented struct
            //  invariants, `target_row` is always a valid index in `target`.
            unsafe { column.move_row_to(row, target_row, target) };

            // SAFETY: by nature of the documented struct invariants, `self_last_row` is always a valid index.
            unsafe { column.swap(row, self_last_row) };
        }
    }

    /// Increases the capacity of the table and all of its columns.
    fn grow(&mut self) {
        let old_capacity = self.handles.capacity();

        // Use the Vec's growth strategy to determine the new capacity
        self.handles.reserve(1);

        for column in self.columns.values_mut() {
            // SAFETY: `old_capacity` is the correct capacity by the nature of the documented struct invariants.
            unsafe { column.grow(old_capacity, self.handles.capacity()) };
        }
    }

    #[cold]
    /// A helper function for panicking on out-of-bounds access, specified to be on the cold path.
    fn index_assert_failed(index: usize, len: usize) -> ! {
        panic!("index (is {index}) should be < len (is {len})");
    }
}

impl Drop for Table {
    fn drop(&mut self) {
        for column in self.columns.values_mut() {
            unsafe { column.drop(self.handles.len(), self.handles.capacity()) };
        }
    }
}

/// A column in a Table.
///
/// This is a low-level representation of a column, which stores the raw byte data and a bitmap indicating valid rows.
/// This struct is not responsible for knowing or managing it's own capacity or length, as that is the responsibility
/// of the Table that owns it, as it is expected that all columns in a table will have the same length and capacity.
///
/// ## Invariants
///
/// - This struct owns the underlying memory, and is thus valid for read and write access based on the mutability of
///   the struct itself in its method signatures.
struct Column {
    layout: Layout,
    data: NonNull<u8>,
    drop_fn: fn(NonNull<u8>),
}

impl Column {
    /// Creates a new column with the specified layout, drop function and initial capacity.
    fn with_capacity(layout: Layout, capacity: usize, drop_fn: fn(NonNull<u8>)) -> Self {
        let alloc_layout = layout.repeat(capacity).unwrap().0;
        let data = Global.allocate(alloc_layout).unwrap().cast();

        Self {
            layout,
            data,
            drop_fn,
        }
    }

    /// Returns the [Layout] of a single element in this column.
    fn layout(&self) -> &Layout {
        &self.layout
    }

    /// Returns the drop function for this column's type.
    fn drop_fn(&self) -> &fn(NonNull<u8>) {
        &self.drop_fn
    }

    /// Writes the value at the specified row.
    ///
    /// The interface of this function does not accurately reflect that this function expects to take ownership of the
    /// value. However, it does. Due to this, The caller must ensure that the value is not dropped after this call.
    ///
    /// ## Safety
    ///
    /// - The caller must ensure that `row` is a valid index in this column.
    /// - The caller must ensure that `value` points to a valid instance of the type represented by this column.
    /// - value must not have it's `drop` method called after this call, as this method takes ownership of the value.
    unsafe fn write(&mut self, row: usize, value: NonNull<u8>) {
        let size = self.layout.size();

        // SAFETY: the safety contract for `write` must be upheld by the caller.
        // SAFETY: self.get_mut(row) is guaranteed to be a valid pointer by nature of the documented struct invariants and
        //  the safety contract for `write`.
        unsafe {
            self.get_mut(row).copy_from_nonoverlapping(value, size);
        }
    }

    /// Grows the column's allocation to the new capacity.
    ///
    /// ## Safety
    ///
    /// - The caller must ensure that `old_capacity` is the same as `current_capacity`.
    /// - The caller must ensure that `new_capacity` is greater than `current_capacity`.
    unsafe fn grow(&mut self, current_capacity: usize, new_capacity: usize) {
        let old_layout = self.layout.repeat(current_capacity).unwrap().0;
        let new_layout = self.layout.repeat(new_capacity).unwrap().0;

        // SAFETY: self.data is guaranteed to be a valid pointer by nature of the documented struct invariants.
        // SAFETY: the safety contract for `grow` must be upheld by the caller, which ensures that calculated
        //  `old_layout` is the same layout that was used to allocate the memory, and that `new_layout` is larger than
        //  `old_layout`.
        self.data = unsafe {
            Global
                .grow(self.data, old_layout, new_layout)
                .unwrap()
                .cast()
        };
    }

    /// Copies the data at `index` in this column to `target_index` in the target column.
    ///
    /// ## Safety
    ///
    /// - The caller must ensure that `index` and `target_index` are both valid indices in their respective columns.
    #[inline(always)]
    unsafe fn move_row_to(&mut self, index: usize, target_index: usize, target: &mut Column) {
        // SAFETY: the safety contract for `move_row_to` must be upheld by the caller.
        // SAFETY: src / dst are always properly aligned as they are copied as `u8`s.
        unsafe {
            core::ptr::copy_nonoverlapping::<u8>(
                self.get(index).as_ptr(),
                target.get_mut(target_index).as_ptr(),
                self.layout.size(),
            );
        }
    }

    /// Swaps the data at `index` in this column with `target_index` in the target column.
    ///
    /// ## Safety
    ///
    /// - The caller must ensure that `index` and `target_index` are both valid indices in this column.
    #[inline(always)]
    unsafe fn swap(&mut self, index: usize, target_index: usize) {
        if index == target_index {
            return;
        }
        // SAFETY: the safety contract for `swap` must be upheld by the caller.
        // SAFETY: `index` / `target_index` are verified to be different, so the pointers cannot overlap by nature of
        //  the `get` and `get_mut` methods.
        // SAFETY: `src` / `dst` are always properly aligned as they are copied as `u8`s.
        unsafe {
            core::ptr::swap_nonoverlapping::<u8>(
                self.get(index).as_ptr(),
                self.get_mut(target_index).as_ptr(),
                self.layout.size(),
            );
        }
    }

    /// Returns a pointer to the data at the specified index.
    ///
    /// ## Safety
    ///
    /// - The caller must ensure that `index` is a valid index in this column.
    #[inline(always)]
    unsafe fn get(&self, index: usize) -> NonNull<u8> {
        // SAFETY: `count` cannot go out of bounds so long as the caller upholds the safety contract of `get`.
        unsafe { self.data.byte_add(index * self.layout.size()) }
    }

    /// Returns a pointer to the data at the specified index.
    ///
    /// ## Safety
    ///
    /// - The caller must ensure that `index` is a valid index in this column.
    #[inline(always)]
    unsafe fn get_mut(&mut self, index: usize) -> NonNull<u8> {
        // SAFETY: `count` cannot go out of bounds so long as the caller upholds the safety contract of `get_mut`.
        unsafe { self.data.byte_add(index * self.layout.size()) }
    }

    /// Calls the drop function for the specified row index.
    ///
    /// ## Safety
    ///
    /// - The caller must ensure that `index` is a valid index in this column.
    unsafe fn drop_row(&mut self, index: usize) {
        // SAFETY: the safety contract for `drop_row` must be upheld by the caller.
        let ptr = unsafe { self.get(index) };
        (self.drop_fn)(ptr);
    }

    /// Calls the drop function on all valid rows, then deallocates the column's memory.
    ///
    /// ## Safety
    ///
    /// - The caller must ensure that `length` is the number of valid rows in this column.
    /// - The caller must ensure that `capacity` is the total capacity of this column.
    unsafe fn drop(&mut self, length: usize, capacity: usize) {
        for i in 0..length {
            // SAFETY: the safety contract for `drop_row` must be upheld by the caller, which ensures that `i` is a
            //   valid index.
            unsafe { self.drop_row(i) };
        }

        let alloc_layout = self.layout.repeat(capacity).unwrap().0;

        // SAFETY: self.data is guaranteed to be a valid pointer by nature of the documented struct invariants.
        // SAFETY: the safety contract for `drop_row` must be upheld by the caller, which ensures that calculated
        //  `alloc_layout` is the same layout that was used to allocate the memory.
        unsafe { Global.deallocate(self.data, alloc_layout) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::field;

    use crate as patina_tables;

    pub fn sorted_ids<T: Fields>() -> Box<[TypeId]> {
        let mut ids = T::ids();
        ids.sort();
        ids
    }

    #[allow(dead_code)]
    struct A(u32);

    impl Field for A {}

    #[allow(dead_code)]
    struct B(u32);

    impl Field for B {}

    #[test]
    fn test_removing_entire_handle() {
        let mut tables = Tables::default();
        assert!(tables.tables.is_empty());

        // Insert handle and validate state
        let handle1 = tables.insert_new((A(1), B(2)));
        assert_eq!(handle1.index, 0);
        assert_eq!(tables.handles[handle1.index].table_index, 0);
        assert_eq!(tables.handles[handle1.index].row, 0);
        assert_eq!(
            tables.table_ids.get(sorted_ids::<(A, B)>().as_ref()),
            Some(&0)
        );

        // Insert another handle and validate state
        let handle2 = tables.insert_new((B(3), A(4)));
        assert_eq!(handle2.index, 1);
        assert!(tables.tables.len() == 1);
        assert!(tables.tables[0].handles.len() == 2);
        assert_eq!(tables.handles[handle1.index].table_index, 0);
        assert_eq!(tables.handles[handle1.index].row, 0);
        assert_eq!(tables.handles[handle2.index].table_index, 0);
        assert_eq!(tables.handles[handle2.index].row, 1);

        tables.remove(handle1);
        assert!(tables.tables.len() == 1);
        assert!(tables.tables[0].handles.len() == 1);
        assert_eq!(tables.handles[handle2.index].table_index, 0);
        assert_eq!(tables.handles[handle2.index].row, 0);

        tables.remove(handle2);
        assert!(tables.tables.len() == 1);
        assert!(tables.tables[0].handles.is_empty());
        assert_eq!(tables.free_handles.len(), 2);
    }

    #[test]
    fn different_ordered_fields_go_to_same_table() {
        let mut tables = Tables::new();
        assert!(tables.tables.is_empty());

        let handle1 = tables.insert_new((A(1), B(2)));
        assert_eq!(handle1.index, 0);
        let handle2 = tables.insert_new((B(3), A(4)));
        assert_eq!(handle2.index, 1);

        assert_eq!(
            tables.table_ids.get(sorted_ids::<(A, B)>().as_ref()),
            Some(&0)
        );
        assert!(tables.tables.len() == 1);
    }

    #[test]
    fn removing_row_reuses_handle_later_on() {
        let mut tables = Tables::new();

        let handle1 = tables.insert_new((A(1), B(2)));
        assert_eq!(handle1.index, 0);
        assert_eq!(tables.handles[handle1.index].table_index, 0);
        assert_eq!(tables.handles[handle1.index].row, 0);

        let handle2 = tables.insert_new((B(3), A(4)));
        assert_eq!(handle2.index, 1);
        assert_eq!(tables.handles[handle2.index].table_index, 0);
        assert_eq!(tables.handles[handle2.index].row, 1);

        let handle3 = tables.insert_new((A(5), B(6)));
        assert_eq!(handle3.index, 2);
        assert_eq!(tables.handles[handle3.index].table_index, 0);
        assert_eq!(tables.handles[handle3.index].row, 2);

        assert_eq!(
            tables.table_ids.get(sorted_ids::<(A, B)>().as_ref()),
            Some(&0)
        );

        tables.remove(handle2);
        assert_eq!(tables.free_handles.len(), 1);
        assert_eq!(tables.free_handles[0], handle2.index);

        let handle4 = tables.insert_new((A(7), B(8)));
        assert_eq!(handle4.index, handle2.index);
        assert_eq!(handle4.generation, handle2.generation + 1);
        assert_eq!(tables.free_handles.len(), 0);
    }

    #[test]
    fn test_add_fields_create_new_table() {
        // This test inserts 4 handles with only field A. Then, it adds field B to the second handle.
        // The expected result is that a new table is created whose columns are field A and B.
        // The second handle is moved to the new table and the 4th handle moves to 2nd handle's old position
        let mut tables = Tables::new();

        let handle1 = tables.insert_new(A(1));
        assert_eq!(tables.tables.len(), 1); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 1); // Check how many rows in the first table
        assert_eq!(tables.tables[0].columns.len(), 1); // Check how many columns in the first table

        assert_eq!(tables.table_ids.get(sorted_ids::<A>().as_ref()), Some(&0)); // Check the table id mapping is correct

        // Validate handle metadata
        assert_eq!(handle1.index, 0);
        assert_eq!(tables.handles[handle1.index].table_index, 0);
        assert_eq!(tables.handles[handle1.index].row, 0);

        let handle2 = tables.insert_new(A(2));
        assert_eq!(tables.tables.len(), 1); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 2); // Check how many rows in the first table
        assert_eq!(tables.tables[0].columns.len(), 1); // Check how many columns in the first table

        // Validate handle metadata
        assert_eq!(handle2.index, 1);
        assert_eq!(tables.handles[handle2.index].table_index, 0);
        assert_eq!(tables.handles[handle2.index].row, 1);

        let handle3 = tables.insert_new(A(3));
        assert_eq!(tables.tables.len(), 1); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 3); // Check how many rows in the first table
        assert_eq!(tables.tables[0].columns.len(), 1); // Check how many columns in the first table

        // Validate handle metadata
        assert_eq!(handle3.index, 2);
        assert_eq!(tables.handles[handle3.index].table_index, 0);
        assert_eq!(tables.handles[handle3.index].row, 2);

        let handle4 = tables.insert_new(A(4));
        assert_eq!(tables.tables.len(), 1); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 4); // Check how many rows in the first table
        assert_eq!(tables.tables[0].columns.len(), 1); // Check how many columns in the first table

        // Validate handle metadata
        assert_eq!(handle4.index, 3);
        assert_eq!(tables.handles[handle4.index].table_index, 0);
        assert_eq!(tables.handles[handle4.index].row, 3);

        tables.add_fields(handle2, B(3));
        assert_eq!(tables.tables.len(), 2); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 3); // Check how many rows in the first table
        assert_eq!(tables.tables[1].handles.len(), 1); // Check how many rows in the second table
        assert_eq!(tables.tables[0].columns.len(), 1); // Check how many columns in the first table
        assert_eq!(tables.tables[1].columns.len(), 2); // Check how many columns in the second table

        assert_eq!(
            tables.table_ids.get(sorted_ids::<(A, B)>().as_ref()),
            Some(&1)
        ); // Check the table id mapping is correct

        // Validate handle metadata
        assert_eq!(tables.handles[handle1.index].table_index, 0);
        assert_eq!(tables.handles[handle1.index].row, 0);
        assert_eq!(tables.handles[handle2.index].table_index, 1);
        assert_eq!(tables.handles[handle2.index].row, 0);
        assert_eq!(tables.handles[handle3.index].table_index, 0);
        assert_eq!(tables.handles[handle3.index].row, 2);
        assert_eq!(tables.handles[handle4.index].table_index, 0);
        assert_eq!(tables.handles[handle4.index].row, 1); // Swapped with handle2
    }

    #[test]
    fn test_add_fields_create_new_table_and_leave_old_table_empty() {
        let mut tables = Tables::new();

        let handle = tables.insert_new(A(1));
        assert_eq!(tables.tables.len(), 1);
        assert_eq!(tables.tables[0].handles.len(), 1);
        assert_eq!(tables.tables[0].columns.len(), 1);

        tables.add_fields(handle, B(2));
        assert_eq!(tables.tables.len(), 2);
        assert_eq!(tables.tables[0].handles.len(), 0);
        assert_eq!(tables.tables[0].columns.len(), 1);
        assert_eq!(tables.tables[1].handles.len(), 1);
        assert_eq!(tables.tables[1].columns.len(), 2);

        assert_eq!(
            tables.table_ids.get(sorted_ids::<(A, B)>().as_ref()),
            Some(&1)
        );

        // Validate handle metadata
        assert_eq!(tables.handles[handle.index].table_index, 1);
        assert_eq!(tables.handles[handle.index].row, 0);
    }

    #[test]
    fn test_all_fields_removed_moves_to_empty_table() {
        let mut tables = Tables::new();
        let handle = tables.insert_new(A(1));
        assert_eq!(tables.tables.len(), 1);
        assert_eq!(tables.tables[0].handles.len(), 1);
        assert_eq!(tables.tables[0].columns.len(), 1);
        assert_eq!(tables.table_ids.get(sorted_ids::<A>().as_ref()), Some(&0));

        tables.remove_fields::<A>(handle);
        assert_eq!(tables.tables.len(), 2);
        assert_eq!(tables.tables[0].handles.len(), 0);
        assert_eq!(tables.tables[0].columns.len(), 1);
        assert_eq!(tables.tables[1].handles.len(), 1);
        assert_eq!(tables.tables[1].columns.len(), 0);
        let ids: &[TypeId] = &[];
        assert_eq!(tables.table_ids.get(ids), Some(&1));
    }

    #[test]
    fn test_remove_multiple_fields_does_not_generate_intermediate_tables() {
        let mut tables = Tables::new();

        let handle = tables.insert_new((A(1), B(2)));
        assert_eq!(tables.tables.len(), 1);
        assert_eq!(tables.tables[0].handles.len(), 1);
        assert_eq!(tables.tables[0].columns.len(), 2);

        assert_eq!(
            tables.table_ids.get(sorted_ids::<(A, B)>().as_ref()),
            Some(&0)
        );

        tables.remove_fields::<(A, B)>(handle);
        assert_eq!(tables.tables.len(), 2);
        assert_eq!(tables.tables[0].handles.len(), 0);
        assert_eq!(tables.tables[0].columns.len(), 2);
        assert_eq!(tables.tables[1].handles.len(), 1);
        assert_eq!(tables.tables[1].columns.len(), 0);

        let ids: &[TypeId] = &[];
        assert_eq!(tables.table_ids.get(ids), Some(&1));
    }

    #[test]
    fn test_remove_field_create_new_table() {
        let mut tables = Tables::new();

        let handle1 = tables.insert_new((A(1), B(2)));
        assert_eq!(tables.tables.len(), 1); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 1); // Check how many rows in the first table
        assert_eq!(tables.tables[0].columns.len(), 2); // Check how many columns in the first table
        assert_eq!(
            tables.table_ids.get(sorted_ids::<(A, B)>().as_ref()),
            Some(&0)
        ); // Check the table id mapping is correct

        // Validate handle metadata
        assert_eq!(handle1.index, 0);
        assert_eq!(tables.handles[handle1.index].table_index, 0);
        assert_eq!(tables.handles[handle1.index].row, 0);

        let handle2 = tables.insert_new((A(3), B(4)));
        assert_eq!(tables.tables.len(), 1); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 2); // Check how many rows in the first table
        assert_eq!(tables.tables[0].columns.len(), 2); // Check how many columns in the first table

        // Validate handle metadata
        assert_eq!(handle2.index, 1);
        assert_eq!(tables.handles[handle2.index].table_index, 0);
        assert_eq!(tables.handles[handle2.index].row, 1);

        let handle3 = tables.insert_new((A(5), B(6)));
        assert_eq!(tables.tables.len(), 1); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 3); // Check how many rows in the first table
        assert_eq!(tables.tables[0].columns.len(), 2); // Check how many columns in the first table

        // Validate handle metadata
        assert_eq!(handle3.index, 2);
        assert_eq!(tables.handles[handle3.index].table_index, 0);
        assert_eq!(tables.handles[handle3.index].row, 2);

        let handle4 = tables.insert_new((A(7), B(8)));
        assert_eq!(tables.tables.len(), 1); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 4); // Check how many rows in the first table
        assert_eq!(tables.tables[0].columns.len(), 2); // Check how many columns in the first table

        // Validate handle metadata
        assert_eq!(handle4.index, 3);
        assert_eq!(tables.handles[handle4.index].table_index, 0);
        assert_eq!(tables.handles[handle4.index].row, 3);

        tables.remove_fields::<A>(handle2);
        assert_eq!(tables.tables.len(), 2); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 3); // Check how many rows in the first table
        assert_eq!(tables.tables[0].columns.len(), 2); // Check how many columns in the first table
        assert_eq!(tables.tables[1].handles.len(), 1); // Check how many rows in the second table
        assert_eq!(tables.tables[1].columns.len(), 1); // Check how many columns in the second table
        assert_eq!(tables.table_ids.get(sorted_ids::<B>().as_ref()), Some(&1));

        // Validate handle metadata
        assert_eq!(tables.handles[handle1.index].table_index, 0);
        assert_eq!(tables.handles[handle1.index].row, 0);
        assert_eq!(tables.handles[handle2.index].table_index, 1);
        assert_eq!(tables.handles[handle2.index].row, 0);
        assert_eq!(tables.handles[handle3.index].table_index, 0);
        assert_eq!(tables.handles[handle3.index].row, 2);
        assert_eq!(tables.handles[handle4.index].table_index, 0);
        assert_eq!(tables.handles[handle4.index].row, 1); // Swapped with handle2

        tables.remove_fields::<(A, B)>(handle3);
        assert_eq!(tables.tables.len(), 3); // Check how many tables
        assert_eq!(tables.tables[0].handles.len(), 2); // Check how many rows in the first table
        assert_eq!(tables.tables[0].columns.len(), 2); // Check how many columns in the first table
        assert_eq!(tables.tables[1].handles.len(), 1); // Check how many rows in the second table
        assert_eq!(tables.tables[1].columns.len(), 1); // Check how many columns in the second table
        assert_eq!(tables.tables[2].handles.len(), 1); // Check how many rows in the third table
        assert_eq!(tables.tables[2].columns.len(), 0); // Check how many columns in the third table

        // Validate handle metadata
        assert_eq!(tables.handles[handle1.index].table_index, 0);
        assert_eq!(tables.handles[handle1.index].row, 0);
        assert_eq!(tables.handles[handle2.index].table_index, 1);
        assert_eq!(tables.handles[handle2.index].row, 0);
        assert_eq!(tables.handles[handle3.index].table_index, 2);
        assert_eq!(tables.handles[handle3.index].row, 0);
        assert_eq!(tables.handles[handle4.index].table_index, 0);
        assert_eq!(tables.handles[handle4.index].row, 1);
    }

    #[test]
    fn test_grow_table_grows_columns() {
        let mut tables = Tables::new();

        const COUNT: u32 = 1000;
        const COUNT_HALF: u32 = COUNT / 2;

        let mut handles = Vec::new();
        for i in 0..COUNT {
            handles.push(tables.insert_new((A(i), B(i * 2))));
        }

        for handle in &handles {
            // Validate handle metadata
            assert_eq!(tables.handles[handle.index].table_index, 0);
            assert_eq!(tables.handles[handle.index].row, handle.index);
        }

        for handle in handles.iter().skip(1).step_by(2) {
            tables.remove_fields::<A>(*handle);
        }

        for handle in &handles {
            assert_eq!(handle.index % 2, tables.handles[handle.index].table_index);
        }

        assert_eq!(tables.tables.len(), 2);
        assert_eq!(tables.tables[0].handles.len(), COUNT_HALF as usize);
        assert_eq!(tables.tables[1].handles.len(), COUNT_HALF as usize);
    }

    #[test]
    #[should_panic(expected = "Column already exists in table. A logic error has occurred.")]
    fn test_table_cannot_create_same_column_twice() {
        let mut table = Table::with_capacity(NonZeroUsize::new(4).unwrap());

        let column_id = TypeId::of::<A>();
        let layout = core::alloc::Layout::new::<A>();
        let drop_fn = |ptr: core::ptr::NonNull<u8>| {
            unsafe { ptr.cast::<A>().drop_in_place() };
        };

        table.add_column(column_id, layout, drop_fn);
        table.add_column(column_id, layout, drop_fn);
    }

    #[test]
    fn test_table_can_create_column_with_0_or_1_rows() {
        let mut table = Table::with_capacity(NonZeroUsize::new(4).unwrap());

        let column_id = TypeId::of::<A>();
        let layout = core::alloc::Layout::new::<A>();
        let drop_fn = |ptr: core::ptr::NonNull<u8>| {
            unsafe { ptr.cast::<A>().drop_in_place() };
        };

        // Adding a column while the table has 0 rows should work
        table.handles.push(0); // Push a dummy handle before adding the column. This is what Tables does.
        table.add_column(column_id, layout, drop_fn);

        // Write a value to the new column
        table.write_value_to_row(0, A(32));
        assert_eq!(table.handles.len(), 1);

        // Adding a column while the table has 1 row should work
        table.add_column(TypeId::of::<B>(), layout, drop_fn);
    }

    #[test]
    #[should_panic(
        expected = "Can only add a new column on an empty table (has 2 rows). This is a logic error."
    )]
    fn test_table_cannot_create_column_with_2_or_more_rows() {
        let mut table = Table::with_capacity(NonZeroUsize::new(4).unwrap());

        let column_id = TypeId::of::<A>();
        let layout = core::alloc::Layout::new::<A>();
        let drop_fn = |ptr: core::ptr::NonNull<u8>| {
            unsafe { ptr.cast::<A>().drop_in_place() };
        };

        // Adding a column while the table has 0 rows should work
        table.handles.push(0); // Push a dummy handle before adding the column. This is what Tables does.
        table.add_column(column_id, layout, drop_fn);

        // Write a value to the new column
        table.write_value_to_row(0, A(32));
        assert_eq!(table.handles.len(), 1);

        // Push another dummy handle to simulate having 2 rows
        table.handles.push(1);

        // Adding a column while the table has 2 rows should panic
        table.add_column(TypeId::of::<B>(), layout, drop_fn);
    }

    #[test]
    fn test_invalid_handle_returns_immediately() {
        let mut tables = Tables::new();

        let handle1 = tables.insert_new((A(1), B(2)));
        assert_eq!(handle1.index, 0);
        assert_eq!(tables.handles[handle1.index].table_index, 0);
        assert_eq!(tables.handles[handle1.index].row, 0);

        let handle2 = tables.insert_new((B(3), A(4)));
        assert_eq!(handle2.index, 1);
        assert_eq!(tables.handles[handle2.index].table_index, 0);
        assert_eq!(tables.handles[handle2.index].row, 1);

        tables.remove(handle1);

        // This should return immediately and not panic
        tables.add_fields(handle1, B(5));
        tables.remove_fields::<A>(handle1);
        tables.remove(handle1);
    }

    #[test]
    fn test_get_2_tables_mut() {
        let mut tables = Tables::new();

        tables.insert_new(A(1));
        tables.insert_new((A(3), B(4)));

        assert_eq!(tables.tables.len(), 2);

        // Test that splitting when a < b works
        {
            let (a, b) = tables.get_2_tables_mut(0, 1);
            assert_eq!(a.columns.len(), 1);
            assert_eq!(b.columns.len(), 2);
        }

        // Test that splitting when a > b works
        {
            let (a, b) = tables.get_2_tables_mut(1, 0);
            assert_eq!(a.columns.len(), 2);
            assert_eq!(b.columns.len(), 1);
        }
    }

    #[test]
    fn test_table_write_value_to_column_and_row_panic_in_bad_state() {
        extern crate std;
        use std::panic::catch_unwind;

        let mut table = Table::with_capacity(NonZeroUsize::new(4).unwrap());

        let value_to_write = A(32);
        let value = NonNull::from_ref(&value_to_write).cast();

        // Catch the panic when we try and write to a column that does not exist
        assert!(
            catch_unwind(move || {
                unsafe { table.write_value_to_column_and_row(TypeId::of::<A>(), 0, value) };
            })
            .is_err()
        );

        let mut table = Table::with_capacity(NonZeroUsize::new(4).unwrap());
        table.add_column(
            TypeId::of::<A>(),
            core::alloc::Layout::new::<A>(),
            |ptr: core::ptr::NonNull<u8>| {
                unsafe { ptr.cast::<A>().drop_in_place() };
            },
        );

        // Catch the panic when we try an out of bounds write
        assert!(
            catch_unwind(move || {
                unsafe { table.write_value_to_column_and_row(TypeId::of::<A>(), 1, value) };
            })
            .is_err()
        );
    }

    #[test]
    #[should_panic(expected = "index (is 1) should be < len (is 0)")]
    fn test_swap_remove_panics_on_out_of_bounds() {
        let mut table = Table::with_capacity(NonZeroUsize::new(4).unwrap());
        table.add_column(
            TypeId::of::<A>(),
            core::alloc::Layout::new::<A>(),
            |ptr: core::ptr::NonNull<u8>| {
                unsafe { ptr.cast::<A>().drop_in_place() };
            },
        );

        // This should panic
        table.swap_remove(1);
    }

    #[test]
    #[should_panic(expected = "index (is 1) should be < len (is 0)")]
    fn test_move_row_to_panics_on_out_of_bounds() {
        let mut table1 = Table::with_capacity(NonZeroUsize::new(4).unwrap());
        table1.add_column(
            TypeId::of::<A>(),
            core::alloc::Layout::new::<A>(),
            |ptr: core::ptr::NonNull<u8>| {
                unsafe { ptr.cast::<A>().drop_in_place() };
            },
        );

        let mut table2 = Table::with_capacity(NonZeroUsize::new(4).unwrap());
        table2.add_column(
            TypeId::of::<A>(),
            core::alloc::Layout::new::<A>(),
            |ptr: core::ptr::NonNull<u8>| {
                unsafe { ptr.cast::<A>().drop_in_place() };
            },
        );

        // This should panic
        table1.move_row_to(1, &mut table2, &[TypeId::of::<A>()]);
    }
}
