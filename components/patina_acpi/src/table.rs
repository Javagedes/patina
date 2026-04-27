use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, Unaligned};

use alloc::vec::Vec;

/// A wrapper around a set of bytes representing an ACPI table.
///
/// This structure supports three different data layouts for ACPI tables:
/// - Fixed: The table has a fixed size
/// - Dst: The table ends with a dynamically sized list of elements that can be manipulated at runtime
/// - DstDst: The table ends with a dynamically sized list of elements that can be manipulated at runtime, but the
///   elements themselves are also dynamically sized
///
/// Depending on the type of ACPI table as described above, certain operations are available on the table. As an
/// example, a `Dst` table implements `IntoIterator` for iterating over it's elements, along with other
/// [Vec] like operations.
///
/// ## Invariants
///
/// - A table table is guaranteed to be long enough to contain a valid ACPI table header due to all possible ways of
///   instantiation requiring, at a minimum, a valid ACPI table header with no way to remove bytes other than those
///   used to store elements of a `Dst` style ACPI table.
pub struct Table<T: AcpiTable + ?Sized> {
    pub(crate) _data: Vec<u8>,
    pub(crate) _marker: core::marker::PhantomData<T>,
}

impl<T: AcpiTable + ?Sized> TryFrom<Vec<u8>> for Table<T> {
    type Error = crate::error::AcpiError;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        // TODO: Run it through a `ref_from_bytes`
        Ok(Self { _data: value, _marker: core::marker::PhantomData })
    }
}

/// A trait representing an element in a dynamically sized ACPI table.
pub trait Element: IntoBytes + FromBytes + Immutable + KnownLayout + Unaligned {
    /// TODO
    const SIZE: usize = 0;
    /// TODO
    fn total_size(&self) -> usize;
}

/// A blanket implementation of `Element` for all sized types
impl<E: IntoBytes + FromBytes + Immutable + KnownLayout + Unaligned> Element for E {
    const SIZE: usize = core::mem::size_of::<E>();
    fn total_size(&self) -> usize {
        Self::SIZE
    }
}

/// TODO
///
/// ## SAFETY
///
/// - TODO
pub unsafe trait AcpiTable: FromBytes + IntoBytes + KnownLayout + Unaligned + Immutable {
    /// The ACPI table signature.
    const SIGNATURE: u32;

    /// TODO
    type Fields: IntoBytes + Immutable;
    /// TODO
    type Element: Element + ?Sized;
    /// TODO
    #[allow(private_bounds)]
    type Kind: TableKind;
}

/// A trait to specify the type of ACPI table this is
///
/// It is purposefully kept private so only our implementations can be used.
trait TableKind {}

#[doc(hidden)]
pub struct Fixed;

impl TableKind for Fixed {}

#[doc(hidden)]
pub struct Dst;

impl TableKind for Dst {}
