use std::borrow::{Borrow, BorrowMut};
use std::mem::{size_of, transmute};

use crate::poseidon::columns::{POSEIDON_SPONGE_RATE, POSEIDON_SPONGE_WIDTH};
use crate::util::{indices_arr, transmute_no_compile_time_size_checks};

pub(crate) const NUM_OUTPUTS: usize = 4;
#[repr(C)]
#[derive(Eq, PartialEq, Debug)]
pub(crate) struct PoseidonSpongeColumnsView<T: Copy> {
    /// 1 if this row represents a full input block, i.e. one in which each byte is an input byte,
    /// not a padding byte; 0 otherwise.
    pub is_full_input_block: T,

    /// The base address at which we will read the input block.
    pub context: T,
    pub segment: T,
    pub virt: T,

    /// The tiùestamp at which inputs should be read from memory.
    pub timestamp: T,

    /// The length of the original input.
    pub len: T,

    /// The number of input elements that have already been absorbed prior to this block.
    pub already_absorbed_elements: T,

    /// If this row represents a final block row, the `i`th entry should be 1 if the final chunk of
    /// input has length `i` (in other words if `len - already_absorbed == i`), otherwise 0.
    ///
    /// If this row represents a full input block, this should contain all 0s.
    pub is_final_input_len: [T; POSEIDON_SPONGE_RATE],

    /// The block being absorbed, which may contain input values and/or padding values.
    /// Since we are reading the input from MemoryStark, which holds 32-bit limbs,
    /// we assume that all our input elements are at most 32-bits long.
    pub block: [T; POSEIDON_SPONGE_RATE],

    /// The current state, taken as input of the current permutation.
    pub input_state: [T; POSEIDON_SPONGE_RATE + POSEIDON_SPONGE_WIDTH],
    /// The output of the permutation on `input_state`.
    pub updated_digest: [T; POSEIDON_SPONGE_WIDTH + POSEIDON_SPONGE_RATE],
}

pub(crate) const NUM_POSEIDON_SPONGE_COLUMNS: usize = size_of::<PoseidonSpongeColumnsView<u8>>();

impl<T: Copy> From<[T; NUM_POSEIDON_SPONGE_COLUMNS]> for PoseidonSpongeColumnsView<T> {
    fn from(value: [T; NUM_POSEIDON_SPONGE_COLUMNS]) -> Self {
        unsafe { transmute_no_compile_time_size_checks(value) }
    }
}

impl<T: Copy> From<PoseidonSpongeColumnsView<T>> for [T; NUM_POSEIDON_SPONGE_COLUMNS] {
    fn from(value: PoseidonSpongeColumnsView<T>) -> Self {
        unsafe { transmute_no_compile_time_size_checks(value) }
    }
}

impl<T: Copy> Borrow<PoseidonSpongeColumnsView<T>> for [T; NUM_POSEIDON_SPONGE_COLUMNS] {
    fn borrow(&self) -> &PoseidonSpongeColumnsView<T> {
        unsafe { transmute(self) }
    }
}

impl<T: Copy> BorrowMut<PoseidonSpongeColumnsView<T>> for [T; NUM_POSEIDON_SPONGE_COLUMNS] {
    fn borrow_mut(&mut self) -> &mut PoseidonSpongeColumnsView<T> {
        unsafe { transmute(self) }
    }
}

impl<T: Copy> Borrow<[T; NUM_POSEIDON_SPONGE_COLUMNS]> for PoseidonSpongeColumnsView<T> {
    fn borrow(&self) -> &[T; NUM_POSEIDON_SPONGE_COLUMNS] {
        unsafe { transmute(self) }
    }
}

impl<T: Copy> BorrowMut<[T; NUM_POSEIDON_SPONGE_COLUMNS]> for PoseidonSpongeColumnsView<T> {
    fn borrow_mut(&mut self) -> &mut [T; NUM_POSEIDON_SPONGE_COLUMNS] {
        unsafe { transmute(self) }
    }
}

impl<T: Copy + Default> Default for PoseidonSpongeColumnsView<T> {
    fn default() -> Self {
        [T::default(); NUM_POSEIDON_SPONGE_COLUMNS].into()
    }
}

const fn make_col_map() -> PoseidonSpongeColumnsView<usize> {
    let indices_arr = indices_arr::<NUM_POSEIDON_SPONGE_COLUMNS>();
    unsafe {
        transmute::<[usize; NUM_POSEIDON_SPONGE_COLUMNS], PoseidonSpongeColumnsView<usize>>(
            indices_arr,
        )
    }
}

pub(crate) const POSEIDON_SPONGE_COL_MAP: PoseidonSpongeColumnsView<usize> = make_col_map();
