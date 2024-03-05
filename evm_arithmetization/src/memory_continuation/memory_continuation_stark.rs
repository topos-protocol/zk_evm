//! `ContinuationMemoryStark` is used to store the initial or the final values
//! in memory. It is checked against `MemoryStark` through a CTL.
//! This is used to ensure a continuation of the memory when proving
//! multiple segments of a single full transaction proof.
//! As such, `ContinuationMemoryStark` doesn't have any constraints.
use std::borrow::Borrow;
use std::cmp::max;
use std::iter::{self, once, repeat};
use std::marker::PhantomData;
use std::mem::size_of;

use itertools::Itertools;
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::Field;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::timed;
use plonky2::util::timing::TimingTree;
use plonky2::util::transpose;
use plonky2_util::ceil_div_usize;
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use starky::evaluation_frame::{StarkEvaluationFrame, StarkFrame};
use starky::lookup::{Column, Filter, Lookup};
use starky::stark::{Stark, StarkTable};

use super::columns::{value_limb, ADDR_CONTEXT, ADDR_SEGMENT, ADDR_VIRTUAL, FILTER, NUM_COLUMNS};
use crate::all_stark::EvmStarkFrame;
use crate::cpu::kernel::aggregator::KERNEL;
use crate::cpu::kernel::keccak_util::keccakf_u32s;
use crate::generation::MemBeforeValues;
use crate::memory::VALUE_LIMBS;
use crate::witness::memory::MemoryAddress;

/// Creates the vector of `Columns` corresponding to:
/// - the propagated address (context, segment, virt),
/// - the value in u32 limbs.
pub(crate) fn ctl_data<F: Field>() -> Vec<Column<F>> {
    let mut res = Column::singles([ADDR_CONTEXT, ADDR_SEGMENT, ADDR_VIRTUAL]).collect_vec();
    res.extend(Column::singles((0..8).map(value_limb)));
    res
}

/// CTL filter for memory operations.
pub(crate) fn ctl_filter<F: Field>() -> Filter<F> {
    Filter::new_simple(Column::single(FILTER))
}

/// Creates the vector of `Columns` corresponding to:
/// - the initialized address (context, segment, virt),
/// - the value in u32 limbs.
pub(crate) fn ctl_data_memory<F: Field>() -> Vec<Column<F>> {
    let mut res = vec![Column::constant(F::ZERO)]; // IS_READ
    res.extend(Column::singles([ADDR_CONTEXT, ADDR_SEGMENT, ADDR_VIRTUAL]).collect_vec());
    res.extend(Column::singles((0..8).map(value_limb)));
    res.push(Column::constant(F::ZERO)); // TIMESTAMP
    res
}

/// Convert `mem_before_values` to a vector of memory trace rows
pub(crate) fn mem_before_values_to_rows<F: Field>(
    mem_before_values: &MemBeforeValues,
) -> Vec<Vec<F>> {
    mem_before_values
        .iter()
        .map(|mem_data| {
            let mut row = vec![F::ZERO; NUM_COLUMNS];
            row[FILTER] = F::ONE;
            row[ADDR_CONTEXT] = F::from_canonical_usize(mem_data.0.context);
            row[ADDR_SEGMENT] = F::from_canonical_usize(mem_data.0.segment);
            row[ADDR_VIRTUAL] = F::from_canonical_usize(mem_data.0.virt);
            for j in 0..VALUE_LIMBS {
                row[j + 4] = F::from_canonical_u32((mem_data.1 >> (j * 32)).low_u32());
            }
            row
        })
        .collect()
}

/// Structure representing the `ContinuationMemory` STARK.
#[derive(Copy, Clone, Default)]
pub(crate) struct MemoryContinuationStark<F, const D: usize> {
    f: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> MemoryContinuationStark<F, D> {
    pub(crate) fn generate_trace(
        &self,
        final_values: Vec<Vec<F>>,
        timing: &mut TimingTree,
    ) -> Vec<PolynomialValues<F>> {
        // Set the trace to the `final_values` provided by `MemoryStark`.
        let mut rows = final_values;

        let num_rows = rows.len();
        let num_rows_padded = max(16, num_rows.next_power_of_two());
        for _ in num_rows..num_rows_padded {
            rows.push(vec![F::ZERO; NUM_COLUMNS]);
        }

        let cols = transpose(&rows);

        cols.into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> StarkTable for MemoryContinuationStark<F, D> {}
