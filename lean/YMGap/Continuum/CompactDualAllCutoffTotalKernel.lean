/-
# A total whole-slab recoupling kernel at every positive cutoff

The globally link-glued raw recoupling row is already defined for an arbitrary
fine representation cutoff, and `SlabScalePair.coarse_cutoff` records the
lossless target cutoff `4 * fine.cutoff`.  The previous total-kernel
construction specialized to cutoff one because positivity of the fine Gibbs
term was used to prove that every physical row had a positive recoupling
partition.

This module separates totality from that coherence theorem.  For any positive
fine cutoff it computes the literal raw-row partition.  If both the fine Gibbs
term and this partition are strictly positive, structural finite search
selects a positive coarse target and the row is the exact normalized
whole-slab recoupling law.  Otherwise the existing reflection-fixed stochastic
completion is used.  Thus no positive row is silently asserted coherent.

At cutoff one the established surface-closure theorem makes the raw partition
positive on every positive physical row, and the new kernel agrees pointwise
with the existing cutoff-one kernel.  At higher cutoffs the positive-Gibbs,
zero-raw-partition branch is a visible analytic defect, not an axiom.

The source-dependence field of `FiniteSlabKernel` is again witnessed on two
Gibbs-null singleton rows.  It certifies only that the total completion is not
constant and carries no physical mixing claim.

This constructs an arbitrary-cutoff finite block kernel.  It does not bound
the incoherent-row mass, the pushforward remainder, a posterior variance, a
spectral gap, a continuum limit, or the Clay target.

## Axiom gate

Finite search, exact rational algebra, and the audited reflection theorems
only.  No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualCutoffOneTotalKernel
import YMGap.Continuum.FiniteBistochasticPositiveTarget

namespace YMGap.Continuum.CompactDualAllCutoffTotalKernel

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabConditionalReflection
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.CompactDualWholeSlabRecouplingReflection
open YMGap.Continuum.FiniteBistochasticPositiveTarget
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal arbitrary-cutoff raw-row partition -/

/-- Sum of the exact whole-slab raw recoupling row over the complete lossless
coarse carrier.  Unlike `wholeSlabRecouplingPartition`, this definition does
not require a preselected positive witness. -/
def wholeSlabRawRowPartition
    (S : SlabScalePair) (fineState : EdgeLabelling) : Q' :=
  listQSum
    (wholeSlabRecouplingRawWeight S fineState)
    S.coarse.physicalLabellings

theorem wholeSlabRawRowPartition_nonnegative
    (S : SlabScalePair) (fineState : EdgeLabelling) :
    (0 : Q') <= wholeSlabRawRowPartition S fineState := by
  unfold wholeSlabRawRowPartition
  apply listQSum_nonnegative_on
  intro coarseState _hcoarse
  exact wholeSlabRecouplingRawWeight_nonnegative
    S fineState coarseState

/-- A positive literal raw-row partition constructively returns the coherent
source expected by the existing exact conditional kernel. -/
def coherentSlabRecouplingSourceOfRawPartitionPos
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S fineState) :
    CoherentSlabRecouplingSource S := by
  let selected := finitePositiveEntryOfSumPos
    (wholeSlabRecouplingRawWeight S fineState)
    (wholeSlabRecouplingRawWeight_nonnegative S fineState)
    S.coarse.physicalLabellings hpartition
  exact
    { fineState := fineState
      fine_mem := hfine
      coarseWitness := selected.item
      coarseWitness_mem := selected.item_mem
      coarseWitness_positive := selected.value_pos }

@[simp] theorem coherentSlabRecouplingSourceOfRawPartitionPos_fineState
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S fineState) :
    (coherentSlabRecouplingSourceOfRawPartitionPos
      S fineState hfine hpartition).fineState = fineState :=
  rfl

theorem coherentSlabRecouplingSourceOfRawPartitionPos_partition_eq
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S fineState) :
    wholeSlabRecouplingPartition
        (coherentSlabRecouplingSourceOfRawPartitionPos
          S fineState hfine hpartition) =
      wholeSlabRawRowPartition S fineState :=
  rfl

/-! ## 2. Reflection of the raw partition -/

/-- Reflection merely permutes the complete coarse target list, so positivity
of the unnormalized row partition is a reflection-invariant property. -/
theorem wholeSlabRawRowPartition_reflection
    (S : SlabScalePair) (fineState : EdgeLabelling) :
    wholeSlabRawRowPartition S
        (S.fine.reflectLabelling fineState) ≈
      wholeSlabRawRowPartition S fineState := by
  let reflectedWeight : EdgeLabelling → Q' :=
    wholeSlabRecouplingRawWeight S
      (S.fine.reflectLabelling fineState)
  let sourceWeight : EdgeLabelling → Q' :=
    wholeSlabRecouplingRawWeight S fineState
  unfold wholeSlabRawRowPartition
  change
    listQSum reflectedWeight S.coarse.physicalLabellings ≈
      listQSum sourceWeight S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum reflectedWeight
      (S.coarse.physicalLabellings.map
        S.coarse.reflectLabelling)) _ ?_ ?_
  · exact
      YMGap.Continuum.Z4CanonicalPolymerRange.listQSum_perm
        reflectedWeight
        (boundedSlabFaceLabellings_reflection_perm
          S.coarse.cutoff S.coarse.extent).symm
  · rw [listQSum_map]
    exact listQSum_congr_on _ _
      S.coarse.physicalLabellings
      (fun coarseState hcoarse =>
        wholeSlabRecouplingRawWeight_reflection S hcoarse)

theorem wholeSlabRawRowPartition_reflection_pos_iff
    (S : SlabScalePair) (fineState : EdgeLabelling) :
    (0 : Q') < wholeSlabRawRowPartition S
        (S.fine.reflectLabelling fineState) ↔
      (0 : Q') < wholeSlabRawRowPartition S fineState := by
  have hreflection :=
    wholeSlabRawRowPartition_reflection S fineState
  constructor
  · intro hpositive
    exact Q'.pos_of_lt_of_le hpositive
      (Q'.le_of_eqv hreflection)
  · intro hpositive
    exact Q'.pos_of_lt_of_le hpositive
      (Q'.ge_of_eqv hreflection)

/-! ## 3. The positive-cutoff null completion -/

theorem allCutoffNullCompletionKernel_row_normalized
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff)
    (fineState : EdgeLabelling) :
    listQSum (nullCompletionKernel S fineState)
        S.coarse.physicalLabellings ≈ 1 := by
  have hcoarseCutoff : 1 <= S.coarse.cutoff := by
    rw [S.coarse_cutoff]
    omega
  unfold nullCompletionKernel
  split
  · exact supportedDirac_slab_row_normalized S.coarse
      (fixedSingletonLabelling_mem S.coarse hcoarseCutoff)
  · exact supportedDirac_slab_row_normalized S.coarse
      (zeroEdgeLabelling_mem_slab S.coarse)

theorem allCutoffNullCompletionKernel_reflection
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff)
    {fineState coarseState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    nullCompletionKernel S
        (S.fine.reflectLabelling fineState)
        (S.coarse.reflectLabelling coarseState) =
      nullCompletionKernel S fineState coarseState := by
  have hfixedFineMem :
      fixedSingletonLabelling S.fine ∈ S.fine.physicalLabellings :=
    fixedSingletonLabelling_mem S.fine hfineCutoff
  have hsource :=
    supportedLabellingEqB_reflection_fixed S.fine
      hfine hfixedFineMem
      (fixedSingletonLabelling_reflection S.fine)
  have hcoarseCutoff : 1 <= S.coarse.cutoff := by
    rw [S.coarse_cutoff]
    omega
  unfold nullCompletionKernel
  rw [hsource]
  split
  · exact supportedDirac_reflection S.coarse
      (fixedSingletonLabelling_mem S.coarse hcoarseCutoff)
      hcoarse (fixedSingletonLabelling_reflection S.coarse)
  · exact supportedDirac_reflection S.coarse
      (zeroEdgeLabelling_mem_slab S.coarse)
      hcoarse (zeroEdgeLabelling_reflection S.coarse)

/-! ## 4. Exact recoupling where possible, explicit fallback otherwise -/

/-- The arbitrary-cutoff total row.  The second positivity test is the exact
coherence fence: a positive physical row with zero raw recoupling partition is
sent through the displayed fallback rather than assumed impossible. -/
def allCutoffWholeSlabKernel
    (S : SlabScalePair)
    (fineState coarseState : EdgeLabelling) : Q' :=
  if hbounded : slabCoordinatesBoundedB S.fine fineState = true then
    let restricted := restrictToSlabSupport S.fine fineState
    let hrestricted :=
      restrictToSlabSupport_mem_of_bounded S.fine hbounded
    if (0 : Q') < S.fine.physicalTerm restricted then
      if hpartition : (0 : Q') <
          wholeSlabRawRowPartition S restricted then
        wholeSlabRecouplingConditionalKernel
          (coherentSlabRecouplingSourceOfRawPartitionPos
            S restricted hrestricted hpartition)
          coarseState
      else
        nullCompletionKernel S restricted coarseState
    else
      nullCompletionKernel S restricted coarseState
  else
    nullCompletionKernel S fineState coarseState

theorem allCutoffWholeSlabKernel_eq_recoupling
    (S : SlabScalePair)
    {fineState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState)
    (hpartition : (0 : Q') <
      wholeSlabRawRowPartition S fineState)
    (coarseState : EdgeLabelling) :
    allCutoffWholeSlabKernel S fineState coarseState =
      wholeSlabRecouplingConditionalKernel
        (coherentSlabRecouplingSourceOfRawPartitionPos
          S fineState hfine hpartition)
        coarseState := by
  unfold allCutoffWholeSlabKernel
  rw [dif_pos (slabCoordinatesBoundedB_true_of_mem S.fine hfine)]
  have hrestrict := restrictToSlabSupport_eq_of_mem S.fine hfine
  simp only [hrestrict]
  rw [if_pos hpositive, dif_pos hpartition]

theorem allCutoffWholeSlabKernel_eq_null_of_not_physical_positive
    (S : SlabScalePair)
    {fineState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hnotPositive : ¬ (0 : Q') < S.fine.physicalTerm fineState)
    (coarseState : EdgeLabelling) :
    allCutoffWholeSlabKernel S fineState coarseState =
      nullCompletionKernel S fineState coarseState := by
  unfold allCutoffWholeSlabKernel
  rw [dif_pos (slabCoordinatesBoundedB_true_of_mem S.fine hfine)]
  have hrestrict := restrictToSlabSupport_eq_of_mem S.fine hfine
  simp only [hrestrict]
  rw [if_neg hnotPositive]

theorem allCutoffWholeSlabKernel_eq_null_of_raw_partition_not_positive
    (S : SlabScalePair)
    {fineState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState)
    (hnotPartition : ¬ (0 : Q') <
      wholeSlabRawRowPartition S fineState)
    (coarseState : EdgeLabelling) :
    allCutoffWholeSlabKernel S fineState coarseState =
      nullCompletionKernel S fineState coarseState := by
  unfold allCutoffWholeSlabKernel
  rw [dif_pos (slabCoordinatesBoundedB_true_of_mem S.fine hfine)]
  have hrestrict := restrictToSlabSupport_eq_of_mem S.fine hfine
  simp only [hrestrict]
  rw [if_pos hpositive, dif_neg hnotPartition]

/-! ## 5. Stochasticity and reflection -/

theorem allCutoffWholeSlabKernel_nonnegative
    (S : SlabScalePair)
    {fineState coarseState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (_hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    (0 : Q') <= allCutoffWholeSlabKernel S fineState coarseState := by
  by_cases hpositive :
      (0 : Q') < S.fine.physicalTerm fineState
  · by_cases hpartition :
        (0 : Q') < wholeSlabRawRowPartition S fineState
    · rw [allCutoffWholeSlabKernel_eq_recoupling
          S hfine hpositive hpartition coarseState]
      exact wholeSlabRecouplingConditionalKernel_nonnegative _ _
    · rw [allCutoffWholeSlabKernel_eq_null_of_raw_partition_not_positive
          S hfine hpositive hpartition coarseState]
      exact nullCompletionKernel_nonnegative S fineState coarseState
  · rw [allCutoffWholeSlabKernel_eq_null_of_not_physical_positive
        S hfine hpositive coarseState]
    exact nullCompletionKernel_nonnegative S fineState coarseState

theorem allCutoffWholeSlabKernel_row_normalized
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff)
    {fineState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings) :
    listQSum (allCutoffWholeSlabKernel S fineState)
        S.coarse.physicalLabellings ≈ 1 := by
  by_cases hpositive :
      (0 : Q') < S.fine.physicalTerm fineState
  · by_cases hpartition :
        (0 : Q') < wholeSlabRawRowPartition S fineState
    · refine Q'.eqv_trans _
          (listQSum
            (wholeSlabRecouplingConditionalKernel
              (coherentSlabRecouplingSourceOfRawPartitionPos
                S fineState hfine hpartition))
            S.coarse.physicalLabellings) _ ?_ ?_
      · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
          (fun coarseState _ => Q'.eqv_of_eq
            (allCutoffWholeSlabKernel_eq_recoupling
              S hfine hpositive hpartition coarseState))
      · exact wholeSlabRecouplingConditionalKernel_row_normalized _
    · refine Q'.eqv_trans _
          (listQSum (nullCompletionKernel S fineState)
            S.coarse.physicalLabellings) _ ?_ ?_
      · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
          (fun coarseState _ => Q'.eqv_of_eq
            (allCutoffWholeSlabKernel_eq_null_of_raw_partition_not_positive
              S hfine hpositive hpartition coarseState))
      · exact allCutoffNullCompletionKernel_row_normalized
          S hfineCutoff fineState
  · refine Q'.eqv_trans _
        (listQSum (nullCompletionKernel S fineState)
          S.coarse.physicalLabellings) _ ?_ ?_
    · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
        (fun coarseState _ => Q'.eqv_of_eq
          (allCutoffWholeSlabKernel_eq_null_of_not_physical_positive
            S hfine hpositive coarseState))
    · exact allCutoffNullCompletionKernel_row_normalized
        S hfineCutoff fineState

theorem allCutoffWholeSlabKernel_reflection
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff)
    {fineState coarseState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    allCutoffWholeSlabKernel S
        (S.fine.reflectLabelling fineState)
        (S.coarse.reflectLabelling coarseState) ≈
      allCutoffWholeSlabKernel S fineState coarseState := by
  let reflectedFine := S.fine.reflectLabelling fineState
  have hreflectedFine :
      reflectedFine ∈ S.fine.physicalLabellings :=
    reflectSupportedSlabFaceLabelling_mem hfine
  by_cases hpositive :
      (0 : Q') < S.fine.physicalTerm fineState
  · have hreflectedPositive :
        (0 : Q') < S.fine.physicalTerm reflectedFine :=
      (physicalTerm_reflection_positive_iff S.fine hfine).mpr
        hpositive
    by_cases hpartition :
        (0 : Q') < wholeSlabRawRowPartition S fineState
    · have hreflectedPartition :
          (0 : Q') < wholeSlabRawRowPartition S reflectedFine :=
        (wholeSlabRawRowPartition_reflection_pos_iff
          S fineState).mpr hpartition
      let source := coherentSlabRecouplingSourceOfRawPartitionPos
        S fineState hfine hpartition
      let reflectedSelected :=
        coherentSlabRecouplingSourceOfRawPartitionPos
          S reflectedFine hreflectedFine hreflectedPartition
      refine Q'.eqv_trans _
        (wholeSlabRecouplingConditionalKernel
          reflectedSelected
          (S.coarse.reflectLabelling coarseState)) _ ?_ ?_
      · exact Q'.eqv_of_eq
          (allCutoffWholeSlabKernel_eq_recoupling
            S hreflectedFine hreflectedPositive
              hreflectedPartition _)
      refine Q'.eqv_trans _
        (wholeSlabRecouplingConditionalKernel
          (reflectCoherentSlabRecouplingSource source)
          (S.coarse.reflectLabelling coarseState)) _ ?_ ?_
      · exact wholeSlabConditionalKernel_eq_of_fineState_eq
          reflectedSelected
          (reflectCoherentSlabRecouplingSource source) rfl _
      refine Q'.eqv_trans _
        (wholeSlabRecouplingConditionalKernel source coarseState) _ ?_ ?_
      · exact wholeSlabRecouplingConditionalKernel_reflection
          source hcoarse
      · exact Q'.eqv_symm (Q'.eqv_of_eq
          (allCutoffWholeSlabKernel_eq_recoupling
            S hfine hpositive hpartition coarseState))
    · have hreflectedNotPartition :
          ¬ (0 : Q') < wholeSlabRawRowPartition S reflectedFine := by
        intro hreflected
        exact hpartition
          ((wholeSlabRawRowPartition_reflection_pos_iff
            S fineState).mp hreflected)
      rw [allCutoffWholeSlabKernel_eq_null_of_raw_partition_not_positive
        S hreflectedFine hreflectedPositive hreflectedNotPartition]
      rw [allCutoffWholeSlabKernel_eq_null_of_raw_partition_not_positive
        S hfine hpositive hpartition]
      exact Q'.eqv_of_eq
        (allCutoffNullCompletionKernel_reflection
          S hfineCutoff hfine hcoarse)
  · have hreflectedNotPositive :
        ¬ (0 : Q') < S.fine.physicalTerm reflectedFine := by
      intro hreflected
      exact hpositive
        ((physicalTerm_reflection_positive_iff S.fine hfine).mp
          hreflected)
    rw [allCutoffWholeSlabKernel_eq_null_of_not_physical_positive
      S hreflectedFine hreflectedNotPositive]
    rw [allCutoffWholeSlabKernel_eq_null_of_not_physical_positive
      S hfine hpositive]
    exact Q'.eqv_of_eq
      (allCutoffNullCompletionKernel_reflection
        S hfineCutoff hfine hcoarse)

/-! ## 6. Source dependence and the packaged kernel -/

theorem allCutoffWholeSlabKernel_fixed_eq_one
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff) :
    allCutoffWholeSlabKernel S
        (fixedSingletonLabelling S.fine)
        (fixedSingletonLabelling S.coarse) = 1 := by
  have hfineMem := fixedSingletonLabelling_mem S.fine hfineCutoff
  rw [allCutoffWholeSlabKernel_eq_null_of_not_physical_positive
    S hfineMem (fixedSingletonPhysicalTerm_not_positive S.fine)]
  unfold nullCompletionKernel
  have hsource :
      supportedLabellingEqB S.fine.faceEdges
          (fixedSingletonLabelling S.fine)
          (fixedSingletonLabelling S.fine) = true :=
    supportedLabellingEqB_true_of_eq _ rfl
  rw [hsource]
  unfold supportedDirac
  have htarget :
      supportedLabellingEqB S.coarse.faceEdges
          (fixedSingletonLabelling S.coarse)
          (fixedSingletonLabelling S.coarse) = true :=
    supportedLabellingEqB_true_of_eq _ rfl
  rw [htarget]
  simp

theorem allCutoffWholeSlabKernel_bottom_eq_zero
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff) :
    allCutoffWholeSlabKernel S
        (bottomSingletonLabelling S.fine)
        (fixedSingletonLabelling S.coarse) = 0 := by
  have hfineMem := bottomSingletonLabelling_mem S.fine hfineCutoff
  have hfixedFineMem := fixedSingletonLabelling_mem S.fine hfineCutoff
  have hcoarseCutoff : 1 <= S.coarse.cutoff := by
    rw [S.coarse_cutoff]
    omega
  have hfixedCoarseMem :=
    fixedSingletonLabelling_mem S.coarse hcoarseCutoff
  have hvacuumCoarseMem := zeroEdgeLabelling_mem_slab S.coarse
  rw [allCutoffWholeSlabKernel_eq_null_of_not_physical_positive
    S hfineMem (bottomSingletonPhysicalTerm_not_positive S.fine)]
  unfold nullCompletionKernel
  have hsource :
      supportedLabellingEqB S.fine.faceEdges
          (bottomSingletonLabelling S.fine)
          (fixedSingletonLabelling S.fine) = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact bottomSingletonLabelling_ne_fixed S.fine
      ((supportedLabellingEqB_true_iff
        hfineMem hfixedFineMem).mp htrue)
  rw [hsource]
  unfold supportedDirac
  have htarget :
      supportedLabellingEqB S.coarse.faceEdges
          (fixedSingletonLabelling S.coarse)
          zeroEdgeLabelling = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact fixedSingletonLabelling_ne_zero S.coarse
      ((supportedLabellingEqB_true_iff
        hfixedCoarseMem hvacuumCoarseMem).mp htrue)
  rw [htarget]
  simp

/-- A total reflected stochastic kernel from cutoff `K` to the lossless cutoff
`4K`, for every displayed `K >= 1`. -/
def allCutoffWholeSlabFiniteKernel
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff) :
    S.FiniteSlabKernel where
  kernel := allCutoffWholeSlabKernel S
  nonnegative := by
    intro fineState coarseState hfine hcoarse
    exact allCutoffWholeSlabKernel_nonnegative S hfine hcoarse
  row_normalized := by
    intro fineState hfine
    exact allCutoffWholeSlabKernel_row_normalized
      S hfineCutoff hfine
  reflection_intertwines := by
    intro fineState coarseState hfine hcoarse
    exact allCutoffWholeSlabKernel_reflection
      S hfineCutoff hfine hcoarse
  source_dependent := by
    have hcoarseCutoff : 1 <= S.coarse.cutoff := by
      rw [S.coarse_cutoff]
      omega
    refine ⟨fixedSingletonLabelling S.fine,
      bottomSingletonLabelling S.fine,
      fixedSingletonLabelling S.coarse, ?_, ?_, ?_, ?_⟩
    · exact fixedSingletonLabelling_mem S.fine hfineCutoff
    · exact bottomSingletonLabelling_mem S.fine hfineCutoff
    · exact fixedSingletonLabelling_mem S.coarse hcoarseCutoff
    · rw [allCutoffWholeSlabKernel_fixed_eq_one S hfineCutoff]
      rw [allCutoffWholeSlabKernel_bottom_eq_zero S hfineCutoff]
      exact (by decide : ¬ ((1 : Q') ≈ 0))

/-! ## 7. Cutoff-one conservativity -/

theorem wholeSlabRawRowPartition_pos_of_cutoffOne_physical_pos
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {fineState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    (0 : Q') < wholeSlabRawRowPartition S fineState := by
  let source := positiveCoherentSource S hfineCutoff
    hcoarseCoupling fineState hfine hpositive
  exact wholeSlabRecouplingPartition_pos source

/-- On listed cutoff-one rows, the arbitrary-cutoff kernel is pointwise the
existing physical kernel.  The proof uses the cutoff-one surface theorem only
to eliminate the newly visible incoherent-row branch. -/
theorem allCutoffWholeSlabKernel_eqv_cutoffOne
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {fineState coarseState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings) :
    allCutoffWholeSlabKernel S fineState coarseState ≈
      cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
        fineState coarseState := by
  by_cases hpositive :
      (0 : Q') < S.fine.physicalTerm fineState
  · have hpartition :=
      wholeSlabRawRowPartition_pos_of_cutoffOne_physical_pos
        S hfineCutoff hcoarseCoupling hfine hpositive
    let selected := coherentSlabRecouplingSourceOfRawPartitionPos
      S fineState hfine hpartition
    let oldSource := positiveCoherentSource S hfineCutoff
      hcoarseCoupling fineState hfine hpositive
    refine Q'.eqv_trans _
      (wholeSlabRecouplingConditionalKernel selected coarseState) _
      (Q'.eqv_of_eq
        (allCutoffWholeSlabKernel_eq_recoupling
          S hfine hpositive hpartition coarseState)) ?_
    refine Q'.eqv_trans _
      (wholeSlabRecouplingConditionalKernel oldSource coarseState) _
      (wholeSlabConditionalKernel_eq_of_fineState_eq
        selected oldSource rfl coarseState) ?_
    exact Q'.eqv_symm
      (cutoffOneWholeSlabKernel_eq_positive
        S hfineCutoff hcoarseCoupling hfine hpositive coarseState)
  · rw [allCutoffWholeSlabKernel_eq_null_of_not_physical_positive
        S hfine hpositive]
    rw [cutoffOneWholeSlabKernel_eq_null
        S hfineCutoff hcoarseCoupling hfine hpositive]
    exact Q'.eqv_refl _

/-! ## 8. The exact higher-cutoff coherence defect -/

/-- Stationary mass of one listed fine row precisely when its physical Gibbs
term is positive but its complete recoupling raw partition is not. -/
def positiveIncoherentRecouplingRowWeight
    (S : SlabScalePair) (fineState : EdgeLabelling) : Q' :=
  if (0 : Q') < S.fine.physicalTerm fineState then
    if (0 : Q') < wholeSlabRawRowPartition S fineState then
      0
    else
      S.fine.normalizedMass fineState
  else
    0

/-- Total normalized fine Gibbs mass sent through the explicit fallback for
the sole physical reason that its exact raw recoupling row has no positive
normalization. -/
def positiveIncoherentRecouplingMass
    (S : SlabScalePair) : Q' :=
  listQSum
    (positiveIncoherentRecouplingRowWeight S)
    S.fine.physicalLabellings

theorem positiveIncoherentRecouplingRowWeight_nonnegative
    (S : SlabScalePair) (fineState : EdgeLabelling) :
    (0 : Q') <=
      positiveIncoherentRecouplingRowWeight S fineState := by
  unfold positiveIncoherentRecouplingRowWeight
  split
  · split
    · exact Q'.le_refl' 0
    · exact S.fine.normalizedMass_nonnegative fineState
  · exact Q'.le_refl' 0

theorem positiveIncoherentRecouplingMass_nonnegative
    (S : SlabScalePair) :
    (0 : Q') <= positiveIncoherentRecouplingMass S := by
  unfold positiveIncoherentRecouplingMass
  apply listQSum_nonnegative_on
  intro fineState _hfine
  exact positiveIncoherentRecouplingRowWeight_nonnegative S fineState

theorem positiveIncoherentRecouplingRowWeight_eq_zero_at_cutoffOne
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {fineState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings) :
    positiveIncoherentRecouplingRowWeight S fineState = 0 := by
  unfold positiveIncoherentRecouplingRowWeight
  by_cases hpositive :
      (0 : Q') < S.fine.physicalTerm fineState
  · rw [if_pos hpositive]
    have hpartition :=
      wholeSlabRawRowPartition_pos_of_cutoffOne_physical_pos
        S hfineCutoff hcoarseCoupling hfine hpositive
    rw [if_pos hpartition]
  · rw [if_neg hpositive]

/-- The newly exposed fallback sector is exactly empty at cutoff one.  At
higher cutoff this equality is deliberately not claimed. -/
theorem positiveIncoherentRecouplingMass_eqv_zero_at_cutoffOne
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    positiveIncoherentRecouplingMass S ≈ 0 := by
  unfold positiveIncoherentRecouplingMass
  refine Q'.eqv_trans _
    (listQSum (fun _fineState => (0 : Q'))
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.fine.physicalLabellings
      (fun fineState hfine => Q'.eqv_of_eq
        (positiveIncoherentRecouplingRowWeight_eq_zero_at_cutoffOne
          S hfineCutoff hcoarseCoupling hfine))
  · exact listQSum_zero S.fine.physicalLabellings

end YMGap.Continuum.CompactDualAllCutoffTotalKernel

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.CompactDualAllCutoffTotalKernel.coherentSlabRecouplingSourceOfRawPartitionPos
#print axioms
  YMGap.Continuum.CompactDualAllCutoffTotalKernel.wholeSlabRawRowPartition_reflection
#print axioms
  YMGap.Continuum.CompactDualAllCutoffTotalKernel.allCutoffWholeSlabKernel_row_normalized
#print axioms
  YMGap.Continuum.CompactDualAllCutoffTotalKernel.allCutoffWholeSlabKernel_reflection
#print axioms
  YMGap.Continuum.CompactDualAllCutoffTotalKernel.allCutoffWholeSlabFiniteKernel
#print axioms
  YMGap.Continuum.CompactDualAllCutoffTotalKernel.wholeSlabRawRowPartition_pos_of_cutoffOne_physical_pos
#print axioms
  YMGap.Continuum.CompactDualAllCutoffTotalKernel.allCutoffWholeSlabKernel_eqv_cutoffOne
#print axioms
  YMGap.Continuum.CompactDualAllCutoffTotalKernel.positiveIncoherentRecouplingMass_eqv_zero_at_cutoffOne
