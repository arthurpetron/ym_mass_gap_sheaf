/-
# Exact branchwise event transport for the enriched all-cutoff kernel

The enriched all-cutoff kernel has a useful exact dichotomy.  A positive fine
source with positive raw recoupling partition enters the coarse branch and is
transported by the genuine whole-slab recoupling row.  A positive source with
nonpositive raw partition enters the retained branch, where only its accepted
fine-intertwiner witness is resampled and its physical state is unchanged.

This module states that dichotomy at the level of arbitrary Boolean physical
observables.  The retained branch preserves every fine physical observable
exactly.  The coherent branch's enriched expectation is exactly the coarse
recoupling expectation, exposing that term as the only positive-source
observable-transport seam.

No smallness estimate for the coherent-branch mismatch, target covariance,
reflection identity, strict form bound, continuum limit, or Clay theorem is
asserted here.

## Axiom gate

Finite-sum algebra, the faithful physical-state code, and exact kernel branch
equations only.  No classical choice, placeholder, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetEvent

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetEvent
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Rational indicators and the enriched event moment -/

def rationalBoolIndicator (value : Bool) : Q' :=
  if value then 1 else 0

/-- A branch-explicit observable on the enriched carrier.  Its fine and
coarse physical predicates remain independent inputs. -/
def allCutoffRetainedBranchEventIndicator
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (target : AllCutoffRetainedTarget) : Q' :=
  match target with
  | Sum.inl coarsePhysical => rationalBoolIndicator (coarseEvent coarsePhysical)
  | Sum.inr retainedFine => rationalBoolIndicator (fineEvent retainedFine.1)

/-- Conditional expectation of a branch-explicit Boolean event in one
enriched kernel row. -/
def allCutoffRetainedFineIntertwinerEventMoment
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (fineEvent coarseEvent : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fun target =>
      allCutoffRetainedFineIntertwinerKernel S source target *
        allCutoffRetainedBranchEventIndicator fineEvent coarseEvent target)
    (allCutoffRetainedTargets S)

/-! ## 2. The retained branch preserves every fine physical event -/

private theorem retainedSamePhysicalStateKernel_indicator_term
    {D : SlabPhysicalData} (source : SlabPhysicalSourceEntry D)
    (hpositive : (0 : Q') < D.physicalTerm source.1)
    (event : EdgeLabelling → Bool)
    (target : EdgeLabelling × SlabFusionWitnessAssignment)
    (htarget : target ∈ slabExpandedFineSources D) :
    retainedSamePhysicalStateKernel source hpositive target *
        rationalBoolIndicator (event target.1) ≈
      retainedSamePhysicalStateKernel source hpositive target *
        rationalBoolIndicator (event source.1) := by
  by_cases hcode : slabPhysicalStateCode D target.1 =
      slabPhysicalStateCode D source.1
  · have hphysical : target.1 = source.1 :=
      slabPhysicalStateCode_injective_on_carrier
        (mem_slabExpandedFineSources_iff.mp htarget).1 source.2 hcode
    rw [hphysical]
    exact Q'.eqv_refl _
  · unfold retainedSamePhysicalStateKernel
    rw [if_neg hcode]
    exact Q'.eqv_trans _ 0 _
      (Q'.zero_mul_eqv _)
      (Q'.eqv_symm (Q'.zero_mul_eqv _))

/-- Resampling the accepted fine-intertwiner witness while retaining the
physical state preserves the expectation of every Boolean physical event. -/
theorem retainedSamePhysicalStateKernel_eventMoment
    {D : SlabPhysicalData} (source : SlabPhysicalSourceEntry D)
    (hpositive : (0 : Q') < D.physicalTerm source.1)
    (event : EdgeLabelling → Bool) :
    listQSum
        (fun target =>
          retainedSamePhysicalStateKernel source hpositive target *
            rationalBoolIndicator (event target.1))
        (slabExpandedFineSources D) ≈
      rationalBoolIndicator (event source.1) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        retainedSamePhysicalStateKernel source hpositive target *
          rationalBoolIndicator (event source.1))
      (slabExpandedFineSources D)) _ ?_ ?_
  · apply listQSum_congr_on _ _ (slabExpandedFineSources D)
    intro target htarget
    exact retainedSamePhysicalStateKernel_indicator_term
      source hpositive event target htarget
  refine Q'.eqv_trans _
    (listQSum (retainedSamePhysicalStateKernel source hpositive)
        (slabExpandedFineSources D) *
      rationalBoolIndicator (event source.1)) _ ?_ ?_
  · exact listQSum_mul_right
      (retainedSamePhysicalStateKernel source hpositive)
      (rationalBoolIndicator (event source.1))
      (slabExpandedFineSources D)
  refine Q'.eqv_trans _
    (1 * rationalBoolIndicator (event source.1)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (retainedSamePhysicalStateKernel_row_normalized source hpositive)
  · exact Q'.one_mul_eqv _

/-! ## 3. Exact positive-source branch dichotomy -/

/-- On a positive incoherent source, the full enriched event moment is
exactly the source's fine-event indicator; the coarse predicate is irrelevant. -/
theorem allCutoffRetainedFineIntertwinerEventMoment_eq_fine_of_incoherent
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hnotPartition : ¬ (0 : Q') < wholeSlabRawRowPartition S source.1)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    allCutoffRetainedFineIntertwinerEventMoment
        S source fineEvent coarseEvent ≈
      rationalBoolIndicator (fineEvent source.1) := by
  unfold allCutoffRetainedFineIntertwinerEventMoment
    allCutoffRetainedTargets
  refine Q'.eqv_trans _
    (listQSum
        (fun coarseState =>
          allCutoffRetainedFineIntertwinerKernel S source
              (.inl coarseState) *
            rationalBoolIndicator (coarseEvent coarseState))
        S.coarse.physicalLabellings +
      listQSum
        (fun retained =>
          allCutoffRetainedFineIntertwinerKernel S source
              (.inr retained) *
            rationalBoolIndicator (fineEvent retained.1))
        (slabExpandedFineSources S.fine)) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_append _ _ _) ?_
    rw [listQSum_map, listQSum_map]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (0 +
      listQSum
        (fun retained =>
          retainedSamePhysicalStateKernel source hpositive retained *
            rationalBoolIndicator (fineEvent retained.1))
        (slabExpandedFineSources S.fine)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (listQSum_congr_on _ _ S.coarse.physicalLabellings
          (fun coarseState _ => by
            rw [allCutoffRetainedFineIntertwinerKernel_coarse_zero_of_incoherent
              S source hpositive hnotPartition coarseState]
            exact Q'.zero_mul_eqv _))
        (listQSum_zero _))
      (listQSum_congr_on _ _ (slabExpandedFineSources S.fine)
        (fun retained _ => by
          rw [allCutoffRetainedFineIntertwinerKernel_eq_retained_of_incoherent
            S source hpositive hnotPartition retained]
          exact Q'.eqv_refl _))
  refine Q'.eqv_trans _
    (0 + rationalBoolIndicator (fineEvent source.1)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl 0)
      (retainedSamePhysicalStateKernel_eventMoment
        source hpositive fineEvent)
  · exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- On a positive coherent source, the enriched event moment is exactly the
coarse-event expectation in the genuine whole-slab recoupling row; the fine
predicate is irrelevant. -/
theorem allCutoffRetainedFineIntertwinerEventMoment_eq_coarse_of_coherent
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    allCutoffRetainedFineIntertwinerEventMoment
        S source fineEvent coarseEvent ≈
      listQSum
        (fun coarseState =>
          wholeSlabRecouplingConditionalKernel
              (coherentSlabRecouplingSourceOfRawPartitionPos
                S source.1 source.2 hpartition) coarseState *
            rationalBoolIndicator (coarseEvent coarseState))
        S.coarse.physicalLabellings := by
  unfold allCutoffRetainedFineIntertwinerEventMoment
    allCutoffRetainedTargets
  refine Q'.eqv_trans _
    (listQSum
        (fun coarseState =>
          allCutoffRetainedFineIntertwinerKernel S source
              (.inl coarseState) *
            rationalBoolIndicator (coarseEvent coarseState))
        S.coarse.physicalLabellings +
      listQSum
        (fun retained =>
          allCutoffRetainedFineIntertwinerKernel S source
              (.inr retained) *
            rationalBoolIndicator (fineEvent retained.1))
        (slabExpandedFineSources S.fine)) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_append _ _ _) ?_
    rw [listQSum_map, listQSum_map]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (listQSum
        (fun coarseState =>
          wholeSlabRecouplingConditionalKernel
              (coherentSlabRecouplingSourceOfRawPartitionPos
                S source.1 source.2 hpartition) coarseState *
            rationalBoolIndicator (coarseEvent coarseState))
        S.coarse.physicalLabellings + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (listQSum_congr_on _ _ S.coarse.physicalLabellings
        (fun coarseState _ => by
          rw [allCutoffRetainedFineIntertwinerKernel_eq_recoupling
            S source hpositive hpartition coarseState]
          exact Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _
        (listQSum_congr_on _ _ (slabExpandedFineSources S.fine)
          (fun retained _ => by
            rw [allCutoffRetainedFineIntertwinerKernel_retained_zero_of_coherent
              S source hpositive hpartition retained]
            exact Q'.zero_mul_eqv _))
        (listQSum_zero _))
  · exact Q'.eqv_of_eq (Q'.add_zero' _)

/-! ## Axiom audit -/

#print axioms retainedSamePhysicalStateKernel_eventMoment
#print axioms allCutoffRetainedFineIntertwinerEventMoment_eq_fine_of_incoherent
#print axioms allCutoffRetainedFineIntertwinerEventMoment_eq_coarse_of_coherent

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
