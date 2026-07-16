/-
# Cutoff-uniform spatial tails for spin-summed support activities

The geometric reach floor for canonical connected supports is independent of
their spin decorations.  Combining it with the cutoff-uniform support
activity and shifted KP estimates gives an exponential boundary tail for all
representation cutoffs simultaneously.
-/

import YMGap.Continuum.Z4SpinSummedSupportPartition
import YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

namespace YMGap.Continuum.Z4SpinSummedSupportBoundaryTail

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Connected supports reaching a distant shell -/

def parametricKPinnedReachSizeActivitySum
    (cutoff n rootId distance size : Nat) : Q' :=
  listQSum (parametricKSupportActivity cutoff n)
    (canonicalPinnedReachSizePolymers n rootId distance size)

theorem parametricKPinnedReachSizeActivitySum_nonnegative
    (cutoff n rootId distance size : Nat) :
    (0 : Q') ≤
      parametricKPinnedReachSizeActivitySum
        cutoff n rootId distance size := by
  unfold parametricKPinnedReachSizeActivitySum
  exact listQSum_nonnegative _
    (parametricKSupportActivity_nonnegative cutoff n) _

theorem parametricKPinnedReachSizeActivitySum_le_pinned
    (cutoff n rootId distance size : Nat) :
    parametricKPinnedReachSizeActivitySum
        cutoff n rootId distance size ≤
      parametricKPinnedSizeActivitySum cutoff n rootId size := by
  unfold parametricKPinnedReachSizeActivitySum
    canonicalPinnedReachSizePolymers
    parametricKPinnedSizeActivitySum
  exact listQSum_filter_le _ _
    (parametricKSupportActivity_nonnegative cutoff n)
    (canonicalPinnedSizePolymers n rootId size)

def parametricKPinnedReachSizeWeightedActivity
    (cutoff n rootId distance size : Nat) : Q' :=
  parametricKPinnedReachSizeActivitySum
      cutoff n rootId distance size *
    eSurrogate ^ size

theorem parametricKPinnedReachSizeWeightedActivity_nonnegative
    (cutoff n rootId distance size : Nat) :
    (0 : Q') ≤
      parametricKPinnedReachSizeWeightedActivity
        cutoff n rootId distance size := by
  unfold parametricKPinnedReachSizeWeightedActivity
  exact Q'.mul_nonneg _ _
    (parametricKPinnedReachSizeActivitySum_nonnegative
      cutoff n rootId distance size)
    (Q'.pow_nonneg eSurrogate eSurrogate_nonneg size)

theorem parametricKPinnedReachSizeWeightedActivity_le_pinned
    (cutoff n rootId distance size : Nat) :
    parametricKPinnedReachSizeWeightedActivity
        cutoff n rootId distance size ≤
      parametricKPinnedSizeWeightedActivity cutoff n rootId size := by
  unfold parametricKPinnedReachSizeWeightedActivity
    parametricKPinnedSizeWeightedActivity
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (parametricKPinnedReachSizeActivitySum_le_pinned
      cutoff n rootId distance size)
    (Q'.pow_nonneg eSurrogate eSurrogate_nonneg size)

theorem parametricKPinnedReachSizeWeightedActivity_eqv_zero_of_le
    (cutoff n rootId distance size : Nat) (hsize : size ≤ distance) :
    (parametricKPinnedReachSizeWeightedActivity
      cutoff n rootId distance size).eqv 0 := by
  unfold parametricKPinnedReachSizeWeightedActivity
    parametricKPinnedReachSizeActivitySum
  rw [canonicalPinnedReachSizePolymers_eq_nil_of_le
    n rootId distance size hsize]
  exact Q'.zero_mul_eqv _

theorem parametricKPinnedReachKPPrefix_eqv_zero
    (cutoff n rootId distance : Nat) :
    ∀ depth, depth ≤ distance + 1 →
      (finSum (fun size =>
        parametricKPinnedReachSizeWeightedActivity
          cutoff n rootId distance size) depth).eqv 0
  | 0, _ => Q'.eqv_refl 0
  | size + 1, hsize => by
      show (finSum (fun index =>
          parametricKPinnedReachSizeWeightedActivity
            cutoff n rootId distance index) size +
        parametricKPinnedReachSizeWeightedActivity
          cutoff n rootId distance size).eqv 0
      have hprefix := parametricKPinnedReachKPPrefix_eqv_zero
        cutoff n rootId distance size (by omega)
      have hlast :=
        parametricKPinnedReachSizeWeightedActivity_eqv_zero_of_le
          cutoff n rootId distance size (by omega)
      refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr' hprefix hlast
      · exact Q'.eqv_of_eq rfl

def parametricKPinnedReachShiftedKPSum
    (cutoff n rootId distance depth : Nat) : Q' :=
  finSum (fun offset =>
    parametricKPinnedReachSizeWeightedActivity
      cutoff n rootId distance (distance + 1 + offset)) depth

/-- Uniform in cutoff, volume, root, and truncation depth. -/
theorem parametricKPinnedReachShiftedKPSum_le_boundaryTail
    (cutoff n rootId distance depth : Nat) :
    parametricKPinnedReachShiftedKPSum
        cutoff n rootId distance depth ≤
      Q'.ofNat 2 *
        anchorDecoratedEffectiveRatio ^ (distance + 1) := by
  unfold parametricKPinnedReachShiftedKPSum
  have hsub :
      finSum (fun offset =>
          parametricKPinnedReachSizeWeightedActivity
            cutoff n rootId distance (distance + 1 + offset)) depth ≤
        finSum (fun offset =>
          parametricKPinnedSizeWeightedActivity cutoff n rootId
            (distance + 1 + offset)) depth :=
    CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        parametricKPinnedReachSizeWeightedActivity_le_pinned
          cutoff n rootId distance (distance + 1 + offset)) depth
  exact Q'.le_trans' _ _ _ hsub
    (parametricKPinnedShiftedKPSum_le_tail
      cutoff n rootId (distance + 1) depth)

def parametricKPinnedReachTruncatedKPSum
    (cutoff n rootId distance sizeCutoff : Nat) : Q' :=
  finSum (fun size =>
    parametricKPinnedReachSizeWeightedActivity
      cutoff n rootId distance size) sizeCutoff

theorem parametricKPinnedReachTruncatedKPSum_le_boundaryTail
    (cutoff n rootId distance sizeCutoff : Nat) :
    parametricKPinnedReachTruncatedKPSum
        cutoff n rootId distance sizeCutoff ≤
      Q'.ofNat 2 *
        anchorDecoratedEffectiveRatio ^ (distance + 1) := by
  let value : Nat → Q' := fun size =>
    parametricKPinnedReachSizeWeightedActivity
      cutoff n rootId distance size
  by_cases hcut : distance + 1 ≤ sizeCutoff
  · obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le hcut
    have hsplit := YMGap.Constructive.finSum_split
      value (distance + 1) depth
    have hprefix : (finSum value (distance + 1)).eqv 0 :=
      parametricKPinnedReachKPPrefix_eqv_zero
        cutoff n rootId distance (distance + 1) (Nat.le_refl _)
    have hcollapse :
        (finSum value (distance + 1) +
          finSum (fun offset =>
            value (distance + 1 + offset)) depth).eqv
          (finSum (fun offset =>
            value (distance + 1 + offset)) depth) := by
      refine Q'.eqv_trans _ ((0 : Q') +
          finSum (fun offset =>
            value (distance + 1 + offset)) depth) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ hprefix
      · exact Q'.eqv_of_eq (Q'.zero_add' _)
    have hwhole :
        (finSum value (distance + 1 + depth)).eqv
          (finSum (fun offset =>
            value (distance + 1 + offset)) depth) :=
      Q'.eqv_trans _ _ _ hsplit hcollapse
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hwhole)
      (parametricKPinnedReachShiftedKPSum_le_boundaryTail
        cutoff n rootId distance depth)
  · have hprefix : (finSum value sizeCutoff).eqv 0 :=
      parametricKPinnedReachKPPrefix_eqv_zero
        cutoff n rootId distance sizeCutoff (by omega)
    have htail0 : (0 : Q') ≤
        Q'.ofNat 2 *
          anchorDecoratedEffectiveRatio ^ (distance + 1) :=
      Q'.mul_nonneg _ _ (by decide)
        (Q'.pow_nonneg anchorDecoratedEffectiveRatio
          anchorDecoratedEffectiveRatio_nonnegative (distance + 1))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hprefix) htail0

/-! ## 2. Supports that leave an expanded finite box -/

def parametricKPinnedExitSizeActivitySum
    (cutoff n rootId inner distance size : Nat) : Q' :=
  listQSum (parametricKSupportActivity cutoff n)
    ((canonicalPinnedSizePolymers n rootId size).filter
      (canonicalPolymerExitsExpandedBoxB n inner distance))

theorem parametricKPinnedExitSizeActivitySum_le_reach
    {cutoff n rootId inner distance size : Nat}
    (hrootInner : boxPlaquetteAt n rootId ∈ boxPlaquettes inner) :
    parametricKPinnedExitSizeActivitySum
        cutoff n rootId inner distance size ≤
      parametricKPinnedReachSizeActivitySum
        cutoff n rootId (distance + 1) size := by
  unfold parametricKPinnedExitSizeActivitySum
    parametricKPinnedReachSizeActivitySum
    canonicalPinnedReachSizePolymers
  exact listQSum_filter_le_filter _ _ _
    (parametricKSupportActivity_nonnegative cutoff n)
    (fun polymer hexit =>
      canonicalPolymerExitsExpandedBoxB_implies_reaches
        hrootInner hexit)
    (canonicalPinnedSizePolymers n rootId size)

def parametricKPinnedExitSizeWeightedActivity
    (cutoff n rootId inner distance size : Nat) : Q' :=
  parametricKPinnedExitSizeActivitySum
      cutoff n rootId inner distance size *
    eSurrogate ^ size

theorem parametricKPinnedExitSizeWeightedActivity_le_reach
    {cutoff n rootId inner distance size : Nat}
    (hrootInner : boxPlaquetteAt n rootId ∈ boxPlaquettes inner) :
    parametricKPinnedExitSizeWeightedActivity
        cutoff n rootId inner distance size ≤
      parametricKPinnedReachSizeWeightedActivity
        cutoff n rootId (distance + 1) size := by
  unfold parametricKPinnedExitSizeWeightedActivity
    parametricKPinnedReachSizeWeightedActivity
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (parametricKPinnedExitSizeActivitySum_le_reach hrootInner)
    (Q'.pow_nonneg eSurrogate eSurrogate_nonneg size)

def parametricKPinnedExitTruncatedKPSum
    (cutoff n rootId inner distance sizeCutoff : Nat) : Q' :=
  finSum (fun size =>
    parametricKPinnedExitSizeWeightedActivity
      cutoff n rootId inner distance size) sizeCutoff

/-- A fixed inner root sees an exponentially small total activity from all
connected supports that leave the box expanded by `distance`, uniformly in
the representation cutoff and the ambient volume. -/
theorem parametricKPinnedExitTruncatedKPSum_le_boundaryTail
    {cutoff n rootId inner distance sizeCutoff : Nat}
    (hrootInner : boxPlaquetteAt n rootId ∈ boxPlaquettes inner) :
    parametricKPinnedExitTruncatedKPSum
        cutoff n rootId inner distance sizeCutoff ≤
      Q'.ofNat 2 *
        anchorDecoratedEffectiveRatio ^ (distance + 2) := by
  unfold parametricKPinnedExitTruncatedKPSum
  have hsum :
      finSum (fun size =>
          parametricKPinnedExitSizeWeightedActivity
            cutoff n rootId inner distance size) sizeCutoff ≤
        parametricKPinnedReachTruncatedKPSum
          cutoff n rootId (distance + 1) sizeCutoff :=
    CharacterTail.finSum_le_termwise _ _
      (fun size =>
        parametricKPinnedExitSizeWeightedActivity_le_reach hrootInner)
      sizeCutoff
  have htail := parametricKPinnedReachTruncatedKPSum_le_boundaryTail
    cutoff n rootId (distance + 1) sizeCutoff
  have hindex : distance + 1 + 1 = distance + 2 := by omega
  rw [hindex] at htail
  exact Q'.le_trans' _ _ _ hsum htail

end YMGap.Continuum.Z4SpinSummedSupportBoundaryTail

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedSupportBoundaryTail.parametricKPinnedReachSizeActivitySum_le_pinned
#print axioms YMGap.Continuum.Z4SpinSummedSupportBoundaryTail.parametricKPinnedReachTruncatedKPSum_le_boundaryTail
#print axioms YMGap.Continuum.Z4SpinSummedSupportBoundaryTail.parametricKPinnedExitSizeActivitySum_le_reach
#print axioms YMGap.Continuum.Z4SpinSummedSupportBoundaryTail.parametricKPinnedExitTruncatedKPSum_le_boundaryTail
