/-
# Cutoff-uniform deletion of one pinned spin-summed polymer layer

The arbitrary-representation-cutoff compatible gas has the same canonical
polymer ambient list as the cutoff-one gas, but each connected support carries
its complete finite spin sum.  The previously proved decorated-face KP tail is
uniform in the representation cutoff.  Reindexing the marked layer by positive
support size and dropping the KP exponential therefore gives the same exact
one-half bound as at cutoff one.

This is the analytic input needed to reuse finite contact deletion and root
insertion in the simultaneous cutoff/volume cylinder state.
-/

import YMGap.Continuum.FiniteCompatibilityLayerDeletion
import YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
import YMGap.Continuum.Z4SpinSummedCompatibleGas

namespace YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

def parametricKCanonicalPinnedLayerActivity
    (cutoff n rootId : Nat) : Q' :=
  markedActivitySum (parametricKSupportActivity cutoff n)
    (canonicalContainsFaceB rootId) (canonicalSurfacePolymers n)

def parametricKCanonicalPinnedShiftedActivitySum
    (cutoff n rootId sizeFloor depth : Nat) : Q' :=
  finSum (fun offset =>
    parametricKPinnedSizeActivitySum cutoff n rootId
      (sizeFloor + offset)) depth

private theorem listQSum_range_eqv_finSum_local (value : Nat → Q') :
    ∀ cutoff : Nat,
      listQSum value (List.range cutoff) ≈ finSum value cutoff
  | 0 => Q'.eqv_refl 0
  | cutoff + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _ _ _
        (listQSum_append value (List.range cutoff) [cutoff])
        (Q'.add_eqv_congr'
          (listQSum_range_eqv_finSum_local value cutoff)
          (Q'.eqv_of_eq (Q'.add_zero' (value cutoff))))

theorem canonicalPinnedPositiveSizeLayers_parametricKActivity_eqv
    (cutoff n rootId : Nat) :
    listQSum (parametricKSupportActivity cutoff n)
        (canonicalPinnedPositiveSizeLayers n rootId) ≈
      parametricKCanonicalPinnedShiftedActivitySum cutoff n rootId 1
        (physicalFaceEdges n).length := by
  unfold canonicalPinnedPositiveSizeLayers
    parametricKCanonicalPinnedShiftedActivitySum
  exact Q'.eqv_trans _ _ _
    (listQSum_flatMap (parametricKSupportActivity cutoff n)
      (fun offset => canonicalPinnedSizePolymers n rootId (1 + offset))
      (List.range (physicalFaceEdges n).length))
    (listQSum_range_eqv_finSum_local
      (fun offset =>
        parametricKPinnedSizeActivitySum cutoff n rootId (1 + offset))
      (physicalFaceEdges n).length)

theorem parametricKCanonicalPinnedLayerActivity_le_shifted
    (cutoff n rootId : Nat) :
    parametricKCanonicalPinnedLayerActivity cutoff n rootId ≤
      parametricKCanonicalPinnedShiftedActivitySum cutoff n rootId 1
        (physicalFaceEdges n).length := by
  have hinjection :
      listQSum (parametricKSupportActivity cutoff n)
          (canonicalPinnedLayerPolymers n rootId) ≤
        listQSum (parametricKSupportActivity cutoff n)
          (canonicalPinnedPositiveSizeLayers n rootId) := by
    apply listQSum_le_of_injective
      (canonicalPinnedLayerPolymers n rootId)
      (canonicalPinnedPositiveSizeLayers n rootId)
      (parametricKSupportActivity cutoff n)
      (parametricKSupportActivity cutoff n)
      (fun polymer => polymer)
      (canonicalPinnedLayerPolymers_nodup n rootId)
    · intro polymer hpolymer
      exact canonicalPinnedLayer_mem_positiveSizeLayers hpolymer
    · intro left _ right _ heq
      exact heq
    · intro polymer _
      exact Q'.le_refl' _
    · intro polymer _
      exact parametricKSupportActivity_nonnegative cutoff n polymer
  unfold parametricKCanonicalPinnedLayerActivity markedActivitySum
  change listQSum (parametricKSupportActivity cutoff n)
      (canonicalPinnedLayerPolymers n rootId) ≤ _
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_of_eqv
      (canonicalPinnedPositiveSizeLayers_parametricKActivity_eqv
        cutoff n rootId))

private theorem one_le_eSurrogate_pow_local : ∀ size : Nat,
    (1 : Q') ≤ eSurrogate ^ size
  | 0 => Q'.le_refl' 1
  | size + 1 => by
      rw [Q'.pow_succ]
      have hpow0 : (0 : Q') ≤ eSurrogate ^ size :=
        Q'.pow_nonneg eSurrogate eSurrogate_nonneg size
      have hbase : (1 : Q') ≤ eSurrogate := by
        unfold eSurrogate
        decide
      have hmul : (1 : Q') * eSurrogate ^ size ≤
          eSurrogate * eSurrogate ^ size :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hpow0
      exact Q'.le_trans' _ _ _ (one_le_eSurrogate_pow_local size)
        (Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (Q'.one_mul_eqv (eSurrogate ^ size))) hmul)

theorem parametricKPinnedSizeActivitySum_le_weighted
    (cutoff n rootId size : Nat) :
    parametricKPinnedSizeActivitySum cutoff n rootId size ≤
      parametricKPinnedSizeWeightedActivity cutoff n rootId size := by
  unfold parametricKPinnedSizeWeightedActivity
  have hactivity0 :=
    parametricKPinnedSizeActivitySum_nonnegative cutoff n rootId size
  have hscaled :
      parametricKPinnedSizeActivitySum cutoff n rootId size * (1 : Q') ≤
        parametricKPinnedSizeActivitySum cutoff n rootId size *
          eSurrogate ^ size :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (one_le_eSurrogate_pow_local size) hactivity0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.mul_one_eqv
        (parametricKPinnedSizeActivitySum cutoff n rootId size)))
    hscaled

theorem parametricKCanonicalPinnedShiftedActivitySum_le_KPSum
    (cutoff n rootId sizeFloor depth : Nat) :
    parametricKCanonicalPinnedShiftedActivitySum
        cutoff n rootId sizeFloor depth ≤
      parametricKPinnedShiftedKPSum
        cutoff n rootId sizeFloor depth := by
  unfold parametricKCanonicalPinnedShiftedActivitySum
    parametricKPinnedShiftedKPSum
  exact CharacterTail.finSum_le_termwise _ _
    (fun offset => parametricKPinnedSizeActivitySum_le_weighted
      cutoff n rootId (sizeFloor + offset)) depth

theorem two_mul_anchorDecoratedEffectiveRatio_pow_one_le_half :
    Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ 1 ≤
      Q'.mkPos 1 2 (by decide) := by
  unfold anchorDecoratedEffectiveRatio anchorDecoratedFaceEnvelope
    animalK eSurrogate
  decide

/-- Uniform in representation cutoff, box, and pinned face. -/
theorem parametricKCanonicalPinnedLayerActivity_le_half
    (cutoff n rootId : Nat) :
    parametricKCanonicalPinnedLayerActivity cutoff n rootId ≤
      Q'.mkPos 1 2 (by decide) := by
  exact Q'.le_trans' _ _ _
    (parametricKCanonicalPinnedLayerActivity_le_shifted cutoff n rootId)
    (Q'.le_trans' _ _ _
      (parametricKCanonicalPinnedShiftedActivitySum_le_KPSum
        cutoff n rootId 1 (physicalFaceEdges n).length)
      (Q'.le_trans' _ _ _
        (parametricKPinnedShiftedKPSum_le_tail
          cutoff n rootId 1 (physicalFaceEdges n).length)
        two_mul_anchorDecoratedEffectiveRatio_pow_one_le_half))

end YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion.canonicalPinnedPositiveSizeLayers_parametricKActivity_eqv
#print axioms YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion.parametricKCanonicalPinnedLayerActivity_le_shifted
#print axioms YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion.parametricKPinnedSizeActivitySum_le_weighted
#print axioms YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion.parametricKCanonicalPinnedLayerActivity_le_half
