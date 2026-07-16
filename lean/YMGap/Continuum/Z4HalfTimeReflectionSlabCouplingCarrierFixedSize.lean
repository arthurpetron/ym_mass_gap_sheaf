/-
# Fixed-size arbitrary-cutoff slab carrier summation

At fixed colored-union size the geometric carrier injection is unchanged.
The two path-deleted backgrounds are now summed with the literal
coupling-parametric finite-cutoff activity.  Their Cartesian sum is exactly

  full compatible partition × corrected-slab support numerator.

This exact product is retained for later cancellation against the actual
normalized ambient and conditioned denominators.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierWeight
import YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierFixedSize
import YMGap.Continuum.Z4SpinSummedColoredSupportWeight

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierFixedSize

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierFixedSize
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierWeight
open YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingSwitchSummation
open YMGap.Continuum.Z4SpinSummedColoredSupportWeight
open YMGap.Continuum.Z4SpinSummedFaceActivityBound

local infix:50 " ≈ " => Q'.eqv

def couplingSpinSummedSlabConnectedCarrierTargetWeight
    (coupling : Q') (cutoff extent size : Nat)
    (carrier : SlabConnectedCarrier) : Q' :=
  anchorDecoratedFaceEnvelope ^ size *
    (couplingParametricKSupportFamilyActivity
        coupling cutoff (extent + 1) carrier.2.1 *
      couplingParametricKSupportFamilyActivity
        coupling cutoff (extent + 1) carrier.2.2)

def couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
    (coupling : Q') (cutoff extent size : Nat)
    (carrier : SlabRootedConnectedCarrier extent) : Q' :=
  couplingSpinSummedSlabConnectedCarrierTargetWeight
    coupling cutoff extent size carrier.2

def couplingSpinSummedSlabConnectedSourceSizeSum
    (coupling : Q') (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1)) (size : Nat) : Q' :=
  listQSum
    (fun entry : SlabConnectedSourceEntry extent roots predicate =>
      couplingSpinSummedSlabCylinderSourcePairWeight
        coupling cutoff entry.val)
    (slabConnectedSourceEntriesAtSize defaultRoot size)

theorem couplingSpinSummedSlabConnectedSourceSizeSum_le_carrierTarget
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (size : Nat) :
    couplingSpinSummedSlabConnectedSourceSizeSum
        (roots := roots) (predicate := predicate)
        coupling cutoff defaultRoot size ≤
      listQSum
        (couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
          coupling cutoff extent size)
        (slabConnectedCarrierTargetList extent roots size) := by
  unfold couplingSpinSummedSlabConnectedSourceSizeSum
  apply listQSum_le_of_injective
    (slabConnectedSourceEntriesAtSize defaultRoot size)
    (slabConnectedCarrierTargetList extent roots size)
    (fun entry : SlabConnectedSourceEntry extent roots predicate =>
      couplingSpinSummedSlabCylinderSourcePairWeight
        coupling cutoff entry.val)
    (couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
      coupling cutoff extent size)
    (slabRootedConnectedCarrier defaultRoot)
    (slabConnectedSourceEntriesAtSize_nodup defaultRoot size)
  · intro entry hentry
    have hsize :
        (slabConnectedCarrierSupport defaultRoot entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    exact slabRootedConnectedCarrier_mem_target
      defaultRoot hrootsSupported entry hsize
  · intro first _ second _ heq
    apply slabConnectedCarrier_injective defaultRoot first second
    exact congrArg (fun carrier => carrier.2) heq
  · intro entry hentry
    have hsize :
        (slabConnectedCarrierSupport defaultRoot entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    have hbound :=
      couplingSpinSummedSlabConnectedSourcePairWeight_le_support_background
        hcoupling hle cutoff defaultRoot entry
    rw [hsize] at hbound
    simpa [couplingSpinSummedSlabRootedConnectedCarrierTargetWeight,
      couplingSpinSummedSlabConnectedCarrierTargetWeight,
      slabRootedConnectedCarrier, slabConnectedCarrier,
      couplingSpinSummedSlabConnectedBackgroundPairWeight] using hbound
  · intro carrier _
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedFaceEnvelope
        anchorDecoratedFaceEnvelope_nonnegative size)
      (Q'.mul_nonneg _ _
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff (extent + 1) carrier.2.2.1)
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff (extent + 1) carrier.2.2.2))

theorem couplingSpinSummedSlabConnectedCarrierTargetSumAtRoot_eqv
    (coupling : Q') (cutoff extent : Nat)
    (root : CanonicalAtom (extent + 1)) (size : Nat) :
    listQSum
        (couplingSpinSummedSlabConnectedCarrierTargetWeight
          coupling cutoff extent size)
        (slabConnectedCarrierTargetListAtRoot extent root size) ≈
      spinSummedColoredPinnedSizeWeightSum (extent + 1)
          (slabCanonicalAtomFirstFace root) size *
        (couplingParametricKCompatibleSupportGasPartition
            coupling cutoff (extent + 1) *
          couplingParametricKCompatibleSupportEventNumerator
            coupling cutoff (extent + 1)
              (canonicalFamilySlabSupportedB extent)) := by
  have houter := listQSum_cartesian_product
    (fun _ : ColoredSupportPair => anchorDecoratedFaceEnvelope ^ size)
    (fun background : List (List Nat) × List (List Nat) =>
      couplingParametricKSupportFamilyActivity
          coupling cutoff (extent + 1) background.1 *
        couplingParametricKSupportFamilyActivity
          coupling cutoff (extent + 1) background.2)
    (canonicalColoredPinnedSizePairs (extent + 1)
      (slabCanonicalAtomFirstFace root) size)
    (cartesian (canonicalCompatibleAmbientFamilies (extent + 1))
      (canonicalSlabSupportedFamilies extent))
  have hinner := listQSum_cartesian_product
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (canonicalCompatibleAmbientFamilies (extent + 1))
    (canonicalSlabSupportedFamilies extent)
  unfold slabConnectedCarrierTargetListAtRoot
    couplingSpinSummedSlabConnectedCarrierTargetWeight
    spinSummedColoredPinnedSizeWeightSum
  refine Q'.eqv_trans _ _ _ houter ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ hinner ?_
  unfold couplingParametricKCompatibleSupportGasPartition
    couplingParametricKCompatibleSupportEventNumerator
    canonicalSlabSupportedFamilies
  exact Q'.eqv_refl _

private theorem couplingSpinSummedSlabRootedTargetMapSum_eqv
    (coupling : Q') (cutoff extent size : Nat)
    (root : CanonicalAtom (extent + 1)) :
    listQSum
        (couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
          coupling cutoff extent size)
        ((slabConnectedCarrierTargetListAtRoot extent root size).map
          (fun carrier => (root, carrier))) ≈
      listQSum
        (couplingSpinSummedSlabConnectedCarrierTargetWeight
          coupling cutoff extent size)
        (slabConnectedCarrierTargetListAtRoot extent root size) := by
  rw [listQSum_map]
  exact Q'.eqv_refl _

theorem couplingSpinSummedSlabConnectedCarrierTargetSum_eqv_rootSum
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1))) (size : Nat) :
    listQSum
        (couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
          coupling cutoff extent size)
        (slabConnectedCarrierTargetList extent roots size) ≈
      listQSum (fun root =>
        listQSum
          (couplingSpinSummedSlabConnectedCarrierTargetWeight
            coupling cutoff extent size)
          (slabConnectedCarrierTargetListAtRoot extent root size)) roots := by
  unfold slabConnectedCarrierTargetList
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
        coupling cutoff extent size)
      (fun root =>
        (slabConnectedCarrierTargetListAtRoot extent root size).map
          (fun carrier => (root, carrier))) roots) ?_
  exact listQSum_congr
    (fun root => couplingSpinSummedSlabRootedTargetMapSum_eqv
      coupling cutoff extent size root) roots

theorem couplingSpinSummedSlabConnectedCarrierTargetSum_le_geom_partition
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1))) (size : Nat) :
    listQSum
        (couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
          coupling cutoff extent size)
        (slabConnectedCarrierTargetList extent roots size) ≤
      Q'.ofNat roots.length *
        (anchorDecoratedEffectiveRatio ^ size *
          (couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (extent + 1) *
            couplingParametricKCompatibleSupportEventNumerator
              coupling cutoff (extent + 1)
                (canonicalFamilySlabSupportedB extent))) := by
  let partitionProduct :=
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (extent + 1) *
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent)
  let bound := anchorDecoratedEffectiveRatio ^ size * partitionProduct
  have hproduct0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff (extent + 1))
      (couplingParametricKCompatibleSupportEventNumerator_nonnegative
        hcoupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent))
  have hbound0 : (0 : Q') ≤ bound :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative size) hproduct0
  have hrootBound : ∀ root, root ∈ roots →
      listQSum
          (couplingSpinSummedSlabConnectedCarrierTargetWeight
            coupling cutoff extent size)
          (slabConnectedCarrierTargetListAtRoot extent root size) ≤
        bound := by
    intro root _
    have hfactor :=
      couplingSpinSummedSlabConnectedCarrierTargetSumAtRoot_eqv
        coupling cutoff extent root size
    have hcolored := Q'.mul_le_mul_of_nonneg_right _ _ _
      (spinSummedColoredPinnedSizeWeightSum_le_geom
        (extent + 1) (slabCanonicalAtomFirstFace root) size)
      hproduct0
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hcolored
  have hrootSum := listQSum_le_length_mul
    (fun root => listQSum
      (couplingSpinSummedSlabConnectedCarrierTargetWeight
        coupling cutoff extent size)
      (slabConnectedCarrierTargetListAtRoot extent root size))
    hbound0 roots hrootBound
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingSpinSummedSlabConnectedCarrierTargetSum_eqv_rootSum
        coupling cutoff extent roots size))
    hrootSum

theorem couplingSpinSummedSlabConnectedSourceSizeSum_le_geom_partition
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (size : Nat) :
    couplingSpinSummedSlabConnectedSourceSizeSum
        (roots := roots) (predicate := predicate)
        coupling cutoff defaultRoot size ≤
      Q'.ofNat roots.length *
        (anchorDecoratedEffectiveRatio ^ size *
          (couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (extent + 1) *
            couplingParametricKCompatibleSupportEventNumerator
              coupling cutoff (extent + 1)
                (canonicalFamilySlabSupportedB extent))) :=
  Q'.le_trans' _ _ _
    (couplingSpinSummedSlabConnectedSourceSizeSum_le_carrierTarget
      hcoupling hle cutoff defaultRoot hrootsSupported size)
    (couplingSpinSummedSlabConnectedCarrierTargetSum_le_geom_partition
      hcoupling cutoff extent roots size)

#print axioms couplingSpinSummedSlabConnectedSourceSizeSum_le_carrierTarget
#print axioms couplingSpinSummedSlabConnectedCarrierTargetSumAtRoot_eqv
#print axioms couplingSpinSummedSlabConnectedCarrierTargetSum_eqv_rootSum
#print axioms couplingSpinSummedSlabConnectedCarrierTargetSum_le_geom_partition
#print axioms couplingSpinSummedSlabConnectedSourceSizeSum_le_geom_partition

end YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierFixedSize
