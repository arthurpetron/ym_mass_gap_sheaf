/-
# Fixed-size arbitrary-cutoff two-block carrier summation

At a fixed colored-carrier size, the existing injective encoding records a
selected first-block root, the two color supports, and the two compatible
background families.  Give the color coordinate the decorated face envelope
and retain the exact coupling-parametric spin-summed activity on both
backgrounds.  Cartesian summation then yields the square of the same
arbitrary-cutoff partition function.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockCarrierFixedSize
import YMGap.Continuum.Z4CouplingParametricTwoBlockColoredCarrierWeight
import YMGap.Continuum.Z4SpinSummedColoredSupportWeight

namespace YMGap.Continuum.Z4CouplingParametricTwoBlockCarrierFixedSize

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockCarrierFixedSize
open YMGap.Continuum.Z4CanonicalTwoBlockColoredCarrierGeometry
open YMGap.Continuum.Z4CanonicalTwoBlockColoredPathCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricTwoBlockColoredCarrierWeight
open YMGap.Continuum.Z4CouplingParametricTwoBlockSwitchSummation
open YMGap.Continuum.Z4SpinSummedColoredSupportWeight
open YMGap.Continuum.Z4SpinSummedFaceActivityBound

local infix:50 " ≈ " => Q'.eqv

def couplingSpinSummedTwoBlockConnectedCarrierTargetWeight
    (coupling : Q') (cutoff n size : Nat)
    (carrier : ConnectedCarrier) : Q' :=
  anchorDecoratedFaceEnvelope ^ size *
    (couplingParametricKSupportFamilyActivity
        coupling cutoff n carrier.2.1 *
      couplingParametricKSupportFamilyActivity
        coupling cutoff n carrier.2.2)

theorem couplingSpinSummedTwoBlockConnectedCarrierTargetSum_eqv
    (coupling : Q') (cutoff n rootFace size : Nat) :
    listQSum
        (couplingSpinSummedTwoBlockConnectedCarrierTargetWeight
          coupling cutoff n size)
        (twoBlockConnectedCarrierTargetList n rootFace size) ≈
      spinSummedColoredPinnedSizeWeightSum n rootFace size *
        (couplingParametricKCompatibleSupportGasPartition
            coupling cutoff n *
          couplingParametricKCompatibleSupportGasPartition
            coupling cutoff n) := by
  have houter := listQSum_cartesian_product
    (fun _ : ColoredSupportPair => anchorDecoratedFaceEnvelope ^ size)
    (fun background : List (List Nat) × List (List Nat) =>
      couplingParametricKSupportFamilyActivity
          coupling cutoff n background.1 *
        couplingParametricKSupportFamilyActivity
          coupling cutoff n background.2)
    (canonicalColoredPinnedSizePairs n rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies n)
      (canonicalCompatibleAmbientFamilies n))
  have hinner := listQSum_cartesian_product
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (canonicalCompatibleAmbientFamilies n)
    (canonicalCompatibleAmbientFamilies n)
  unfold twoBlockConnectedCarrierTargetList
    couplingSpinSummedTwoBlockConnectedCarrierTargetWeight
    spinSummedColoredPinnedSizeWeightSum
  refine Q'.eqv_trans _ _ _ houter ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  unfold couplingParametricKCompatibleSupportGasPartition
  exact hinner

theorem couplingSpinSummedTwoBlockConnectedCarrierTargetSum_le_geom
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n rootFace size : Nat) :
    listQSum
        (couplingSpinSummedTwoBlockConnectedCarrierTargetWeight
          coupling cutoff n size)
        (twoBlockConnectedCarrierTargetList n rootFace size) ≤
      anchorDecoratedEffectiveRatio ^ size *
        (couplingParametricKCompatibleSupportGasPartition
            coupling cutoff n *
          couplingParametricKCompatibleSupportGasPartition
            coupling cutoff n) := by
  have hfactor :=
    couplingSpinSummedTwoBlockConnectedCarrierTargetSum_eqv
      coupling cutoff n rootFace size
  have hpartition0 : (0 : Q') ≤
      couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n *
        couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n :=
    Q'.mul_nonneg _ _
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff n)
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (spinSummedColoredPinnedSizeWeightSum_le_geom n rootFace size)
      hpartition0)

def couplingSpinSummedTwoBlockRootCarrierTargetWeight
    (coupling : Q') (cutoff n size : Nat)
    (tagged : TwoBlockRootedCarrier n) : Q' :=
  couplingSpinSummedTwoBlockConnectedCarrierTargetWeight
    coupling cutoff n size tagged.2

theorem couplingSpinSummedTwoBlockRootCarrierTargetSum_eqv
    (coupling : Q') (cutoff n size : Nat)
    (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) :
    listQSum
        (couplingSpinSummedTwoBlockRootCarrierTargetWeight
          coupling cutoff n size)
        (twoBlockRootCarrierTargetList n rootStart roots size) ≈
      listQSum (fun root =>
        listQSum
          (couplingSpinSummedTwoBlockConnectedCarrierTargetWeight
            coupling cutoff n size)
          (twoBlockConnectedCarrierTargetList n
            (rootStart root) size)) roots := by
  unfold twoBlockRootCarrierTargetList
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (couplingSpinSummedTwoBlockRootCarrierTargetWeight
        coupling cutoff n size)
      (fun root =>
        (twoBlockConnectedCarrierTargetList n
          (rootStart root) size).map
            (fun carrier => (root, carrier))) roots) ?_
  apply listQSum_congr
  intro root
  rw [listQSum_map]
  exact Q'.eqv_refl _

theorem couplingSpinSummedTwoBlockRootCarrierTargetSum_le_geom
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n size : Nat) (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) :
    listQSum
        (couplingSpinSummedTwoBlockRootCarrierTargetWeight
          coupling cutoff n size)
        (twoBlockRootCarrierTargetList n rootStart roots size) ≤
      Q'.ofNat roots.length *
        (anchorDecoratedEffectiveRatio ^ size *
          (couplingParametricKCompatibleSupportGasPartition
              coupling cutoff n *
            couplingParametricKCompatibleSupportGasPartition
              coupling cutoff n)) := by
  let partitionProduct :=
    couplingParametricKCompatibleSupportGasPartition coupling cutoff n *
      couplingParametricKCompatibleSupportGasPartition coupling cutoff n
  let bound := anchorDecoratedEffectiveRatio ^ size * partitionProduct
  have hbound0 : (0 : Q') ≤ bound :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative size)
      (Q'.mul_nonneg _ _
        (couplingParametricKCompatibleSupportGasPartition_nonnegative
          hcoupling cutoff n)
        (couplingParametricKCompatibleSupportGasPartition_nonnegative
          hcoupling cutoff n))
  have hsum := couplingSpinSummedTwoBlockRootCarrierTargetSum_eqv
    coupling cutoff n size rootStart roots
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
  apply listQSum_le_length_mul
    (fun root =>
      listQSum
        (couplingSpinSummedTwoBlockConnectedCarrierTargetWeight
          coupling cutoff n size)
        (twoBlockConnectedCarrierTargetList n
          (rootStart root) size))
    hbound0 roots
  intro root _
  exact couplingSpinSummedTwoBlockConnectedCarrierTargetSum_le_geom
    hcoupling cutoff n (rootStart root) size

theorem couplingSpinSummedTwoBlockConnectedSizeSum_le_rootTarget
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (cutoff : Nat)
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (rootStart : CanonicalAtom n → Nat)
    (hstartMem : ∀ root, root ∈ firstRoots → rootStart root ∈ root.val)
    (hne : ∀ entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate,
      twoBlockConnectedFirst entry ≠ twoBlockConnectedSecond entry)
    (size : Nat) :
    listQSum
        (fun entry : TwoBlockConnectedEntry firstRoots secondRoots
          firstPredicate secondPredicate =>
          couplingSpinSummedTwoBlockSourcePairWeight
            coupling cutoff entry.val)
        (twoBlockConnectedSourceEntriesAtSize size) ≤
      listQSum
        (couplingSpinSummedTwoBlockRootCarrierTargetWeight
          coupling cutoff n size)
        (twoBlockRootCarrierTargetList n rootStart firstRoots size) := by
  apply listQSum_le_of_injective
    (twoBlockConnectedSourceEntriesAtSize
      (firstRoots := firstRoots) (secondRoots := secondRoots)
      (firstPredicate := firstPredicate)
      (secondPredicate := secondPredicate) size)
    (twoBlockRootCarrierTargetList n rootStart firstRoots size)
    (fun entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate =>
      couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff entry.val)
    (couplingSpinSummedTwoBlockRootCarrierTargetWeight
      coupling cutoff n size)
    twoBlockConnectedRootCarrierEncode
    (twoBlockConnectedSourceEntriesAtSize_nodup
      firstRoots secondRoots firstPredicate secondPredicate size)
  · intro entry hentry
    have hsize : (twoBlockConnectedColoredSupport entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    unfold twoBlockRootCarrierTargetList
    apply List.mem_flatMap.mpr
    refine ⟨twoBlockConnectedFirst entry,
      twoBlockConnectedFirst_mem entry, ?_⟩
    apply List.mem_map.mpr
    refine ⟨twoBlockConnectedColoredCarrier entry, ?_, rfl⟩
    exact twoBlockConnectedColoredCarrier_mem_target entry (hne entry)
      (hstartMem _ (twoBlockConnectedFirst_mem entry)) hsize
  · intro first _ second _ heq
    exact twoBlockConnectedRootCarrierEncode_injective first second heq
  · intro entry hentry
    have hsize : (twoBlockConnectedColoredSupport entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    have hbound :=
      couplingSpinSummedTwoBlockConnectedSourcePairWeight_le_support_background
        hcoupling hle cutoff entry
    rw [hsize] at hbound
    simpa [couplingSpinSummedTwoBlockRootCarrierTargetWeight,
      twoBlockConnectedRootCarrierEncode,
      couplingSpinSummedTwoBlockConnectedCarrierTargetWeight,
      twoBlockConnectedColoredCarrier,
      couplingSpinSummedTwoBlockConnectedBackgroundPairWeight] using hbound
  · intro tagged _
    unfold couplingSpinSummedTwoBlockRootCarrierTargetWeight
      couplingSpinSummedTwoBlockConnectedCarrierTargetWeight
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedFaceEnvelope
        anchorDecoratedFaceEnvelope_nonnegative size)
      (Q'.mul_nonneg _ _
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff n tagged.2.2.1)
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff n tagged.2.2.2))

#print axioms couplingSpinSummedTwoBlockConnectedCarrierTargetSum_eqv
#print axioms couplingSpinSummedTwoBlockRootCarrierTargetSum_le_geom
#print axioms couplingSpinSummedTwoBlockConnectedSizeSum_le_rootTarget

end YMGap.Continuum.Z4CouplingParametricTwoBlockCarrierFixedSize
