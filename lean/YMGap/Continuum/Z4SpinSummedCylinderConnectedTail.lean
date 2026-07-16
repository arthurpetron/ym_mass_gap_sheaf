/-
# Uniform arbitrary-cutoff tail for the connected cylinder residue

The marked-cylinder classification into forward and mirrored singleton roots
is independent of the activity.  Reweighting its raw-pair injection by the
spin-summed family activity and applying the decorated singleton carrier tails
gives a cutoff-uniform cylinder residue bound with exact target and embedded
target partition factors.
-/

import YMGap.Continuum.Z4CanonicalCylinderConnectedTail
import YMGap.Continuum.Z4SpinSummedConnectedCarrierTail
import YMGap.Continuum.Z4SpinSummedTargetCylinderRatio

namespace YMGap.Continuum.Z4SpinSummedCylinderConnectedTail

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderConnectedClassification
open YMGap.Continuum.Z4CanonicalCylinderConnectedTail
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedConnectedCarrierTail
open YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight
open YMGap.Continuum.Z4SpinSummedCylinderSwitchSummation
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedTargetCylinderRatio

local infix:50 " ≈ " => Q'.eqv

theorem spinSummedConnectedCylinderPairSum_le_allRootRawPairSum
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true) :
    listQSum (spinSummedCylinderSourcePairWeight cutoff)
        (connectedCylinderSourcePairs
          (roots := roots) (predicate := predicate) hsmall) ≤
      listQSum (spinSummedCylinderRawPairWeight cutoff n)
        (allCylinderConnectedRawPairs hsmall roots) := by
  apply listQSum_le_of_injective
    (connectedCylinderSourcePairs
      (roots := roots) (predicate := predicate) hsmall)
    (allCylinderConnectedRawPairs hsmall roots)
    (spinSummedCylinderSourcePairWeight cutoff)
    (spinSummedCylinderRawPairWeight cutoff n)
    cylinderConnectedRawEncode
    (connectedCylinderSourcePairs_nodup hsmall roots predicate)
  · exact cylinderConnectedRawEncode_mem_all hsmall hrootsInside
  · intro first _ second _ heq
    exact cylinderConnectedRawEncode_injective first second heq
  · intro pair _
    exact Q'.le_refl' _
  · intro pair _
    exact Q'.mul_nonneg _ _
      (parametricKSupportFamilyActivity_nonnegative cutoff n pair.1)
      (parametricKSupportFamilyActivity_nonnegative cutoff n pair.2)

private theorem listQSum_pointwise_eqv {A : Type}
    (f g : A → Q') (hfg : ∀ x, f x ≈ g x) :
    ∀ xs : List A, listQSum f xs ≈ listQSum g xs
  | [] => Q'.eqv_refl 0
  | head :: tail =>
      Q'.add_eqv_congr' (hfg head)
        (listQSum_pointwise_eqv f g hfg tail)

theorem spinSummedForwardConnectedRawPairSum_eqv
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (root : CanonicalAtom n) :
    listQSum (spinSummedCylinderRawPairWeight cutoff n)
        (forwardConnectedRawPairs hsmall root) ≈
      listQSum (spinSummedSourcePairWeight cutoff)
        (connectedSourcePairs (root := root.val) hsmall) := by
  unfold forwardConnectedRawPairs
  rw [listQSum_map]
  exact Q'.eqv_refl _

theorem spinSummedReverseConnectedRawPairSum_eqv
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (root : CanonicalAtom n) :
    listQSum (spinSummedCylinderRawPairWeight cutoff n)
        (reverseConnectedRawPairs hsmall root) ≈
      listQSum (spinSummedReverseSourcePairWeight cutoff)
        (connectedReverseSourcePairs (root := root.val) hsmall) := by
  unfold reverseConnectedRawPairs
  rw [listQSum_map]
  apply listQSum_pointwise_eqv
  intro pair
  unfold spinSummedCylinderRawPairWeight
    spinSummedReverseSourcePairWeight
  exact Q'.mul_comm_eqv _ _

theorem spinSummedRootedCylinderConnectedRawPairSum_eqv
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (root : CanonicalAtom n) :
    listQSum (spinSummedCylinderRawPairWeight cutoff n)
        (rootedCylinderConnectedRawPairs hsmall root) ≈
      listQSum (spinSummedSourcePairWeight cutoff)
          (connectedSourcePairs (root := root.val) hsmall) +
        listQSum (spinSummedReverseSourcePairWeight cutoff)
          (connectedReverseSourcePairs (root := root.val) hsmall) := by
  unfold rootedCylinderConnectedRawPairs
  exact Q'.eqv_trans _ _ _
    (listQSum_append (spinSummedCylinderRawPairWeight cutoff n)
      (forwardConnectedRawPairs hsmall root)
      (reverseConnectedRawPairs hsmall root))
    (Q'.add_eqv_congr'
      (spinSummedForwardConnectedRawPairSum_eqv cutoff hsmall root)
      (spinSummedReverseConnectedRawPairSum_eqv cutoff hsmall root))

def spinSummedCylinderSingleRootBoundaryTail
    (cutoff small n distance : Nat) : Q' :=
  (parametricKCompatibleSupportGasPartition cutoff n *
      parametricKEmbeddedTargetPartition cutoff small n) *
    (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)

def spinSummedCylinderSingleRootTwoSidedTail
    (cutoff small n distance : Nat) : Q' :=
  spinSummedCylinderSingleRootBoundaryTail cutoff small n distance +
    spinSummedCylinderSingleRootBoundaryTail cutoff small n distance

theorem spinSummedCylinderSingleRootBoundaryTail_nonnegative
    (cutoff small n distance : Nat) :
    (0 : Q') ≤
      spinSummedCylinderSingleRootBoundaryTail
        cutoff small n distance := by
  unfold spinSummedCylinderSingleRootBoundaryTail
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (parametricKCompatibleSupportGasPartition_nonnegative cutoff n)
      (parametricKEmbeddedTargetPartition_nonnegative cutoff small n))
    (Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative (distance + 2))
      (by decide))

theorem spinSummedCylinderSingleRootTwoSidedTail_nonnegative
    (cutoff small n distance : Nat) :
    (0 : Q') ≤
      spinSummedCylinderSingleRootTwoSidedTail
        cutoff small n distance := by
  unfold spinSummedCylinderSingleRootTwoSidedTail
  exact Q'.zero_le_add _ _
    (spinSummedCylinderSingleRootBoundaryTail_nonnegative
      cutoff small n distance)
    (spinSummedCylinderSingleRootBoundaryTail_nonnegative
      cutoff small n distance)

theorem spinSummedRootedCylinderConnectedRawPairSum_le_boundaryTail
    (cutoff : Nat) {small n inner distance start : Nat}
    (hsmall : small ≤ n) (root : CanonicalAtom n)
    (hstart : start ∈ root.val)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (spinSummedCylinderRawPairWeight cutoff n)
        (rootedCylinderConnectedRawPairs hsmall root) ≤
      spinSummedCylinderSingleRootTwoSidedTail
        cutoff small n distance := by
  have hforward := spinSummedConnectedSourcePairSum_le_boundaryTail
    cutoff hsmall hstart hstartInner hbox
  have hreverse := spinSummedConnectedReverseSourcePairSum_le_boundaryTail
    cutoff hsmall hstart hstartInner hbox
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (spinSummedRootedCylinderConnectedRawPairSum_eqv
        cutoff hsmall root))
    (Q'.add_le_add hforward hreverse)

theorem spinSummedAllCylinderConnectedRawPairSum_le_boundaryTail
    (cutoff : Nat) {small n inner distance : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (spinSummedCylinderRawPairWeight cutoff n)
        (allCylinderConnectedRawPairs hsmall roots) ≤
      Q'.ofNat roots.length *
        spinSummedCylinderSingleRootTwoSidedTail
          cutoff small n distance := by
  have hflat := listQSum_flatMap
    (spinSummedCylinderRawPairWeight cutoff n)
    (rootedCylinderConnectedRawPairs hsmall) roots
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv hflat)
  apply listQSum_le_length_mul
    (fun root => listQSum (spinSummedCylinderRawPairWeight cutoff n)
      (rootedCylinderConnectedRawPairs hsmall root))
    (spinSummedCylinderSingleRootTwoSidedTail_nonnegative
      cutoff small n distance)
    roots
  intro root hroot
  obtain ⟨start, hstart, hstartInner⟩ := hgeometry root hroot
  exact spinSummedRootedCylinderConnectedRawPairSum_le_boundaryTail
    cutoff hsmall root hstart hstartInner hbox

/-- Uniform connected-residue tail for every finite cylinder predicate and
every representation cutoff. -/
theorem spinSummedConnectedCylinderPairSum_le_boundaryTail
    (cutoff : Nat) {small n inner distance : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (spinSummedCylinderSourcePairWeight cutoff)
        (connectedCylinderSourcePairs
          (roots := roots) (predicate := predicate) hsmall) ≤
      Q'.ofNat roots.length *
        spinSummedCylinderSingleRootTwoSidedTail
          cutoff small n distance := by
  exact Q'.le_trans' _ _ _
    (spinSummedConnectedCylinderPairSum_le_allRootRawPairSum
      cutoff hsmall roots predicate hrootsInside)
    (spinSummedAllCylinderConnectedRawPairSum_le_boundaryTail
      cutoff hsmall roots hgeometry hbox)

theorem spinSummedConnectedCylinderResidue_le_boundaryTail
    (cutoff : Nat) {small n inner distance : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    spinSummedConnectedCylinderResidue cutoff hsmall roots predicate ≤
      Q'.ofNat roots.length *
        spinSummedCylinderSingleRootTwoSidedTail
          cutoff small n distance := by
  unfold spinSummedConnectedCylinderResidue
  exact spinSummedConnectedCylinderPairSum_le_boundaryTail
    cutoff hsmall roots predicate hrootsInside hgeometry hbox

end YMGap.Continuum.Z4SpinSummedCylinderConnectedTail

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedCylinderConnectedTail.spinSummedConnectedCylinderPairSum_le_allRootRawPairSum
#print axioms YMGap.Continuum.Z4SpinSummedCylinderConnectedTail.spinSummedRootedCylinderConnectedRawPairSum_le_boundaryTail
#print axioms YMGap.Continuum.Z4SpinSummedCylinderConnectedTail.spinSummedConnectedCylinderPairSum_le_boundaryTail
#print axioms YMGap.Continuum.Z4SpinSummedCylinderConnectedTail.spinSummedConnectedCylinderResidue_le_boundaryTail
