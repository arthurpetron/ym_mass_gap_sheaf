/-
# Uniform tail for the right-rooted connected residue

The reverse carrier stores its backgrounds in the same large/embedded order
as the forward target.  It therefore injects into the already-counted shifted
colored shells and inherits the identical exact geometric tail.
-/

import YMGap.Continuum.Z4CanonicalConnectedCarrierTail
import YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier

namespace YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedCarrierTail
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Membership in the common colored-carrier target -/

def reverseConnectedColorPair
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    ColoredSupportPair :=
  (reverseConnectedLeftColorSupport hsmall entry,
    reverseConnectedRightColorSupport hsmall entry)

theorem reverseConnectedColorPair_union
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    coloredSupportUnion n (reverseConnectedColorPair hsmall entry) =
      reverseConnectedCarrierSupport hsmall entry := by
  exact coloredFamilyUnion_eq_appendUnion n
    (reverseConnectedPathLeftFamily hsmall entry)
    (reverseConnectedPathRightFamily hsmall entry)

theorem reverseConnectedColorPair_mem_fixed
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {rootFace size : Nat} (hrootFace : rootFace ∈ root)
    (hsize : (reverseConnectedCarrierSupport hsmall entry).length = size) :
    reverseConnectedColorPair hsmall entry ∈
      canonicalColoredPinnedSizePairs n rootFace size := by
  unfold canonicalColoredPinnedSizePairs
  apply List.mem_filter.mpr
  constructor
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨familyUnionSupport_mem_cutoffOneFaceSupports n _,
      familyUnionSupport_mem_cutoffOneFaceSupports n _⟩
  · apply (memberB_eq_true_iff _ _).2
    rw [reverseConnectedColorPair_union hsmall entry]
    exact mem_canonicalPinnedSizePolymers_iff.mpr
      ⟨reverseConnectedCarrierSupport_mem_canonicalSurfacePolymers
          hsmall entry hrootFace,
        reverseConnectedCarrierSupport_root_mem hsmall entry hrootFace,
        hsize⟩

theorem reverseConnectedCarrier_mem_target
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {rootFace size : Nat} (hrootFace : rootFace ∈ root)
    (hsize : (reverseConnectedCarrierSupport hsmall entry).length = size) :
    reverseConnectedCarrier hsmall entry ∈
      connectedCarrierTargetList small n rootFace size := by
  unfold connectedCarrierTargetList reverseConnectedCarrier
  apply (mem_cartesian_iff _ _ _).2
  constructor
  · exact reverseConnectedColorPair_mem_fixed
      hsmall entry hrootFace hsize
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨reverseConnectedBackgroundRightFamily_mem hsmall entry,
      reverseConnectedBackgroundLeftFamily_mem_embedded hsmall entry⟩

/-! ## 2. Direct shifted-shell injection -/

theorem reverseConnectedCarrierSupport_length_le_ambient
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    (reverseConnectedCarrierSupport hsmall entry).length ≤
      (physicalFaceEdges n).length := by
  have hsupport := reverseConnectedCarrierSupport_mem_faceSupports
    hsmall entry
  have hnodup := nodup_of_mem_sublists
    (physicalFaceEdges n) (reverseConnectedCarrierSupport hsmall entry)
    (physicalFaceEdges_nodup n) hsupport
  exact length_le_of_unique_representation
    (fun source target : Nat => source = target)
    (reverseConnectedCarrierSupport hsmall entry) (physicalFaceEdges n)
    hnodup
    (fun face hface =>
      ⟨face, mem_of_mem_sublists (physicalFaceEdges n)
        (reverseConnectedCarrierSupport hsmall entry) hsupport face hface,
        rfl⟩)
    (fun left _ right _ target hleft hright =>
      hleft.trans hright.symm)

def reverseConnectedCarrierShiftEncode
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (floor : Nat) (entry : ReverseConnectedSourceEntry root hsmall) :
    Nat × ConnectedCarrier :=
  ((reverseConnectedCarrierSupport hsmall entry).length - floor,
    reverseConnectedCarrier hsmall entry)

theorem connectedReverseSourcePairs_nodup
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    (connectedReverseSourcePairs (root := root) hsmall).Nodup :=
  List.filter_sublist.nodup (reverseSourcePairList_nodup hsmall root)

theorem connectedReverseSourcePairSum_le_shiftedTarget
    {small n inner distance start : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum reverseSourcePairWeight
        (connectedReverseSourcePairs (root := root) hsmall) ≤
      listQSum (shiftedCarrierTargetWeight n (distance + 2))
        (shiftedCarrierTargetList small n start (distance + 2)
          ((physicalFaceEdges n).length + 1)) := by
  have hinjection := listQSum_le_of_injective
    (connectedReverseSourcePairs (root := root) hsmall).attach
    (shiftedCarrierTargetList small n start (distance + 2)
      ((physicalFaceEdges n).length + 1))
    (fun entry : ReverseConnectedSourceEntry root hsmall =>
      reverseSourcePairWeight entry.val)
    (shiftedCarrierTargetWeight n (distance + 2))
    (reverseConnectedCarrierShiftEncode hsmall (distance + 2))
    (attach_nodup_of_nodup _
      (connectedReverseSourcePairs_nodup hsmall root))
    (fun entry _ => by
      have hfloor := reverseConnectedCarrierSupport_boundary_floor
        hsmall entry hstart hstartInner hbox
      have hmax := reverseConnectedCarrierSupport_length_le_ambient
        hsmall entry
      let offset := (reverseConnectedCarrierSupport hsmall entry).length -
        (distance + 2)
      have hoffset : offset < (physicalFaceEdges n).length + 1 := by
        unfold offset
        omega
      have hsize :
          (reverseConnectedCarrierSupport hsmall entry).length =
            distance + 2 + offset := by
        unfold offset
        omega
      apply mem_shiftedCarrierTargetList_of_lt
        small n start (distance + 2)
        ((physicalFaceEdges n).length + 1) hoffset
      exact reverseConnectedCarrier_mem_target
        hsmall entry hstart hsize)
    (fun first _ second _ heq => by
      apply reverseConnectedCarrier_injective hsmall first second
      exact congrArg Prod.snd heq)
    (fun entry _ => by
      have hfloor := reverseConnectedCarrierSupport_boundary_floor
        hsmall entry hstart hstartInner hbox
      have hsize :
          distance + 2 +
              ((reverseConnectedCarrierSupport hsmall entry).length -
                (distance + 2)) =
            (reverseConnectedCarrierSupport hsmall entry).length := by
        omega
      have hbound :=
        reverseConnectedSourcePairWeight_le_support_background
          hsmall entry
      unfold reverseConnectedBackgroundPairWeight at hbound
      unfold reverseConnectedCarrierShiftEncode shiftedCarrierTargetWeight
        connectedCarrierTargetWeight reverseConnectedCarrier
      rw [hsize]
      simpa using hbound)
    (fun tagged _ => by
      unfold shiftedCarrierTargetWeight connectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorPerFaceEnvelope (by decide) _)
        (Q'.mul_nonneg _ _
          (canonicalSurfaceFamilyActivity_nonnegative n tagged.2.2.1)
          (canonicalSurfaceFamilyActivity_nonnegative n tagged.2.2.2)))
  rw [listQSum_attach] at hinjection
  exact hinjection

theorem connectedReverseSourcePairSum_le_boundaryTail
    {small n inner distance start : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum reverseSourcePairWeight
        (connectedReverseSourcePairs (root := root) hsmall) ≤
      (anchorCanonicalPartition n * anchorCanonicalPartition small) *
        (anchorEffectiveRatio ^ (distance + 2) * Q'.ofNat 2) := by
  exact Q'.le_trans' _ _ _
    (connectedReverseSourcePairSum_le_shiftedTarget
      hsmall hstart hstartInner hbox)
    (shiftedCarrierTargetSum_le_tail hsmall start (distance + 2)
      ((physicalFaceEdges n).length + 1))

end YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail.reverseConnectedCarrier_mem_target
#print axioms YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail.connectedReverseSourcePairSum_le_shiftedTarget
#print axioms YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail.connectedReverseSourcePairSum_le_boundaryTail
