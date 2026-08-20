/-
# Fixed-size summation of two-block connected carriers

At one carrier size, tag the recoverable colored carrier by its selected
first-block root.  That root supplies a pinned face, so the established
three-state colored-animal count applies.  The two compatible backgrounds
sum to two copies of the canonical partition function.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockColoredCarrierGeometry
import YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize

namespace YMGap.Continuum.Z4CanonicalTwoBlockCarrierFixedSize

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalColoredSupportWeight
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockColoredCarrierGeometry
open YMGap.Continuum.Z4CanonicalTwoBlockColoredPathCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

def twoBlockConnectedColorPair
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : ColoredSupportPair :=
  (twoBlockConnectedLeftColorSupport entry,
    twoBlockConnectedRightColorSupport entry)

theorem twoBlockConnectedColorPair_union
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    coloredSupportUnion n (twoBlockConnectedColorPair entry) =
      twoBlockConnectedColoredSupport entry := by
  exact coloredFamilyUnion_eq_appendUnion n
    (twoBlockConnectedPathLeftFamily entry)
    (twoBlockConnectedPathRightFamily entry)

theorem twoBlockConnectedFirstFace_mem_support
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate)
    (hne : twoBlockConnectedFirst entry ≠
      twoBlockConnectedSecond entry)
    {face : Nat} (hface : face ∈ (twoBlockConnectedFirst entry).val) :
    face ∈ twoBlockConnectedColoredSupport entry := by
  rw [twoBlockConnectedColoredSupport_eq_fullPathSupport entry hne]
  rw [twoBlockConnectedFullPathSupport_eq_carrierSupport entry]
  exact twoBlockConnectedCarrierSupport_first_mem
    (twoBlockSourceLeftCompatible entry.val)
    (twoBlockSourceRightCompatible entry.val)
    (twoBlockConnectedFirst entry)
    (twoBlockConnectedSecond entry)
    (twoBlockConnectedEndpoints_reach entry) hface

theorem twoBlockConnectedColorPair_mem_fixed
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate)
    (hne : twoBlockConnectedFirst entry ≠
      twoBlockConnectedSecond entry)
    {rootFace size : Nat}
    (hrootFace : rootFace ∈ (twoBlockConnectedFirst entry).val)
    (hsize : (twoBlockConnectedColoredSupport entry).length = size) :
    twoBlockConnectedColorPair entry ∈
      canonicalColoredPinnedSizePairs n rootFace size := by
  unfold canonicalColoredPinnedSizePairs
  apply List.mem_filter.mpr
  constructor
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨familyUnionSupport_mem_cutoffOneFaceSupports n _,
      familyUnionSupport_mem_cutoffOneFaceSupports n _⟩
  · apply (memberB_eq_true_iff _ _).2
    rw [twoBlockConnectedColorPair_union entry]
    exact mem_canonicalPinnedSizePolymers_iff.mpr
      ⟨(by
          rw [twoBlockConnectedColoredSupport_eq_fullPathSupport entry hne]
          rw [twoBlockConnectedFullPathSupport_eq_carrierSupport entry]
          exact connectedFaceSupport_mem_canonicalSurfacePolymers
            (twoBlockConnectedCarrierSupport_mem_faceSupports
              (twoBlockSourceLeftCompatible entry.val)
              (twoBlockSourceRightCompatible entry.val)
              (twoBlockConnectedFirst entry)
              (twoBlockConnectedSecond entry)
              (twoBlockConnectedEndpoints_reach entry))
            ⟨rootFace, twoBlockConnectedCarrierSupport_first_mem
              (twoBlockSourceLeftCompatible entry.val)
              (twoBlockSourceRightCompatible entry.val)
              (twoBlockConnectedFirst entry)
              (twoBlockConnectedSecond entry)
              (twoBlockConnectedEndpoints_reach entry) hrootFace⟩
            (twoBlockConnectedCarrierSupport_internallyConnected
              (twoBlockSourceLeftCompatible entry.val)
              (twoBlockSourceRightCompatible entry.val)
              (twoBlockConnectedFirst entry)
              (twoBlockConnectedSecond entry)
              (twoBlockConnectedEndpoints_reach entry) hrootFace)),
        twoBlockConnectedFirstFace_mem_support entry hne hrootFace,
        hsize⟩

def twoBlockConnectedCarrierTargetList
    (n rootFace size : Nat) : List ConnectedCarrier :=
  cartesian (canonicalColoredPinnedSizePairs n rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies n)
      (canonicalCompatibleAmbientFamilies n))

def twoBlockConnectedCarrierTargetWeight
    (n size : Nat) (carrier : ConnectedCarrier) : Q' :=
  anchorPerFaceEnvelope ^ size *
    (canonicalSurfaceFamilyActivity anchorCoupling n carrier.2.1 *
      canonicalSurfaceFamilyActivity anchorCoupling n carrier.2.2)

theorem twoBlockConnectedColoredCarrier_mem_target
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate)
    (hne : twoBlockConnectedFirst entry ≠
      twoBlockConnectedSecond entry)
    {rootFace size : Nat}
    (hrootFace : rootFace ∈ (twoBlockConnectedFirst entry).val)
    (hsize : (twoBlockConnectedColoredSupport entry).length = size) :
    twoBlockConnectedColoredCarrier entry ∈
      twoBlockConnectedCarrierTargetList n rootFace size := by
  unfold twoBlockConnectedCarrierTargetList
    twoBlockConnectedColoredCarrier
  apply (mem_cartesian_iff _ _ _).2
  constructor
  · exact twoBlockConnectedColorPair_mem_fixed
      entry hne hrootFace hsize
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨twoBlockConnectedBackgroundLeftFamily_mem entry,
      twoBlockConnectedBackgroundRightFamily_mem entry⟩

theorem twoBlockConnectedCarrierTargetSum_eqv
    (n rootFace size : Nat) :
    listQSum (twoBlockConnectedCarrierTargetWeight n size)
        (twoBlockConnectedCarrierTargetList n rootFace size) ≈
      canonicalColoredPinnedSizeWeightSum n rootFace size *
        (anchorCanonicalPartition n * anchorCanonicalPartition n) := by
  have houter := listQSum_cartesian_product
    (fun _ : ColoredSupportPair => anchorPerFaceEnvelope ^ size)
    (fun background : List (List Nat) × List (List Nat) =>
      canonicalSurfaceFamilyActivity anchorCoupling n background.1 *
        canonicalSurfaceFamilyActivity anchorCoupling n background.2)
    (canonicalColoredPinnedSizePairs n rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies n)
      (canonicalCompatibleAmbientFamilies n))
  have hinner := listQSum_cartesian_product
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (canonicalCompatibleAmbientFamilies n)
    (canonicalCompatibleAmbientFamilies n)
  unfold twoBlockConnectedCarrierTargetList
    twoBlockConnectedCarrierTargetWeight
    canonicalColoredPinnedSizeWeightSum
  refine Q'.eqv_trans _ _ _ houter ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  exact hinner

theorem twoBlockConnectedCarrierTargetSum_le_geom
    (n rootFace size : Nat) :
    listQSum (twoBlockConnectedCarrierTargetWeight n size)
        (twoBlockConnectedCarrierTargetList n rootFace size) ≤
      anchorEffectiveRatio ^ size *
        (anchorCanonicalPartition n * anchorCanonicalPartition n) := by
  have hfactor := twoBlockConnectedCarrierTargetSum_eqv
    n rootFace size
  have hpartition0 : (0 : Q') ≤
      anchorCanonicalPartition n * anchorCanonicalPartition n :=
    Q'.mul_nonneg _ _
      (anchorCanonicalPartition_nonnegative n)
      (anchorCanonicalPartition_nonnegative n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (canonicalColoredPinnedSizeWeightSum_le_geom n rootFace size)
      hpartition0)

abbrev TwoBlockRootedCarrier (n : Nat) :=
  CanonicalAtom n × ConnectedCarrier

def twoBlockRootCarrierTargetList
    (n : Nat) (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) (size : Nat) :
    List (TwoBlockRootedCarrier n) :=
  roots.flatMap (fun root =>
    (twoBlockConnectedCarrierTargetList n (rootStart root) size).map
      (fun carrier => (root, carrier)))

def twoBlockRootCarrierTargetWeight
    (n size : Nat) (tagged : TwoBlockRootedCarrier n) : Q' :=
  twoBlockConnectedCarrierTargetWeight n size tagged.2

theorem twoBlockRootCarrierTargetSum_eqv
    (n size : Nat) (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) :
    listQSum (twoBlockRootCarrierTargetWeight n size)
        (twoBlockRootCarrierTargetList n rootStart roots size) ≈
      listQSum (fun root =>
        listQSum (twoBlockConnectedCarrierTargetWeight n size)
          (twoBlockConnectedCarrierTargetList n
            (rootStart root) size)) roots := by
  unfold twoBlockRootCarrierTargetList
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap (twoBlockRootCarrierTargetWeight n size)
      (fun root =>
        (twoBlockConnectedCarrierTargetList n
          (rootStart root) size).map
            (fun carrier => (root, carrier))) roots) ?_
  apply listQSum_congr
  intro root
  rw [listQSum_map]
  exact Q'.eqv_refl _

theorem twoBlockRootCarrierTargetSum_le_geom
    (n size : Nat) (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) :
    listQSum (twoBlockRootCarrierTargetWeight n size)
        (twoBlockRootCarrierTargetList n rootStart roots size) ≤
      Q'.ofNat roots.length *
        (anchorEffectiveRatio ^ size *
          (anchorCanonicalPartition n * anchorCanonicalPartition n)) := by
  let bound := anchorEffectiveRatio ^ size *
    (anchorCanonicalPartition n * anchorCanonicalPartition n)
  have hbound0 : (0 : Q') ≤ bound :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorEffectiveRatio
        anchorEffectiveRatio_nonnegative size)
      (Q'.mul_nonneg _ _
        (anchorCanonicalPartition_nonnegative n)
        (anchorCanonicalPartition_nonnegative n))
  have hsum := twoBlockRootCarrierTargetSum_eqv
    n size rootStart roots
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
  apply listQSum_le_length_mul
    (fun root =>
      listQSum (twoBlockConnectedCarrierTargetWeight n size)
        (twoBlockConnectedCarrierTargetList n (rootStart root) size))
    hbound0 roots
  intro root _
  exact twoBlockConnectedCarrierTargetSum_le_geom
    n (rootStart root) size

def twoBlockConnectedSourceEntriesAtSize
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (size : Nat) :
    List (TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :=
  (connectedTwoBlockSourcePairs
    (firstRoots := firstRoots) (secondRoots := secondRoots)
    (firstPredicate := firstPredicate)
    (secondPredicate := secondPredicate)).attach.filter
      (fun entry => decide
        ((twoBlockConnectedColoredSupport entry).length = size))

theorem connectedTwoBlockSourcePairs_nodup
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    (connectedTwoBlockSourcePairs
      (firstRoots := firstRoots) (secondRoots := secondRoots)
      (firstPredicate := firstPredicate)
      (secondPredicate := secondPredicate)).Nodup :=
  List.filter_sublist.nodup
    (twoBlockSourcePairList_nodup
      firstRoots secondRoots firstPredicate secondPredicate)

theorem twoBlockConnectedSourceEntriesAtSize_nodup
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool)
    (size : Nat) :
    (twoBlockConnectedSourceEntriesAtSize
      (firstRoots := firstRoots) (secondRoots := secondRoots)
      (firstPredicate := firstPredicate)
      (secondPredicate := secondPredicate) size).Nodup :=
  List.filter_sublist.nodup
    (attach_nodup_of_nodup _
      (connectedTwoBlockSourcePairs_nodup
        firstRoots secondRoots firstPredicate secondPredicate))

def twoBlockConnectedRootCarrierEncode
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : TwoBlockRootedCarrier n :=
  (twoBlockConnectedFirst entry,
    twoBlockConnectedColoredCarrier entry)

theorem twoBlockConnectedRootCarrierEncode_injective
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (first second : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate)
    (heq : twoBlockConnectedRootCarrierEncode first =
      twoBlockConnectedRootCarrierEncode second) : first = second :=
  twoBlockConnectedColoredCarrier_injective first second
    (congrArg Prod.snd heq)

theorem twoBlockConnectedSizeSum_le_rootTarget
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
          twoBlockSourcePairWeight anchorCoupling entry.val)
        (twoBlockConnectedSourceEntriesAtSize size) ≤
      listQSum (twoBlockRootCarrierTargetWeight n size)
        (twoBlockRootCarrierTargetList n rootStart firstRoots size) := by
  apply listQSum_le_of_injective
    (twoBlockConnectedSourceEntriesAtSize
      (firstRoots := firstRoots) (secondRoots := secondRoots)
      (firstPredicate := firstPredicate)
      (secondPredicate := secondPredicate) size)
    (twoBlockRootCarrierTargetList n rootStart firstRoots size)
    (fun entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate =>
      twoBlockSourcePairWeight anchorCoupling entry.val)
    (twoBlockRootCarrierTargetWeight n size)
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
      twoBlockConnectedSourcePairWeight_le_support_background entry
    rw [hsize] at hbound
    simpa [twoBlockRootCarrierTargetWeight,
      twoBlockConnectedRootCarrierEncode,
      twoBlockConnectedCarrierTargetWeight,
      twoBlockConnectedColoredCarrier,
      twoBlockConnectedBackgroundPairWeight] using hbound
  · intro tagged _
    unfold twoBlockRootCarrierTargetWeight
      twoBlockConnectedCarrierTargetWeight
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorPerFaceEnvelope (by decide) size)
      (Q'.mul_nonneg _ _
        (canonicalSurfaceFamilyActivity_nonnegative n tagged.2.2.1)
        (canonicalSurfaceFamilyActivity_nonnegative n tagged.2.2.2))

#print axioms twoBlockConnectedColorPair_mem_fixed
#print axioms twoBlockConnectedCarrierTargetSum_le_geom
#print axioms twoBlockRootCarrierTargetSum_le_geom
#print axioms twoBlockConnectedSizeSum_le_rootTarget

end YMGap.Continuum.Z4CanonicalTwoBlockCarrierFixedSize
