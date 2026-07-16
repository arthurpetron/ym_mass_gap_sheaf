/-
# Fixed-size summation of connected colored carriers

At a fixed union-support size, each connected source entry injects into a
pair consisting of its two support colors and its two exact compatible
backgrounds.  The support colors are counted by the exact three-state bound;
the background sum factors into two copies of the canonical partition.
-/

import YMGap.Continuum.Z4CanonicalColoredSupportWeight

namespace YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalColoredSupportWeight
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two color supports have exactly the carrier union -/

theorem coloredFamilyUnion_eq_appendUnion
    (n : Nat) (left right : List (List Nat)) :
    coloredSupportUnion n
        (familyUnionSupport n left, familyUnionSupport n right) =
      familyUnionSupport n (left ++ right) := by
  apply sublists_eq_of_mem_iff (physicalFaceEdges n)
    (coloredSupportUnion n
      (familyUnionSupport n left, familyUnionSupport n right))
    (familyUnionSupport n (left ++ right))
    (physicalFaceEdges_nodup n)
    (coloredSupportUnion_mem_faceSupports n _)
    (familyUnionSupport_mem_cutoffOneFaceSupports n (left ++ right))
  intro face
  rw [mem_coloredSupportUnion_iff
    (familyUnionSupport_mem_cutoffOneFaceSupports n left)
    (familyUnionSupport_mem_cutoffOneFaceSupports n right) face]
  constructor
  · intro h
    apply (mem_familyUnionSupport_iff n (left ++ right) face).2
    rcases h with hleft | hright
    · obtain ⟨hphysical, polymer, hpolymer, hface⟩ :=
        (mem_familyUnionSupport_iff n left face).1 hleft
      exact ⟨hphysical, polymer, List.mem_append.mpr (Or.inl hpolymer),
        hface⟩
    · obtain ⟨hphysical, polymer, hpolymer, hface⟩ :=
        (mem_familyUnionSupport_iff n right face).1 hright
      exact ⟨hphysical, polymer, List.mem_append.mpr (Or.inr hpolymer),
        hface⟩
  · intro h
    obtain ⟨hphysical, polymer, hpolymer, hface⟩ :=
      (mem_familyUnionSupport_iff n (left ++ right) face).1 h
    rcases List.mem_append.mp hpolymer with hleft | hright
    · exact Or.inl ((mem_familyUnionSupport_iff n left face).2
        ⟨hphysical, polymer, hleft, hface⟩)
    · exact Or.inr ((mem_familyUnionSupport_iff n right face).2
        ⟨hphysical, polymer, hright, hface⟩)

def connectedColorPair
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : ColoredSupportPair :=
  (connectedLeftColorSupport hsmall entry,
    connectedRightColorSupport hsmall entry)

theorem connectedColorPair_union
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    coloredSupportUnion n (connectedColorPair hsmall entry) =
      connectedCarrierSupport hsmall entry := by
  exact coloredFamilyUnion_eq_appendUnion n
    (connectedPathLeftFamily hsmall entry)
    (connectedPathRightFamily hsmall entry)

theorem connectedColorPair_mem_fixed
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall)
    {rootFace size : Nat} (hrootFace : rootFace ∈ root)
    (hsize : (connectedCarrierSupport hsmall entry).length = size) :
    connectedColorPair hsmall entry ∈
      canonicalColoredPinnedSizePairs n rootFace size := by
  unfold canonicalColoredPinnedSizePairs
  apply List.mem_filter.mpr
  constructor
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨familyUnionSupport_mem_cutoffOneFaceSupports n _,
      familyUnionSupport_mem_cutoffOneFaceSupports n _⟩
  · apply (memberB_eq_true_iff _ _).2
    rw [connectedColorPair_union hsmall entry]
    exact mem_canonicalPinnedSizePolymers_iff.mpr
      ⟨connectedCarrierSupport_mem_canonicalSurfacePolymers
          hsmall entry hrootFace,
        connectedCarrierSupport_root_mem hsmall entry hrootFace,
        hsize⟩

/-! ## 2. Fixed-size source and carrier lists -/

def connectedSourceEntriesAtSize
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (size : Nat) : List (ConnectedSourceEntry root hsmall) :=
  (connectedSourcePairs (root := root) hsmall).attach.filter
    (fun entry => decide
      ((connectedCarrierSupport hsmall entry).length = size))

def connectedCarrierTargetList (small n rootFace size : Nat) :
    List ConnectedCarrier :=
  cartesian (canonicalColoredPinnedSizePairs n rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies n)
      (embeddedCompatibleFamilies small n))

def connectedCarrierTargetWeight (n size : Nat)
    (carrier : ConnectedCarrier) : Q' :=
  anchorPerFaceEnvelope ^ size *
    (canonicalSurfaceFamilyActivity anchorCoupling n carrier.2.1 *
      canonicalSurfaceFamilyActivity anchorCoupling n carrier.2.2)

def connectedSourceSizeSum
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (size : Nat) : Q' :=
  listQSum (fun entry : ConnectedSourceEntry root hsmall =>
      sourcePairWeight entry.val)
    (connectedSourceEntriesAtSize hsmall size)

theorem connectedSourceEntriesAtSize_nodup
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (size : Nat) :
    (connectedSourceEntriesAtSize (root := root) hsmall size).Nodup := by
  unfold connectedSourceEntriesAtSize
  exact List.filter_sublist.nodup
    (attach_nodup_of_nodup _
      (List.filter_sublist.nodup (sourcePairList_nodup hsmall root)))

theorem connectedBackgroundRightFamily_mem_embedded
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    connectedBackgroundRightFamily hsmall entry ∈
      embeddedCompatibleFamilies small n := by
  apply family_mem_embeddedCompatibleFamilies_of_inside hsmall
    (connectedBackgroundRightFamily_mem hsmall entry)
  have hinside := familyInsideBox_of_mem_embeddedCompatibleFamilies
    hsmall (sourceRightEmbedded entry.val)
  intro support hsupport
  exact hinside support (List.mem_filter.mp hsupport).1

theorem connectedCarrier_mem_target
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall)
    {rootFace size : Nat} (hrootFace : rootFace ∈ root)
    (hsize : (connectedCarrierSupport hsmall entry).length = size) :
    connectedCarrier hsmall entry ∈
      connectedCarrierTargetList small n rootFace size := by
  unfold connectedCarrierTargetList connectedCarrier
  apply (mem_cartesian_iff _ _ _).2
  constructor
  · exact connectedColorPair_mem_fixed hsmall entry hrootFace hsize
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨connectedBackgroundLeftFamily_mem hsmall entry,
      connectedBackgroundRightFamily_mem_embedded hsmall entry⟩

theorem connectedSourceSizeSum_le_carrierTarget
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    {rootFace size : Nat} (hrootFace : rootFace ∈ root) :
    connectedSourceSizeSum (root := root) hsmall size ≤
      listQSum (connectedCarrierTargetWeight n size)
        (connectedCarrierTargetList small n rootFace size) := by
  unfold connectedSourceSizeSum
  apply listQSum_le_of_injective
    (connectedSourceEntriesAtSize hsmall size)
    (connectedCarrierTargetList small n rootFace size)
    (fun entry : ConnectedSourceEntry root hsmall =>
      sourcePairWeight entry.val)
    (connectedCarrierTargetWeight n size)
    (connectedCarrier hsmall)
    (connectedSourceEntriesAtSize_nodup hsmall size)
  · intro entry hentry
    have hsize : (connectedCarrierSupport hsmall entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    exact connectedCarrier_mem_target hsmall entry hrootFace hsize
  · intro first _ second _ heq
    exact connectedCarrier_injective hsmall first second heq
  · intro entry hentry
    have hsize : (connectedCarrierSupport hsmall entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    have hbound := connectedSourcePairWeight_le_support_background
      hsmall entry
    rw [hsize] at hbound
    simpa [connectedCarrierTargetWeight, connectedCarrier,
      connectedBackgroundPairWeight] using hbound
  · intro carrier _
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorPerFaceEnvelope (by decide) size)
      (Q'.mul_nonneg _ _
        (canonicalSurfaceFamilyActivity_nonnegative n carrier.2.1)
        (canonicalSurfaceFamilyActivity_nonnegative n carrier.2.2))

/-! ## 3. Exact background factorization and the geometric bound -/

theorem connectedCarrierTargetSum_eqv
    {small n : Nat} (hsmall : small ≤ n) (rootFace size : Nat) :
    listQSum (connectedCarrierTargetWeight n size)
        (connectedCarrierTargetList small n rootFace size) ≈
      canonicalColoredPinnedSizeWeightSum n rootFace size *
        (anchorCanonicalPartition n * anchorCanonicalPartition small) := by
  have houter := listQSum_cartesian_product
    (fun _ : ColoredSupportPair => anchorPerFaceEnvelope ^ size)
    (fun background : List (List Nat) × List (List Nat) =>
      canonicalSurfaceFamilyActivity anchorCoupling n background.1 *
        canonicalSurfaceFamilyActivity anchorCoupling n background.2)
    (canonicalColoredPinnedSizePairs n rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies n)
      (embeddedCompatibleFamilies small n))
  have hinner := listQSum_cartesian_product
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (canonicalCompatibleAmbientFamilies n)
    (embeddedCompatibleFamilies small n)
  have hembedded := anchorCanonicalPartition_eqv_embedded hsmall
  unfold connectedCarrierTargetList connectedCarrierTargetWeight
    canonicalColoredPinnedSizeWeightSum
  refine Q'.eqv_trans _ _ _ houter ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ hinner ?_
  unfold anchorCanonicalPartition embeddedAnchorPartition
    parametricCanonicalCompatibleAmbientPartition at hembedded
  unfold anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hembedded)

theorem connectedSourceSizeSum_le_geom_partition_sq
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    {rootFace size : Nat} (hrootFace : rootFace ∈ root) :
    connectedSourceSizeSum (root := root) hsmall size ≤
      anchorEffectiveRatio ^ size *
        (anchorCanonicalPartition n * anchorCanonicalPartition small) := by
  have htarget := connectedSourceSizeSum_le_carrierTarget
    hsmall hrootFace (size := size)
  have hfactor := connectedCarrierTargetSum_eqv hsmall rootFace size
  have hpartition0 : (0 : Q') ≤
      anchorCanonicalPartition n * anchorCanonicalPartition small :=
    Q'.mul_nonneg _ _
      (anchorCanonicalPartition_nonnegative n)
      (anchorCanonicalPartition_nonnegative small)
  have hcolored := Q'.mul_le_mul_of_nonneg_right _ _ _
    (canonicalColoredPinnedSizeWeightSum_le_geom n rootFace size)
    hpartition0
  exact Q'.le_trans' _ _ _ htarget
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hcolored)

end YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize.coloredFamilyUnion_eq_appendUnion
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize.connectedSourceSizeSum_le_carrierTarget
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize.connectedCarrierTargetSum_eqv
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize.connectedSourceSizeSum_le_geom_partition_sq
