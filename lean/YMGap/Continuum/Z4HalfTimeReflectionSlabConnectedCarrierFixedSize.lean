/-
# Fixed-size summation of slab connected carriers

At fixed colored-union size, every connected slab source entry injects into
its selected marked root, two support colors, an arbitrary compatible ambient
background, and an arbitrary slab-supported background.  The background
Cartesian sum is therefore exactly the full canonical partition `Z` times the
slab-support numerator `S`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierWeight
import YMGap.Continuum.Z4CanonicalColoredSupportWeight

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierFixedSize

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalColoredSupportWeight
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierWeight
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two color supports have exactly the carrier union -/

def slabConnectedColorPair
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    ColoredSupportPair :=
  (slabConnectedLeftColorSupport defaultRoot entry,
    slabConnectedRightColorSupport defaultRoot entry)

theorem slabConnectedColorPair_union
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    coloredSupportUnion (extent + 1)
        (slabConnectedColorPair defaultRoot entry) =
      slabConnectedCarrierSupport defaultRoot entry := by
  exact coloredFamilyUnion_eq_appendUnion (extent + 1)
    (slabConnectedPathLeftFamily defaultRoot entry)
    (slabConnectedPathRightFamily defaultRoot entry)

def slabCanonicalAtomFirstFace
    {n : Nat} (root : CanonicalAtom n) : Nat :=
  root.val.head (by
    intro hnil
    obtain ⟨face, hface⟩ :=
      canonicalSurfacePolymers_allNonempty n root.val root.property
    rw [hnil] at hface
    cases hface)

theorem slabCanonicalAtomFirstFace_mem
    {n : Nat} (root : CanonicalAtom n) :
    slabCanonicalAtomFirstFace root ∈ root.val := by
  unfold slabCanonicalAtomFirstFace
  exact List.head_mem _

theorem slabConnectedColorPair_mem_fixed
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {size : Nat}
    (hsize : (slabConnectedCarrierSupport defaultRoot entry).length = size) :
    slabConnectedColorPair defaultRoot entry ∈
      canonicalColoredPinnedSizePairs (extent + 1)
        (slabCanonicalAtomFirstFace
          (slabSourceRootAtom defaultRoot entry.val)) size := by
  unfold canonicalColoredPinnedSizePairs
  apply List.mem_filter.mpr
  constructor
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨familyUnionSupport_mem_cutoffOneFaceSupports (extent + 1) _,
      familyUnionSupport_mem_cutoffOneFaceSupports (extent + 1) _⟩
  · apply (memberB_eq_true_iff _ _).2
    rw [slabConnectedColorPair_union defaultRoot entry]
    exact mem_canonicalPinnedSizePolymers_iff.mpr
      ⟨slabConnectedCarrierSupport_mem_canonicalSurfacePolymers
          defaultRoot hrootsSupported entry
          (slabCanonicalAtomFirstFace_mem
            (slabSourceRootAtom defaultRoot entry.val)),
        slabConnectedCarrierSupport_root_mem
          defaultRoot hrootsSupported entry
          (slabCanonicalAtomFirstFace_mem
            (slabSourceRootAtom defaultRoot entry.val)),
        hsize⟩

/-! ## 2. Fixed-size source and rooted carrier targets -/

def slabConnectedSourceEntriesAtSize
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1)) (size : Nat) :
    List (SlabConnectedSourceEntry extent roots predicate) :=
  (connectedSlabCylinderSourcePairs
    (extent := extent) (roots := roots)
    (predicate := predicate)).attach.filter
      (fun entry => decide
        ((slabConnectedCarrierSupport defaultRoot entry).length = size))

def slabConnectedCarrierTargetListAtRoot
    (extent : Nat) (root : CanonicalAtom (extent + 1)) (size : Nat) :
    List SlabConnectedCarrier :=
  cartesian
    (canonicalColoredPinnedSizePairs (extent + 1)
      (slabCanonicalAtomFirstFace root) size)
    (cartesian (canonicalCompatibleAmbientFamilies (extent + 1))
      (canonicalSlabSupportedFamilies extent))

abbrev SlabRootedConnectedCarrier (extent : Nat) :=
  CanonicalAtom (extent + 1) × SlabConnectedCarrier

def slabConnectedCarrierTargetList
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (size : Nat) : List (SlabRootedConnectedCarrier extent) :=
  roots.flatMap fun root =>
    (slabConnectedCarrierTargetListAtRoot extent root size).map
      (fun carrier => (root, carrier))

def slabConnectedCarrierTargetWeight
    (extent size : Nat) (carrier : SlabConnectedCarrier) : Q' :=
  anchorPerFaceEnvelope ^ size *
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1)
        carrier.2.1 *
      canonicalSurfaceFamilyActivity anchorCoupling (extent + 1)
        carrier.2.2)

def slabRootedConnectedCarrierTargetWeight
    (extent size : Nat) (carrier : SlabRootedConnectedCarrier extent) : Q' :=
  slabConnectedCarrierTargetWeight extent size carrier.2

def slabConnectedSourceSizeSum
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1)) (size : Nat) : Q' :=
  listQSum (fun entry : SlabConnectedSourceEntry extent roots predicate =>
      slabCylinderSourcePairWeight entry.val)
    (slabConnectedSourceEntriesAtSize defaultRoot size)

theorem slabConnectedSourceEntriesAtSize_nodup
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1)) (size : Nat) :
    (slabConnectedSourceEntriesAtSize
      (extent := extent) (roots := roots) (predicate := predicate)
      defaultRoot size).Nodup := by
  unfold slabConnectedSourceEntriesAtSize
  exact List.filter_sublist.nodup
    (attach_nodup_of_nodup _
      (List.filter_sublist.nodup
        (slabCylinderSourcePairList_nodup extent roots predicate)))

def slabRootedConnectedCarrier
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    SlabRootedConnectedCarrier extent :=
  (slabSourceRootAtom defaultRoot entry.val,
    slabConnectedCarrier defaultRoot entry)

theorem slabConnectedCarrier_mem_target_at_root
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {size : Nat}
    (hsize : (slabConnectedCarrierSupport defaultRoot entry).length = size) :
    slabConnectedCarrier defaultRoot entry ∈
      slabConnectedCarrierTargetListAtRoot extent
        (slabSourceRootAtom defaultRoot entry.val) size := by
  unfold slabConnectedCarrierTargetListAtRoot slabConnectedCarrier
  apply (mem_cartesian_iff _ _ _).2
  constructor
  · exact slabConnectedColorPair_mem_fixed
      defaultRoot hrootsSupported entry hsize
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨slabConnectedBackgroundLeftFamily_mem defaultRoot entry,
      slabConnectedBackgroundRightFamily_mem_supported defaultRoot entry⟩

theorem slabRootedConnectedCarrier_mem_target
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {size : Nat}
    (hsize : (slabConnectedCarrierSupport defaultRoot entry).length = size) :
    slabRootedConnectedCarrier defaultRoot entry ∈
      slabConnectedCarrierTargetList extent roots size := by
  unfold slabConnectedCarrierTargetList slabRootedConnectedCarrier
  apply List.mem_flatMap.mpr
  refine ⟨slabSourceRootAtom defaultRoot entry.val,
    (slabSourceRootAtom_spec defaultRoot entry.val entry.property).2, ?_⟩
  apply List.mem_map.mpr
  exact ⟨slabConnectedCarrier defaultRoot entry,
    slabConnectedCarrier_mem_target_at_root
      defaultRoot hrootsSupported entry hsize, rfl⟩

theorem slabConnectedSourceSizeSum_le_carrierTarget
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (size : Nat) :
    slabConnectedSourceSizeSum
        (extent := extent) (roots := roots) (predicate := predicate)
        defaultRoot size ≤
      listQSum (slabRootedConnectedCarrierTargetWeight extent size)
        (slabConnectedCarrierTargetList extent roots size) := by
  unfold slabConnectedSourceSizeSum
  apply listQSum_le_of_injective
    (slabConnectedSourceEntriesAtSize defaultRoot size)
    (slabConnectedCarrierTargetList extent roots size)
    (fun entry : SlabConnectedSourceEntry extent roots predicate =>
      slabCylinderSourcePairWeight entry.val)
    (slabRootedConnectedCarrierTargetWeight extent size)
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
    have hbound := slabConnectedSourcePairWeight_le_support_background
      defaultRoot entry
    rw [hsize] at hbound
    simpa [slabRootedConnectedCarrierTargetWeight,
      slabConnectedCarrierTargetWeight, slabRootedConnectedCarrier,
      slabConnectedCarrier, slabConnectedBackgroundPairWeight] using hbound
  · intro carrier _
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorPerFaceEnvelope (by decide) size)
      (Q'.mul_nonneg _ _
        (canonicalSurfaceFamilyActivity_nonnegative
          (extent + 1) carrier.2.2.1)
        (canonicalSurfaceFamilyActivity_nonnegative
          (extent + 1) carrier.2.2.2))

/-! ## 3. Exact `Z * S` background factor and fixed-size bound -/

theorem slabConnectedCarrierTargetSumAtRoot_eqv
    (extent : Nat) (root : CanonicalAtom (extent + 1)) (size : Nat) :
    listQSum (slabConnectedCarrierTargetWeight extent size)
        (slabConnectedCarrierTargetListAtRoot extent root size) ≈
      canonicalColoredPinnedSizeWeightSum (extent + 1)
          (slabCanonicalAtomFirstFace root) size *
        (anchorCanonicalPartition (extent + 1) *
          anchorEventNumerator (extent + 1)
            (canonicalFamilySlabSupportedB extent)) := by
  have houter := listQSum_cartesian_product
    (fun _ : ColoredSupportPair => anchorPerFaceEnvelope ^ size)
    (fun background : List (List Nat) × List (List Nat) =>
      canonicalSurfaceFamilyActivity anchorCoupling (extent + 1)
          background.1 *
        canonicalSurfaceFamilyActivity anchorCoupling (extent + 1)
          background.2)
    (canonicalColoredPinnedSizePairs (extent + 1)
      (slabCanonicalAtomFirstFace root) size)
    (cartesian (canonicalCompatibleAmbientFamilies (extent + 1))
      (canonicalSlabSupportedFamilies extent))
  have hinner := listQSum_cartesian_product
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (canonicalCompatibleAmbientFamilies (extent + 1))
    (canonicalSlabSupportedFamilies extent)
  unfold slabConnectedCarrierTargetListAtRoot
    slabConnectedCarrierTargetWeight canonicalColoredPinnedSizeWeightSum
  refine Q'.eqv_trans _ _ _ houter ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ hinner ?_
  unfold anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition anchorEventNumerator
    canonicalSlabSupportedFamilies
  exact Q'.eqv_refl _

private theorem slabRootedTargetMapSum_eqv
    (extent size : Nat) (root : CanonicalAtom (extent + 1)) :
    listQSum (slabRootedConnectedCarrierTargetWeight extent size)
        ((slabConnectedCarrierTargetListAtRoot extent root size).map
          (fun carrier => (root, carrier))) ≈
      listQSum (slabConnectedCarrierTargetWeight extent size)
        (slabConnectedCarrierTargetListAtRoot extent root size) := by
  rw [listQSum_map]
  exact Q'.eqv_refl _

theorem slabConnectedCarrierTargetSum_eqv_rootSum
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (size : Nat) :
    listQSum (slabRootedConnectedCarrierTargetWeight extent size)
        (slabConnectedCarrierTargetList extent roots size) ≈
      listQSum (fun root =>
        listQSum (slabConnectedCarrierTargetWeight extent size)
          (slabConnectedCarrierTargetListAtRoot extent root size)) roots := by
  unfold slabConnectedCarrierTargetList
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (slabRootedConnectedCarrierTargetWeight extent size)
      (fun root =>
        (slabConnectedCarrierTargetListAtRoot extent root size).map
          (fun carrier => (root, carrier))) roots) ?_
  exact listQSum_congr
    (fun root => slabRootedTargetMapSum_eqv extent size root) roots

theorem slabConnectedCarrierTargetSum_le_geom_partition
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (size : Nat) :
    listQSum (slabRootedConnectedCarrierTargetWeight extent size)
        (slabConnectedCarrierTargetList extent roots size) ≤
      Q'.ofNat roots.length *
        (anchorEffectiveRatio ^ size *
          (anchorCanonicalPartition (extent + 1) *
            anchorEventNumerator (extent + 1)
              (canonicalFamilySlabSupportedB extent))) := by
  let partitionProduct := anchorCanonicalPartition (extent + 1) *
    anchorEventNumerator (extent + 1)
      (canonicalFamilySlabSupportedB extent)
  let bound := anchorEffectiveRatio ^ size * partitionProduct
  have hproduct0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (anchorCanonicalPartition_nonnegative (extent + 1))
      (anchorEventNumerator_nonnegative (extent + 1)
        (canonicalFamilySlabSupportedB extent))
  have hbound0 : (0 : Q') ≤ bound :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorEffectiveRatio
        anchorEffectiveRatio_nonnegative size) hproduct0
  have hrootBound : ∀ root, root ∈ roots →
      listQSum (slabConnectedCarrierTargetWeight extent size)
          (slabConnectedCarrierTargetListAtRoot extent root size) ≤
        bound := by
    intro root _
    have hfactor := slabConnectedCarrierTargetSumAtRoot_eqv
      extent root size
    have hcolored := Q'.mul_le_mul_of_nonneg_right _ _ _
      (canonicalColoredPinnedSizeWeightSum_le_geom
        (extent + 1) (slabCanonicalAtomFirstFace root) size)
      hproduct0
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hcolored
  have hrootSum := listQSum_le_length_mul
    (fun root => listQSum
      (slabConnectedCarrierTargetWeight extent size)
      (slabConnectedCarrierTargetListAtRoot extent root size))
    hbound0 roots hrootBound
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (slabConnectedCarrierTargetSum_eqv_rootSum extent roots size))
    hrootSum

theorem slabConnectedSourceSizeSum_le_geom_partition
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (size : Nat) :
    slabConnectedSourceSizeSum
        (extent := extent) (roots := roots) (predicate := predicate)
        defaultRoot size ≤
      Q'.ofNat roots.length *
        (anchorEffectiveRatio ^ size *
          (anchorCanonicalPartition (extent + 1) *
            anchorEventNumerator (extent + 1)
              (canonicalFamilySlabSupportedB extent))) :=
  Q'.le_trans' _ _ _
    (slabConnectedSourceSizeSum_le_carrierTarget
      defaultRoot hrootsSupported size)
    (slabConnectedCarrierTargetSum_le_geom_partition extent roots size)

#print axioms slabConnectedColorPair_mem_fixed
#print axioms slabConnectedSourceSizeSum_le_carrierTarget
#print axioms slabConnectedCarrierTargetSumAtRoot_eqv
#print axioms slabConnectedCarrierTargetSum_eqv_rootSum
#print axioms slabConnectedCarrierTargetSum_le_geom_partition
#print axioms slabConnectedSourceSizeSum_le_geom_partition

end YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierFixedSize
