/-
# Exact signed cancellation for the seven-cube outward cycle

The four connected 28-face polymers constructed in the preceding modules
realize the literal outward-query cycle

`011 -> 100 -> 000 -> 111 -> 011`.

This file first transports the face-membership certificates to the physical
component labels and then to singleton canonical families.  It then combines
those truth tables with the exact equality of the four complete cutoff-one
activities to obtain a pointwise-zero signed profile.
-/

import YMGap.Continuum.Z4OutwardCentralSmallLiftSignedPath
import YMGap.Continuum.Z4OutwardSevenCubeCycleActivity

namespace YMGap.Continuum.Z4OutwardSevenCubeSignedCycle

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4OutwardCentralSmallLiftSignedPath
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardSevenCubeCycleActivity
open YMGap.Continuum.Z4OutwardSevenCubeCycleConnectedRoots
open YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic event transport for an encoded geometric support -/

private theorem coarseX_event_true {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hface : outwardXQueryFace ∈ support) :
    physicalComponentSubsupportEvent 6 outwardXQuery
        (componentLabel root) = true := by
  apply componentLabel_subsupportEvent_true hroot
  rw [hencode]
  exact coarseFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .rightYZ support hface

private theorem coarseY_event_true {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hface : outwardYQueryFace ∈ support) :
    physicalComponentSubsupportEvent 6 outwardYQuery
        (componentLabel root) = true := by
  apply componentLabel_subsupportEvent_true hroot
  rw [hencode]
  exact coarseFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .backXZ support hface

private theorem coarseZ_event_true {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hface : outwardZQueryFace ∈ support) :
    physicalComponentSubsupportEvent 6 outwardZQuery
        (componentLabel root) = true := by
  apply componentLabel_subsupportEvent_true hroot
  rw [hencode]
  exact coarseFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .topXY support hface

private theorem coarseX_event_false {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardXQueryFace ∉ support) :
    physicalComponentSubsupportEvent 6 outwardXQuery
        (componentLabel root) = false := by
  apply componentLabel_subsupportEvent_false hroot
  rw [hencode]
  exact coarseFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .rightYZ support hbox hface

private theorem coarseY_event_false {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardYQueryFace ∉ support) :
    physicalComponentSubsupportEvent 6 outwardYQuery
        (componentLabel root) = false := by
  apply componentLabel_subsupportEvent_false hroot
  rw [hencode]
  exact coarseFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .backXZ support hbox hface

private theorem coarseZ_event_false {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardZQueryFace ∉ support) :
    physicalComponentSubsupportEvent 6 outwardZQuery
        (componentLabel root) = false := by
  apply componentLabel_subsupportEvent_false hroot
  rw [hencode]
  exact coarseFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .topXY support hbox hface

private theorem fineX_event_true {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hface : outwardXFineQueryFace ∈ support) :
    physicalComponentSubsupportEvent 6 outwardXFineQuery
        (componentLabel root) = true := by
  apply componentLabel_subsupportEvent_true hroot
  rw [hencode, outwardXFineQuery_eq_geometric]
  exact fineFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .rightYZ .origin support hface

private theorem fineY_event_true {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hface : outwardYFineQueryFace ∈ support) :
    physicalComponentSubsupportEvent 6 outwardYFineQuery
        (componentLabel root) = true := by
  apply componentLabel_subsupportEvent_true hroot
  rw [hencode, outwardYFineQuery_eq_geometric]
  exact fineFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .backXZ .origin support hface

private theorem fineZ_event_true {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hface : outwardZFineQueryFace ∈ support) :
    physicalComponentSubsupportEvent 6 outwardZFineQuery
        (componentLabel root) = true := by
  apply componentLabel_subsupportEvent_true hroot
  rw [hencode, outwardZFineQuery_eq_geometric]
  exact fineFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .topXY .origin support hface

private theorem fineX_event_false {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardXFineQueryFace ∉ support) :
    physicalComponentSubsupportEvent 6 outwardXFineQuery
        (componentLabel root) = false := by
  apply componentLabel_subsupportEvent_false hroot
  rw [hencode, outwardXFineQuery_eq_geometric]
  exact fineFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .rightYZ .origin support hbox hface

private theorem fineY_event_false {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardYFineQueryFace ∉ support) :
    physicalComponentSubsupportEvent 6 outwardYFineQuery
        (componentLabel root) = false := by
  apply componentLabel_subsupportEvent_false hroot
  rw [hencode, outwardYFineQuery_eq_geometric]
  exact fineFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .backXZ .origin support hbox hface

private theorem fineZ_event_false {root : List Nat} {support : List Z4Plaq}
    (hencode : root = geometricSupportIds 6 support)
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hface : outwardZFineQueryFace ∉ support) :
    physicalComponentSubsupportEvent 6 outwardZFineQuery
        (componentLabel root) = false := by
  apply componentLabel_subsupportEvent_false hroot
  rw [hencode, outwardZFineQuery_eq_geometric]
  exact fineFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .topXY .origin support hbox hface

private theorem coarsePattern_of_events {root : List Nat}
    {left shared right : Bool}
    (hx : physicalComponentSubsupportEvent 6 outwardXQuery
      (componentLabel root) = left)
    (hy : physicalComponentSubsupportEvent 6 outwardYQuery
      (componentLabel root) = shared)
    (hz : physicalComponentSubsupportEvent 6 outwardZQuery
      (componentLabel root) = right) :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel root) = (left, shared, right) := by
  unfold physicalComponentSubsupportPattern
  apply Prod.ext
  · simpa only [outwardCoarseQueries, componentSubsupportQueryLeft] using hx
  · apply Prod.ext
    · simpa only [outwardCoarseQueries,
        componentSubsupportQueryShared] using hy
    · simpa only [outwardCoarseQueries,
        componentSubsupportQueryRight] using hz

private theorem finePattern_of_events {root : List Nat}
    {left shared right : Bool}
    (hx : physicalComponentSubsupportEvent 6 outwardXFineQuery
      (componentLabel root) = left)
    (hy : physicalComponentSubsupportEvent 6 outwardYFineQuery
      (componentLabel root) = shared)
    (hz : physicalComponentSubsupportEvent 6 outwardZFineQuery
      (componentLabel root) = right) :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel root) = (left, shared, right) := by
  unfold physicalComponentSubsupportPattern
  apply Prod.ext
  · simpa only [outwardFineQueries, componentSubsupportQueryLeft] using hx
  · apply Prod.ext
    · simpa only [outwardFineQueries,
        componentSubsupportQueryShared] using hy
    · simpa only [outwardFineQueries,
        componentSubsupportQueryRight] using hz

/-! ## 2. Physical and singleton-family truth tables -/

theorem sevenCube011To100Root_coarsePattern_011 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
        (componentLabel sevenCube011To100Root) =
      (false, true, true) := by
  have hx := coarseX_event_false
      (root := sevenCube011To100Root)
      (support := sevenCube011To100Surface)
      rfl
      sevenCube011To100Root_mem_canonical
      sevenCube011To100Surface_subset_box_six
      sevenCube011To100_queryFaces.1.1
  have hy := coarseY_event_true
      (root := sevenCube011To100Root)
      (support := sevenCube011To100Surface)
      rfl
      sevenCube011To100Root_mem_canonical
      sevenCube011To100_queryFaces.1.2.1
  have hz := coarseZ_event_true
      (root := sevenCube011To100Root)
      (support := sevenCube011To100Surface)
      rfl
      sevenCube011To100Root_mem_canonical
      sevenCube011To100_queryFaces.1.2.2
  exact coarsePattern_of_events
    (root := sevenCube011To100Root) hx hy hz

theorem sevenCube011To100Root_finePattern_100 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
      (componentLabel sevenCube011To100Root) =
      (true, false, false) := by
  have hx := fineX_event_true
      (root := sevenCube011To100Root)
      (support := sevenCube011To100Surface) rfl
      sevenCube011To100Root_mem_canonical
      sevenCube011To100_queryFaces.2.1
  have hy := fineY_event_false
      (root := sevenCube011To100Root)
      (support := sevenCube011To100Surface) rfl
      sevenCube011To100Root_mem_canonical
      sevenCube011To100Surface_subset_box_six
      sevenCube011To100_queryFaces.2.2.1
  have hz := fineZ_event_false
      (root := sevenCube011To100Root)
      (support := sevenCube011To100Surface) rfl
      sevenCube011To100Root_mem_canonical
      sevenCube011To100Surface_subset_box_six
      sevenCube011To100_queryFaces.2.2.2
  exact finePattern_of_events
    (root := sevenCube011To100Root) hx hy hz

theorem sevenCube100To000Root_coarsePattern_100 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
      (componentLabel sevenCube100To000Root) =
      (true, false, false) := by
  have hx := coarseX_event_true
      (root := sevenCube100To000Root)
      (support := sevenCube100To000Surface) rfl
      sevenCube100To000Root_mem_canonical
      sevenCube100To000_queryFaces.1.1
  have hy := coarseY_event_false
      (root := sevenCube100To000Root)
      (support := sevenCube100To000Surface) rfl
      sevenCube100To000Root_mem_canonical
      sevenCube100To000Surface_subset_box_six
      sevenCube100To000_queryFaces.1.2.1
  have hz := coarseZ_event_false
      (root := sevenCube100To000Root)
      (support := sevenCube100To000Surface) rfl
      sevenCube100To000Root_mem_canonical
      sevenCube100To000Surface_subset_box_six
      sevenCube100To000_queryFaces.1.2.2
  exact coarsePattern_of_events
    (root := sevenCube100To000Root) hx hy hz

theorem sevenCube100To000Root_finePattern_000 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
      (componentLabel sevenCube100To000Root) =
      (false, false, false) := by
  have hx := fineX_event_false
      (root := sevenCube100To000Root)
      (support := sevenCube100To000Surface) rfl
      sevenCube100To000Root_mem_canonical
      sevenCube100To000Surface_subset_box_six
      sevenCube100To000_queryFaces.2.1
  have hy := fineY_event_false
      (root := sevenCube100To000Root)
      (support := sevenCube100To000Surface) rfl
      sevenCube100To000Root_mem_canonical
      sevenCube100To000Surface_subset_box_six
      sevenCube100To000_queryFaces.2.2.1
  have hz := fineZ_event_false
      (root := sevenCube100To000Root)
      (support := sevenCube100To000Surface) rfl
      sevenCube100To000Root_mem_canonical
      sevenCube100To000Surface_subset_box_six
      sevenCube100To000_queryFaces.2.2.2
  exact finePattern_of_events
    (root := sevenCube100To000Root) hx hy hz

theorem sevenCube000To111Root_coarsePattern_000 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
      (componentLabel sevenCube000To111Root) =
      (false, false, false) := by
  have hx := coarseX_event_false
      (root := sevenCube000To111Root)
      (support := sevenCube000To111Surface) rfl
      sevenCube000To111Root_mem_canonical
      sevenCube000To111Surface_subset_box_six
      sevenCube000To111_queryFaces.1.1
  have hy := coarseY_event_false
      (root := sevenCube000To111Root)
      (support := sevenCube000To111Surface) rfl
      sevenCube000To111Root_mem_canonical
      sevenCube000To111Surface_subset_box_six
      sevenCube000To111_queryFaces.1.2.1
  have hz := coarseZ_event_false
      (root := sevenCube000To111Root)
      (support := sevenCube000To111Surface) rfl
      sevenCube000To111Root_mem_canonical
      sevenCube000To111Surface_subset_box_six
      sevenCube000To111_queryFaces.1.2.2
  exact coarsePattern_of_events
    (root := sevenCube000To111Root) hx hy hz

theorem sevenCube000To111Root_finePattern_111 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
      (componentLabel sevenCube000To111Root) =
      (true, true, true) := by
  have hx := fineX_event_true
      (root := sevenCube000To111Root)
      (support := sevenCube000To111Surface) rfl
      sevenCube000To111Root_mem_canonical
      sevenCube000To111_queryFaces.2.1
  have hy := fineY_event_true
      (root := sevenCube000To111Root)
      (support := sevenCube000To111Surface) rfl
      sevenCube000To111Root_mem_canonical
      sevenCube000To111_queryFaces.2.2.1
  have hz := fineZ_event_true
      (root := sevenCube000To111Root)
      (support := sevenCube000To111Surface) rfl
      sevenCube000To111Root_mem_canonical
      sevenCube000To111_queryFaces.2.2.2
  exact finePattern_of_events
    (root := sevenCube000To111Root) hx hy hz

theorem sevenCube111To011Root_coarsePattern_111 :
    physicalComponentSubsupportPattern 6 outwardCoarseQueries
      (componentLabel sevenCube111To011Root) =
      (true, true, true) := by
  have hx := coarseX_event_true
      (root := sevenCube111To011Root)
      (support := sevenCube111To011Surface) rfl
      sevenCube111To011Root_mem_canonical
      sevenCube111To011_queryFaces.1.1
  have hy := coarseY_event_true
      (root := sevenCube111To011Root)
      (support := sevenCube111To011Surface) rfl
      sevenCube111To011Root_mem_canonical
      sevenCube111To011_queryFaces.1.2.1
  have hz := coarseZ_event_true
      (root := sevenCube111To011Root)
      (support := sevenCube111To011Surface) rfl
      sevenCube111To011Root_mem_canonical
      sevenCube111To011_queryFaces.1.2.2
  exact coarsePattern_of_events
    (root := sevenCube111To011Root) hx hy hz

theorem sevenCube111To011Root_finePattern_011 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
      (componentLabel sevenCube111To011Root) =
      (false, true, true) := by
  have hx := fineX_event_false
      (root := sevenCube111To011Root)
      (support := sevenCube111To011Surface) rfl
      sevenCube111To011Root_mem_canonical
      sevenCube111To011Surface_subset_box_six
      sevenCube111To011_queryFaces.2.1
  have hy := fineY_event_true
      (root := sevenCube111To011Root)
      (support := sevenCube111To011Surface) rfl
      sevenCube111To011Root_mem_canonical
      sevenCube111To011_queryFaces.2.2.1
  have hz := fineZ_event_true
      (root := sevenCube111To011Root)
      (support := sevenCube111To011Surface) rfl
      sevenCube111To011Root_mem_canonical
      sevenCube111To011_queryFaces.2.2.2
  exact finePattern_of_events
    (root := sevenCube111To011Root) hx hy hz

private theorem singletonFamilyPattern_of_physicalPattern
    {root : List Nat} {queries : ComponentSubsupportQueryTriple}
    {pattern : ThreeBlockPattern}
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hpattern : physicalComponentSubsupportPattern 6 queries
      (componentLabel root) = pattern) :
    outwardComponentSubsupportFamilyPattern queries [root] = pattern := by
  unfold physicalComponentSubsupportPattern
    physicalComponentSubsupportEvent at hpattern
  rw [componentLabelAmbientFamily_eq_singleton hroot] at hpattern
  simpa only [outwardComponentSubsupportFamilyPattern] using hpattern

theorem sevenCube011To100_coarseFamilyPattern_011 :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        [sevenCube011To100Root] = (false, true, true) :=
  singletonFamilyPattern_of_physicalPattern
    sevenCube011To100Root_mem_canonical
    sevenCube011To100Root_coarsePattern_011

theorem sevenCube011To100_fineFamilyPattern_100 :
    outwardComponentSubsupportFamilyPattern outwardFineQueries
        [sevenCube011To100Root] = (true, false, false) :=
  singletonFamilyPattern_of_physicalPattern
    sevenCube011To100Root_mem_canonical
    sevenCube011To100Root_finePattern_100

theorem sevenCube100To000_coarseFamilyPattern_100 :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        [sevenCube100To000Root] = (true, false, false) :=
  singletonFamilyPattern_of_physicalPattern
    sevenCube100To000Root_mem_canonical
    sevenCube100To000Root_coarsePattern_100

theorem sevenCube100To000_fineFamilyPattern_000 :
    outwardComponentSubsupportFamilyPattern outwardFineQueries
        [sevenCube100To000Root] = (false, false, false) :=
  singletonFamilyPattern_of_physicalPattern
    sevenCube100To000Root_mem_canonical
    sevenCube100To000Root_finePattern_000

theorem sevenCube000To111_coarseFamilyPattern_000 :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        [sevenCube000To111Root] = (false, false, false) :=
  singletonFamilyPattern_of_physicalPattern
    sevenCube000To111Root_mem_canonical
    sevenCube000To111Root_coarsePattern_000

theorem sevenCube000To111_fineFamilyPattern_111 :
    outwardComponentSubsupportFamilyPattern outwardFineQueries
        [sevenCube000To111Root] = (true, true, true) :=
  singletonFamilyPattern_of_physicalPattern
    sevenCube000To111Root_mem_canonical
    sevenCube000To111Root_finePattern_111

theorem sevenCube111To011_coarseFamilyPattern_111 :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        [sevenCube111To011Root] = (true, true, true) :=
  singletonFamilyPattern_of_physicalPattern
    sevenCube111To011Root_mem_canonical
    sevenCube111To011Root_coarsePattern_111

theorem sevenCube111To011_fineFamilyPattern_011 :
    outwardComponentSubsupportFamilyPattern outwardFineQueries
        [sevenCube111To011Root] = (false, true, true) :=
  singletonFamilyPattern_of_physicalPattern
    sevenCube111To011Root_mem_canonical
    sevenCube111To011Root_finePattern_011

#print axioms sevenCube011To100Root_coarsePattern_011
#print axioms sevenCube011To100Root_finePattern_100
#print axioms sevenCube100To000Root_coarsePattern_100
#print axioms sevenCube100To000Root_finePattern_000
#print axioms sevenCube000To111Root_coarsePattern_000
#print axioms sevenCube000To111Root_finePattern_111
#print axioms sevenCube111To011Root_coarsePattern_111
#print axioms sevenCube111To011Root_finePattern_011
#print axioms sevenCube011To100_coarseFamilyPattern_011
#print axioms sevenCube111To011_fineFamilyPattern_011

end YMGap.Continuum.Z4OutwardSevenCubeSignedCycle
