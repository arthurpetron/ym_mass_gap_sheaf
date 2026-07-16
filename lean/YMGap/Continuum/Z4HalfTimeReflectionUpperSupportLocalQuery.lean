/-
# Reading reflected-upper local queries from lower support coordinates

The right coordinate of the half-time Gram kernel is the upper physical
labelling read through reflection on the lower face identifiers.  This file
constructs the corresponding ambient face reindexing and proves that the
complete right support decodes local occurrence queries on the original
strictly upper canonical roots.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry

namespace YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart
open YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality

/-! ## 1. The ambient numerical reflection involution on slab faces -/

/-- Numerical ambient identifier of the geometrically reflected plaquette.
It is used only with faces known to belong to the corrected slab. -/
def centralAmbientFaceReflectId (half id : Nat) : Nat :=
  listIndexOf
    (timeReflectPlaquette (centralExtent half)
      (boxPlaquetteAt (centralAmbient half) id))
    (boxPlaquettes (centralAmbient half))

theorem centralAmbientFaceReflectId_physical
    {half id : Nat}
    (hid : id ∈ physicalFaceEdges (centralAmbient half))
    (hslab : boxPlaquetteAt (centralAmbient half) id ∈
      boundaryCompleteSlabPlaquettes (centralExtent half)) :
    centralAmbientFaceReflectId half id ∈
      physicalFaceEdges (centralAmbient half) := by
  unfold centralAmbientFaceReflectId physicalFaceEdges plaquetteEdgeCount
  apply List.mem_range.mpr
  apply listIndexOf_lt_of_mem
  exact (mem_boundaryCompleteSlabPlaquettes _ _).1
    (timeReflectPlaquette_mem_boundaryCompleteSlab hslab) |>.1

theorem boxPlaquetteAt_centralAmbientFaceReflectId
    {half id : Nat}
    (hid : id ∈ physicalFaceEdges (centralAmbient half))
    (hslab : boxPlaquetteAt (centralAmbient half) id ∈
      boundaryCompleteSlabPlaquettes (centralExtent half)) :
    boxPlaquetteAt (centralAmbient half)
        (centralAmbientFaceReflectId half id) =
      timeReflectPlaquette (centralExtent half)
        (boxPlaquetteAt (centralAmbient half) id) := by
  unfold boxPlaquetteAt centralAmbientFaceReflectId
  apply getD_listIndexOf_of_mem
  exact (mem_boundaryCompleteSlabPlaquettes _ _).1
    (timeReflectPlaquette_mem_boundaryCompleteSlab hslab) |>.1

theorem centralAmbientFaceReflectId_involutive
    {half id : Nat}
    (hid : id ∈ physicalFaceEdges (centralAmbient half))
    (hslab : boxPlaquetteAt (centralAmbient half) id ∈
      boundaryCompleteSlabPlaquettes (centralExtent half)) :
    centralAmbientFaceReflectId half
        (centralAmbientFaceReflectId half id) = id := by
  have hreflectedPhysical := centralAmbientFaceReflectId_physical hid hslab
  have hreflectedSlab :
      boxPlaquetteAt (centralAmbient half)
          (centralAmbientFaceReflectId half id) ∈
        boundaryCompleteSlabPlaquettes (centralExtent half) := by
    rw [boxPlaquetteAt_centralAmbientFaceReflectId hid hslab]
    exact timeReflectPlaquette_mem_boundaryCompleteSlab hslab
  apply boxPlaquetteAt_injective_on_physical
    (centralAmbientFaceReflectId_physical hreflectedPhysical hreflectedSlab) hid
  rw [boxPlaquetteAt_centralAmbientFaceReflectId
      hreflectedPhysical hreflectedSlab,
    boxPlaquetteAt_centralAmbientFaceReflectId hid hslab]
  exact timeReflectPlaquette_involutive
    (centralExtent half) _
    ((mem_boundaryCompleteSlabPlaquettes _ _).1 hslab).2

private theorem slabPlaquetteAt_eq_of_enumerate_local
    {extent id : Nat}
    {plaquette : YMGap.Continuum.ClusterCount4DProgress.Z4Plaq}
    (hindexed : (id, plaquette) ∈
      enumerate (boundaryCompleteSlabPlaquettes extent)) :
    slabPlaquetteAt extent id = plaquette := by
  unfold slabPlaquetteAt
  exact enumerate_getD_of_mem fallbackPlaquette hindexed

/-! ## 2. Pointwise reconstruction of the reflected upper support -/

/-- On a lower ambient face, the support reconstructed from the right Gram
coordinate is exactly the occupied bit of the geometrically reflected upper
ambient face in the original physical labelling. -/
theorem centralReflectedUpperSupportAmbient_memberB_eq_physical
    (half : Nat) (physical : EdgeLabelling) {targetId : Nat}
    (htarget : targetId ∈ physicalFaceEdges (centralAmbient half))
    (hlower : plaquetteHalfSide half
      (boxPlaquetteAt (centralAmbient half) targetId) = .lower) :
    memberB
        (centralLowerSupportAmbientFaces half
          (centralHalfSupportCode half
            (centralReflectedUpperRestriction half
              (ambientToSlabPhysical (centralExtent half) physical))))
        targetId =
      memberB (excitedPlaquetteIds (centralAmbient half) physical)
        (centralAmbientFaceReflectId half targetId) := by
  have hslab := lowerAmbientFace_mem_centralSlab htarget hlower
  obtain ⟨sourceId, hsourceIndexed⟩ := exists_mem_enumerate hslab
  have hsourcePhysical : sourceId ∈
      slabPhysicalFaceEdges (centralExtent half) := by
    unfold slabPhysicalFaceEdges
    exact List.mem_range.mpr (enumerate_index_lt hsourceIndexed)
  have hsourceAt :
      slabPlaquetteAt (centralExtent half) sourceId =
        boxPlaquetteAt (centralAmbient half) targetId :=
    slabPlaquetteAt_eq_of_enumerate_local hsourceIndexed
  have hsourceLower : sourceId ∈ centralLowerFaceIds half := by
    apply mem_centralLowerFaceIds.mpr
    exact ⟨hsourcePhysical, by simpa only [hsourceAt] using hlower⟩
  have htargetIndexed :
      (targetId, boxPlaquetteAt (centralAmbient half) targetId) ∈
        enumerate (boxPlaquettes (centralAmbient half)) := by
    apply boxPlaquetteAt_mem_enumerate
    exact physicalFaceId_lt htarget
  let reflectedId := centralAmbientFaceReflectId half targetId
  have hreflectedPhysical : reflectedId ∈
      physicalFaceEdges (centralAmbient half) :=
    centralAmbientFaceReflectId_physical htarget hslab
  have hreflectedAt :
      boxPlaquetteAt (centralAmbient half) reflectedId =
        timeReflectPlaquette (centralExtent half)
          (boxPlaquetteAt (centralAmbient half) targetId) :=
    boxPlaquetteAt_centralAmbientFaceReflectId htarget hslab
  have hreflectedIndexed :
      (reflectedId, boxPlaquetteAt (centralAmbient half) reflectedId) ∈
        enumerate (boxPlaquettes (centralAmbient half)) := by
    apply boxPlaquetteAt_mem_enumerate
    exact physicalFaceId_lt hreflectedPhysical
  apply Bool.eq_iff_iff.mpr
  simp only [memberB_eq_true_iff]
  constructor
  · intro hreconstructed
    have hpositiveReconstructed := (List.mem_filter.mp hreconstructed).2
    simp only [decide_eq_true_eq] at hpositiveReconstructed
    unfold centralLowerSupportAmbientFaces at hreconstructed
    have hspin :
        slabToAmbientPhysical (centralExtent half)
            (componentLabel
              (centralHalfSupportCode half
                (centralReflectedUpperRestriction half
                  (ambientToSlabPhysical (centralExtent half) physical))))
            targetId =
          componentLabel
              (centralHalfSupportCode half
                (centralReflectedUpperRestriction half
                  (ambientToSlabPhysical (centralExtent half) physical)))
            sourceId := by
      rw [slabToAmbientPhysical_eq_on_enumerate htargetIndexed,
        slabGeometricSpin_eq_of_enumerate hsourceIndexed]
    rw [hspin] at hpositiveReconstructed
    have hsourceSupport : sourceId ∈
        centralHalfSupportCode half
          (centralReflectedUpperRestriction half
            (ambientToSlabPhysical (centralExtent half) physical)) := by
      by_cases hmem : sourceId ∈
          centralHalfSupportCode half
            (centralReflectedUpperRestriction half
              (ambientToSlabPhysical (centralExtent half) physical))
      · exact hmem
      · rw [componentLabel_eq_zero_of_not_mem hmem]
          at hpositiveReconstructed
        omega
    have hpositiveSource := (List.mem_filter.mp hsourceSupport).2
    simp only [decide_eq_true_eq] at hpositiveSource
    unfold centralReflectedUpperRestriction at hpositiveSource
    rw [if_pos hsourceLower,
      ambientToSlabPhysical_eq_on_physical
        (slabFaceReflectId_physical hsourcePhysical),
      slabPlaquetteAt_slabFaceReflectId hsourcePhysical,
      hsourceAt, ← hreflectedAt] at hpositiveSource
    change 1 ≤ geometricSpinOfPhysical (centralAmbient half) physical
      (boxPlaquetteAt (centralAmbient half) reflectedId) at hpositiveSource
    rw [geometricSpinOfPhysical_eq_of_enumerate hreflectedIndexed]
      at hpositiveSource
    apply List.mem_filter.mpr
    exact ⟨hreflectedPhysical, decide_eq_true hpositiveSource⟩
  · intro horiginal
    have hpositiveOriginal := (List.mem_filter.mp horiginal).2
    simp only [decide_eq_true_eq] at hpositiveOriginal
    have hpositiveSource : 1 ≤
        centralReflectedUpperRestriction half
          (ambientToSlabPhysical (centralExtent half) physical) sourceId := by
      unfold centralReflectedUpperRestriction
      rw [if_pos hsourceLower,
        ambientToSlabPhysical_eq_on_physical
          (slabFaceReflectId_physical hsourcePhysical),
        slabPlaquetteAt_slabFaceReflectId hsourcePhysical,
        hsourceAt, ← hreflectedAt]
      change 1 ≤ geometricSpinOfPhysical (centralAmbient half) physical
        (boxPlaquetteAt (centralAmbient half) reflectedId)
      rw [geometricSpinOfPhysical_eq_of_enumerate hreflectedIndexed]
      exact hpositiveOriginal
    have hsourceSupport : sourceId ∈
        centralHalfSupportCode half
          (centralReflectedUpperRestriction half
            (ambientToSlabPhysical (centralExtent half) physical)) := by
      unfold centralHalfSupportCode
      apply List.mem_filter.mpr
      exact ⟨hsourceLower, decide_eq_true hpositiveSource⟩
    have hcomponent :
        componentLabel
          (centralHalfSupportCode half
            (centralReflectedUpperRestriction half
              (ambientToSlabPhysical (centralExtent half) physical)))
          sourceId = 1 :=
      componentLabel_eq_one_iff.mpr hsourceSupport
    unfold centralLowerSupportAmbientFaces excitedPlaquetteIds
    apply List.mem_filter.mpr
    refine ⟨htarget, decide_eq_true ?_⟩
    rw [slabToAmbientPhysical_eq_on_enumerate htargetIndexed,
      slabGeometricSpin_eq_of_enumerate hsourceIndexed, hcomponent]
    exact Nat.le_refl 1

/-! ## 3. Reflection transports canonical-root membership -/

theorem centralReflectedCanonicalRoot_supported
    {half : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers (centralAmbient half))
    (hsupported : canonicalPolymerSlabSupportedB
      (centralExtent half) root = true) :
    canonicalPolymerSlabSupportedB (centralExtent half)
      (centralReflectedCanonicalRoot half root) = true := by
  unfold canonicalPolymerSlabSupportedB
  apply List.all_eq_true.mpr
  intro face hface
  apply decide_eq_true
  have hgeom : boxPlaquetteAt (centralAmbient half) face ∈
      geometricPolymer (centralAmbient half)
        (centralReflectedCanonicalRoot half root) :=
    List.mem_map.mpr ⟨face, hface, rfl⟩
  have hmapped :=
    (centralReflectedCanonicalRoot_sameSupport hsupported).1 _ hgeom
  obtain ⟨sourcePlaquette, hsourcePlaquette, hreflectedEq⟩ :=
    List.mem_map.mp hmapped
  obtain ⟨sourceFace, hsourceFace, hsourceEq⟩ :=
    List.mem_map.mp hsourcePlaquette
  have hsourceSlab := canonicalPolymerSlabSupported_face
    hsupported hsourceFace
  change boxPlaquetteAt (centralAmbient half) face ∈
    boundaryCompleteSlabPlaquettes (centralExtent half)
  rw [← hreflectedEq, ← hsourceEq]
  exact timeReflectPlaquette_mem_boundaryCompleteSlab hsourceSlab

/-- Membership in a reflected canonical root is equivalent to membership of
the ambient reflected identifier in the source root.  The statement is
restricted to corrected-slab faces, exactly the domain on which the
reflection is a genuine ambient permutation. -/
theorem mem_centralReflectedCanonicalRoot_iff_reflectId_mem
    {half : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers (centralAmbient half))
    (hsupported : canonicalPolymerSlabSupportedB
      (centralExtent half) root = true)
    {face : Nat}
    (hfacePhysical : face ∈ physicalFaceEdges (centralAmbient half))
    (hfaceSlab : boxPlaquetteAt (centralAmbient half) face ∈
      boundaryCompleteSlabPlaquettes (centralExtent half)) :
    face ∈ centralReflectedCanonicalRoot half root ↔
      centralAmbientFaceReflectId half face ∈ root := by
  have hreflectedPhysical :=
    centralAmbientFaceReflectId_physical hfacePhysical hfaceSlab
  have hlowerCanonical := centralReflectedCanonicalRoot_canonical
    hroot hsupported
  constructor
  · intro hface
    have hgeom : boxPlaquetteAt (centralAmbient half) face ∈
        geometricPolymer (centralAmbient half)
          (centralReflectedCanonicalRoot half root) :=
      List.mem_map.mpr ⟨face, hface, rfl⟩
    have hmapped :=
      (centralReflectedCanonicalRoot_sameSupport hsupported).1 _ hgeom
    obtain ⟨sourcePlaquette, hsourcePlaquette, hreflectedEq⟩ :=
      List.mem_map.mp hmapped
    obtain ⟨sourceFace, hsourceFace, hsourceEq⟩ :=
      List.mem_map.mp hsourcePlaquette
    have hsourcePhysical := mem_of_mem_sublists
      (physicalFaceEdges (centralAmbient half)) root
      (canonicalSurfacePolymer_mem_faceSupports hroot)
      sourceFace hsourceFace
    have hsourceAdmissible :=
      (mem_boundaryCompleteSlabPlaquettes _ _).1
        (canonicalPolymerSlabSupported_face hsupported hsourceFace) |>.2
    rw [hsourceEq] at hsourceAdmissible
    have hback := congrArg (timeReflectPlaquette (centralExtent half))
      hreflectedEq
    rw [timeReflectPlaquette_involutive
      (centralExtent half) sourcePlaquette hsourceAdmissible] at hback
    have hidEq : centralAmbientFaceReflectId half face = sourceFace := by
      apply boxPlaquetteAt_injective_on_physical
        hreflectedPhysical hsourcePhysical
      rw [boxPlaquetteAt_centralAmbientFaceReflectId
        hfacePhysical hfaceSlab, hsourceEq]
      exact hback.symm
    rw [hidEq]
    exact hsourceFace
  · intro hreflected
    have hreflectedGeom :
        boxPlaquetteAt (centralAmbient half)
            (centralAmbientFaceReflectId half face) ∈
          geometricPolymer (centralAmbient half) root :=
      List.mem_map.mpr ⟨_, hreflected, rfl⟩
    have hmapped : boxPlaquetteAt (centralAmbient half) face ∈
        (geometricPolymer (centralAmbient half) root).map
          (timeReflectPlaquette (centralExtent half)) := by
      apply List.mem_map.mpr
      refine ⟨boxPlaquetteAt (centralAmbient half)
          (centralAmbientFaceReflectId half face), hreflectedGeom, ?_⟩
      rw [boxPlaquetteAt_centralAmbientFaceReflectId
        hfacePhysical hfaceSlab]
      exact timeReflectPlaquette_involutive
        (centralExtent half)
        (boxPlaquetteAt (centralAmbient half) face)
        ((mem_boundaryCompleteSlabPlaquettes _ _).1 hfaceSlab).2
    have hlowerGeom :=
      (centralReflectedCanonicalRoot_sameSupport hsupported).2 _ hmapped
    obtain ⟨lowerFace, hlowerFace, hlowerEq⟩ :=
      List.mem_map.mp hlowerGeom
    have hlowerPhysical := mem_of_mem_sublists
      (physicalFaceEdges (centralAmbient half))
      (centralReflectedCanonicalRoot half root)
      (canonicalSurfacePolymer_mem_faceSupports hlowerCanonical)
      lowerFace hlowerFace
    have hlowerIdEq : lowerFace = face :=
      boxPlaquetteAt_injective_on_physical
        hlowerPhysical hfacePhysical hlowerEq
    simpa only [hlowerIdEq] using hlowerFace

/-! ## 4. Reflection transports the complete one-link query shell -/

theorem ambientFace_mem_centralSlab_of_time_lt
    {half face : Nat}
    (hface : face ∈ physicalFaceEdges (centralAmbient half))
    (htime :
      (boxPlaquetteAt (centralAmbient half) face).1.2.2.2 <
        centralExtent half) :
    boxPlaquetteAt (centralAmbient half) face ∈
      boundaryCompleteSlabPlaquettes (centralExtent half) := by
  apply (mem_boundaryCompleteSlabPlaquettes _ _).2
  constructor
  · simpa only [centralAmbient] using
      (boxPlaquetteAt_mem_boxPlaquettes_of_physical hface)
  · generalize hplaquette :
      boxPlaquetteAt (centralAmbient half) face = plaquette at htime ⊢
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
    cases plane <;>
      simp [plaquetteTimeAdmissible] at htime ⊢ <;>
      omega

theorem centralStrictUpperCanonicalRoot_exterior_mem_slab
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (centralAmbient radius)
      (centralStrictUpperCanonicalRoot radius base root)) :
    boxPlaquetteAt (centralAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (centralExtent radius) := by
  obtain ⟨hfacePhysical, _houtside, inside, hinside, hadj⟩ :=
    (mem_canonicalPolymerExteriorFaceQueries_iff
      (centralAmbient radius)
      (centralStrictUpperCanonicalRoot radius base root) face).1 hface
  have hinsideTime :
      (boxPlaquetteAt (centralAmbient radius) inside).1.2.2.2 <
        radius + strictQueryBase base := by
    exact centralFaceQueryCanonicalRoot_time_lt hbase
      (strictQuerySourceRoot_canonical hroot) hinside
  have hforward := actualAdjacentOfFaceLinkAdjacent hadj
  have hreverse : z4Chain.toLattice.Adjacent
      (boxPlaquetteAt (centralAmbient radius) face)
      (boxPlaquetteAt (centralAmbient radius) inside) := {
    link := hforward.link
    on_p := hforward.on_q
    on_q := hforward.on_p
  }
  have htimeStep := adjacent_time_le_add_one hreverse
  apply ambientFace_mem_centralSlab_of_time_lt hfacePhysical
  unfold centralExtent
  omega

theorem faceLinkAdjacentB_centralAmbientFaceReflectId
    {half left right : Nat}
    (hleftPhysical : left ∈ physicalFaceEdges (centralAmbient half))
    (hleftSlab : boxPlaquetteAt (centralAmbient half) left ∈
      boundaryCompleteSlabPlaquettes (centralExtent half))
    (hrightPhysical : right ∈ physicalFaceEdges (centralAmbient half))
    (hrightSlab : boxPlaquetteAt (centralAmbient half) right ∈
      boundaryCompleteSlabPlaquettes (centralExtent half))
    (hadj : faceLinkAdjacentB (centralAmbient half) left right = true) :
    faceLinkAdjacentB (centralAmbient half)
        (centralAmbientFaceReflectId half left)
        (centralAmbientFaceReflectId half right) = true := by
  apply faceLinkAdjacentB_true_of_actualAdjacent
    (centralAmbientFaceReflectId_physical hleftPhysical hleftSlab)
    (centralAmbientFaceReflectId_physical hrightPhysical hrightSlab)
  have hreflected := timeReflectAdjacent
    (centralExtent half)
    ((mem_boundaryCompleteSlabPlaquettes _ _).1 hleftSlab).2
    ((mem_boundaryCompleteSlabPlaquettes _ _).1 hrightSlab).2
    (actualAdjacentOfFaceLinkAdjacent hadj)
  simpa only [boxPlaquetteAt_centralAmbientFaceReflectId
    hleftPhysical hleftSlab,
    boxPlaquetteAt_centralAmbientFaceReflectId
      hrightPhysical hrightSlab] using hreflected

/-- The exterior query shell of a strict lower reflected root is exactly the
ambient reflection of the exterior query shell of its strict upper source. -/
theorem mem_strictLower_exterior_iff_reflectId_mem_strictUpper_exterior
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hfacePhysical : face ∈ physicalFaceEdges (centralAmbient radius))
    (hfaceSlab : boxPlaquetteAt (centralAmbient radius) face ∈
      boundaryCompleteSlabPlaquettes (centralExtent radius)) :
    face ∈ canonicalPolymerExteriorFaceQueries
        (centralAmbient radius)
        (centralStrictLowerCanonicalRoot radius base root) ↔
      centralAmbientFaceReflectId radius face ∈
        canonicalPolymerExteriorFaceQueries
          (centralAmbient radius)
          (centralStrictUpperCanonicalRoot radius base root) := by
  let upper := centralStrictUpperCanonicalRoot radius base root
  let lower := centralStrictLowerCanonicalRoot radius base root
  have hupperCanonical := centralStrictUpperCanonicalRoot_canonical hbase hroot
  have hupperSupported := centralStrictUpperCanonicalRoot_supported hbase hroot
  have hlowerCanonical := centralStrictLowerCanonicalRoot_canonical hbase hroot
  have hlowerSupported := centralReflectedCanonicalRoot_supported
    hupperCanonical hupperSupported
  have hreflectedPhysical :=
    centralAmbientFaceReflectId_physical hfacePhysical hfaceSlab
  have hreflectedSlab :
      boxPlaquetteAt (centralAmbient radius)
          (centralAmbientFaceReflectId radius face) ∈
        boundaryCompleteSlabPlaquettes (centralExtent radius) := by
    rw [boxPlaquetteAt_centralAmbientFaceReflectId hfacePhysical hfaceSlab]
    exact timeReflectPlaquette_mem_boundaryCompleteSlab hfaceSlab
  constructor
  · intro hlowerExterior
    obtain ⟨_hlowerPhysical, hlowerOutside, inside,
        hinside, hadj⟩ :=
      (mem_canonicalPolymerExteriorFaceQueries_iff
        (centralAmbient radius) lower face).1 hlowerExterior
    have hinsidePhysical := mem_of_mem_sublists
      (physicalFaceEdges (centralAmbient radius)) lower
      (canonicalSurfacePolymer_mem_faceSupports hlowerCanonical)
      inside hinside
    have hinsideSlab := canonicalPolymerSlabSupported_face
      hlowerSupported hinside
    have hinsideUpper : centralAmbientFaceReflectId radius inside ∈ upper :=
      (mem_centralReflectedCanonicalRoot_iff_reflectId_mem
        hupperCanonical hupperSupported hinsidePhysical hinsideSlab).1 hinside
    apply (mem_canonicalPolymerExteriorFaceQueries_iff
      (centralAmbient radius) upper
      (centralAmbientFaceReflectId radius face)).2
    refine ⟨hreflectedPhysical, ?_,
      centralAmbientFaceReflectId radius inside, hinsideUpper, ?_⟩
    · intro hfaceUpper
      exact hlowerOutside
        ((mem_centralReflectedCanonicalRoot_iff_reflectId_mem
          hupperCanonical hupperSupported hfacePhysical hfaceSlab).2
            hfaceUpper)
    · exact faceLinkAdjacentB_centralAmbientFaceReflectId
        hinsidePhysical hinsideSlab hfacePhysical hfaceSlab hadj
  · intro hupperExterior
    obtain ⟨_hreflectedPhysical, hupperOutside, inside,
        hinside, hadj⟩ :=
      (mem_canonicalPolymerExteriorFaceQueries_iff
        (centralAmbient radius) upper
        (centralAmbientFaceReflectId radius face)).1 hupperExterior
    have hinsidePhysical := mem_of_mem_sublists
      (physicalFaceEdges (centralAmbient radius)) upper
      (canonicalSurfacePolymer_mem_faceSupports hupperCanonical)
      inside hinside
    have hinsideSlab := canonicalPolymerSlabSupported_face
      hupperSupported hinside
    let lowerInside := centralAmbientFaceReflectId radius inside
    have hlowerInsidePhysical : lowerInside ∈
        physicalFaceEdges (centralAmbient radius) :=
      centralAmbientFaceReflectId_physical hinsidePhysical hinsideSlab
    have hlowerInsideSlab :
        boxPlaquetteAt (centralAmbient radius) lowerInside ∈
          boundaryCompleteSlabPlaquettes (centralExtent radius) := by
      rw [boxPlaquetteAt_centralAmbientFaceReflectId
        hinsidePhysical hinsideSlab]
      exact timeReflectPlaquette_mem_boundaryCompleteSlab hinsideSlab
    have hlowerInside : lowerInside ∈ lower := by
      apply (mem_centralReflectedCanonicalRoot_iff_reflectId_mem
        hupperCanonical hupperSupported
          hlowerInsidePhysical hlowerInsideSlab).2
      rw [centralAmbientFaceReflectId_involutive
        hinsidePhysical hinsideSlab]
      exact hinside
    apply (mem_canonicalPolymerExteriorFaceQueries_iff
      (centralAmbient radius) lower face).2
    refine ⟨hfacePhysical, ?_, lowerInside, hlowerInside, ?_⟩
    · intro hfaceLower
      exact hupperOutside
        ((mem_centralReflectedCanonicalRoot_iff_reflectId_mem
          hupperCanonical hupperSupported hfacePhysical hfaceSlab).1
            hfaceLower)
    · have hreflectedAdj :=
        faceLinkAdjacentB_centralAmbientFaceReflectId
          hinsidePhysical hinsideSlab
          hreflectedPhysical hreflectedSlab hadj
      rw [centralAmbientFaceReflectId_involutive
        hfacePhysical hfaceSlab] at hreflectedAdj
      exact hreflectedAdj

/-! ## 5. The reflected right support decides the strict upper query -/

theorem centralStrictReflectedSupportQueryEventB_eq_upperPhysical
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    (physical : EdgeLabelling) :
    canonicalPolymerSupportQueryEventB (centralAmbient radius)
        (centralStrictLowerCanonicalRoot radius base root)
        (centralLowerSupportAmbientFaces radius
          (centralHalfSupportCode radius
            (centralReflectedUpperRestriction radius
              (ambientToSlabPhysical (centralExtent radius) physical)))) =
      canonicalPolymerSupportQueryEventB (centralAmbient radius)
        (centralStrictUpperCanonicalRoot radius base root)
        (excitedPlaquetteIds (centralAmbient radius) physical) := by
  have hupperCanonical := centralStrictUpperCanonicalRoot_canonical hbase hroot
  have hupperSupported := centralStrictUpperCanonicalRoot_supported hbase hroot
  have hlowerCanonical := centralStrictLowerCanonicalRoot_canonical hbase hroot
  have hlowerSupported := centralReflectedCanonicalRoot_supported
    hupperCanonical hupperSupported
  unfold canonicalPolymerSupportQueryEventB
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · intro hlowerQuery
    constructor
    · apply List.all_eq_true.mpr
      intro upperFace hupperFace
      have hupperFacePhysical := mem_of_mem_sublists
        (physicalFaceEdges (centralAmbient radius))
        (centralStrictUpperCanonicalRoot radius base root)
        (canonicalSurfacePolymer_mem_faceSupports hupperCanonical)
        upperFace hupperFace
      have hupperFaceSlab := canonicalPolymerSlabSupported_face
        hupperSupported hupperFace
      let lowerFace := centralAmbientFaceReflectId radius upperFace
      have hlowerFacePhysical : lowerFace ∈
          physicalFaceEdges (centralAmbient radius) :=
        centralAmbientFaceReflectId_physical
          hupperFacePhysical hupperFaceSlab
      have hlowerFaceSlab :
          boxPlaquetteAt (centralAmbient radius) lowerFace ∈
            boundaryCompleteSlabPlaquettes (centralExtent radius) := by
        rw [boxPlaquetteAt_centralAmbientFaceReflectId
          hupperFacePhysical hupperFaceSlab]
        exact timeReflectPlaquette_mem_boundaryCompleteSlab hupperFaceSlab
      have hlowerFace : lowerFace ∈
          centralStrictLowerCanonicalRoot radius base root := by
        apply (mem_centralReflectedCanonicalRoot_iff_reflectId_mem
          hupperCanonical hupperSupported
            hlowerFacePhysical hlowerFaceSlab).2
        rw [centralAmbientFaceReflectId_involutive
          hupperFacePhysical hupperFaceSlab]
        exact hupperFace
      have hbit := List.all_eq_true.mp hlowerQuery.1
        lowerFace hlowerFace
      have hpoint := centralReflectedUpperSupportAmbient_memberB_eq_physical
        radius physical hlowerFacePhysical
          (centralStrictLowerCanonicalRoot_side hbase hroot hlowerFace)
      rw [hpoint, centralAmbientFaceReflectId_involutive
        hupperFacePhysical hupperFaceSlab] at hbit
      exact hbit
    · apply List.all_eq_true.mpr
      intro upperFace hupperExterior
      have hupperParts :=
        (mem_canonicalPolymerExteriorFaceQueries_iff
          (centralAmbient radius)
          (centralStrictUpperCanonicalRoot radius base root)
          upperFace).1 hupperExterior
      have hupperFacePhysical := hupperParts.1
      have hupperFaceSlab :=
        centralStrictUpperCanonicalRoot_exterior_mem_slab
          hbase hroot hupperExterior
      let lowerFace := centralAmbientFaceReflectId radius upperFace
      have hlowerFacePhysical : lowerFace ∈
          physicalFaceEdges (centralAmbient radius) :=
        centralAmbientFaceReflectId_physical
          hupperFacePhysical hupperFaceSlab
      have hlowerFaceSlab :
          boxPlaquetteAt (centralAmbient radius) lowerFace ∈
            boundaryCompleteSlabPlaquettes (centralExtent radius) := by
        rw [boxPlaquetteAt_centralAmbientFaceReflectId
          hupperFacePhysical hupperFaceSlab]
        exact timeReflectPlaquette_mem_boundaryCompleteSlab hupperFaceSlab
      have hlowerExterior : lowerFace ∈
          canonicalPolymerExteriorFaceQueries
            (centralAmbient radius)
            (centralStrictLowerCanonicalRoot radius base root) := by
        apply (mem_strictLower_exterior_iff_reflectId_mem_strictUpper_exterior
          hbase hroot hlowerFacePhysical hlowerFaceSlab).2
        rw [centralAmbientFaceReflectId_involutive
          hupperFacePhysical hupperFaceSlab]
        exact hupperExterior
      have hbit := List.all_eq_true.mp hlowerQuery.2
        lowerFace hlowerExterior
      have hpoint := centralReflectedUpperSupportAmbient_memberB_eq_physical
        radius physical hlowerFacePhysical
          (centralStrictLowerCanonicalRoot_exterior_side
            hbase hroot hlowerExterior)
      rw [hpoint, centralAmbientFaceReflectId_involutive
        hupperFacePhysical hupperFaceSlab] at hbit
      exact hbit
  · intro hupperQuery
    constructor
    · apply List.all_eq_true.mpr
      intro lowerFace hlowerFace
      have hlowerFacePhysical := mem_of_mem_sublists
        (physicalFaceEdges (centralAmbient radius))
        (centralStrictLowerCanonicalRoot radius base root)
        (canonicalSurfacePolymer_mem_faceSupports hlowerCanonical)
        lowerFace hlowerFace
      have hlowerFaceSlab := canonicalPolymerSlabSupported_face
        hlowerSupported hlowerFace
      have hupperFace :=
        (mem_centralReflectedCanonicalRoot_iff_reflectId_mem
          hupperCanonical hupperSupported
            hlowerFacePhysical hlowerFaceSlab).1 hlowerFace
      have hbit := List.all_eq_true.mp hupperQuery.1
        (centralAmbientFaceReflectId radius lowerFace) hupperFace
      have hpoint := centralReflectedUpperSupportAmbient_memberB_eq_physical
        radius physical hlowerFacePhysical
          (centralStrictLowerCanonicalRoot_side hbase hroot hlowerFace)
      rw [hpoint]
      exact hbit
    · apply List.all_eq_true.mpr
      intro lowerFace hlowerExterior
      have hlowerParts :=
        (mem_canonicalPolymerExteriorFaceQueries_iff
          (centralAmbient radius)
          (centralStrictLowerCanonicalRoot radius base root)
          lowerFace).1 hlowerExterior
      have hlowerFacePhysical := hlowerParts.1
      have hlowerSide := centralStrictLowerCanonicalRoot_exterior_side
        hbase hroot hlowerExterior
      have hlowerFaceSlab := lowerAmbientFace_mem_centralSlab
        hlowerFacePhysical hlowerSide
      have hupperExterior :=
        (mem_strictLower_exterior_iff_reflectId_mem_strictUpper_exterior
          hbase hroot hlowerFacePhysical hlowerFaceSlab).1 hlowerExterior
      have hbit := List.all_eq_true.mp hupperQuery.2
        (centralAmbientFaceReflectId radius lowerFace) hupperExterior
      have hpoint := centralReflectedUpperSupportAmbient_memberB_eq_physical
        radius physical hlowerFacePhysical hlowerSide
      rw [hpoint]
      exact hbit

def centralStrictUpperCylinderRoots
    (radius base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  roots.map (centralStrictUpperCanonicalRoot radius base)

@[simp] theorem centralStrictUpperCylinderRoots_length
    (radius base : Nat) (roots : List (List Nat)) :
    (centralStrictUpperCylinderRoots radius base roots).length =
      roots.length := by
  simp [centralStrictUpperCylinderRoots]

theorem centralStrictUpperCylinderRoots_canonical
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ centralStrictUpperCylinderRoots radius base roots →
      target ∈ canonicalSurfacePolymers (centralAmbient radius) := by
  intro target htarget
  obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp htarget
  rw [← htargetEq]
  exact centralStrictUpperCanonicalRoot_canonical hbase
    (hroots source hsource)

/-- The complete reflected-upper support coordinate reads the local support
query fingerprint of the unreflected strict upper roots, entry by entry. -/
theorem centralStrictReflectedSupportQueryFingerprint_eq_upperPhysical
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (physical : EdgeLabelling) :
    centralLowerSupportQueryFingerprint radius
        (centralStrictLowerCylinderRoots radius base roots)
        (centralHalfSupportCode radius
          (centralReflectedUpperRestriction radius
            (ambientToSlabPhysical (centralExtent radius) physical))) =
      canonicalRootsSupportQueryFingerprint (centralAmbient radius)
        (centralStrictUpperCylinderRoots radius base roots)
        (excitedPlaquetteIds (centralAmbient radius) physical) := by
  unfold centralLowerSupportQueryFingerprint
    centralStrictLowerCylinderRoots centralStrictUpperCylinderRoots
    canonicalRootsSupportQueryFingerprint
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro root hroot
  exact centralStrictReflectedSupportQueryEventB_eq_upperPhysical
    hbase (hroots root hroot) physical

/-- Symmetric right decoder: the same concrete lower query code used on the
right Gram coordinate is the occurrence fingerprint of the strict upper
roots in the original physical canonical family. -/
theorem centralStrictReflectedUpperSupportQueryFingerprint_eq_familyOccurrence
    {radius base : Nat} (hbase : strictQueryBase base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (physical : EdgeLabelling) :
    centralLowerSupportQueryFingerprint radius
        (centralStrictLowerCylinderRoots radius base roots)
        (centralHalfSupportCode radius
          (centralReflectedUpperRestriction radius
            (ambientToSlabPhysical (centralExtent radius) physical))) =
      familyOccurrenceFingerprint
        (centralStrictUpperCylinderRoots radius base roots)
        (physicalCanonicalAmbientFamily (centralAmbient radius) physical) := by
  calc
    centralLowerSupportQueryFingerprint radius
        (centralStrictLowerCylinderRoots radius base roots)
        (centralHalfSupportCode radius
          (centralReflectedUpperRestriction radius
            (ambientToSlabPhysical (centralExtent radius) physical))) =
        canonicalRootsSupportQueryFingerprint (centralAmbient radius)
          (centralStrictUpperCylinderRoots radius base roots)
          (excitedPlaquetteIds (centralAmbient radius) physical) :=
      centralStrictReflectedSupportQueryFingerprint_eq_upperPhysical
        hbase hroots physical
    _ = canonicalRootsSupportQueryFingerprint (centralAmbient radius)
          (centralStrictUpperCylinderRoots radius base roots)
          (familyUnionSupport (centralAmbient radius)
            (physicalCanonicalAmbientFamily
              (centralAmbient radius) physical)) := by
      rw [physicalCanonicalAmbientFamily_unionSupport]
    _ = familyOccurrenceFingerprint
          (centralStrictUpperCylinderRoots radius base roots)
          (physicalCanonicalAmbientFamily
            (centralAmbient radius) physical) :=
      (familyOccurrenceFingerprint_eq_supportQueryFingerprint
        (centralStrictUpperCylinderRoots_canonical hbase hroots)
        (physicalCanonicalAmbientFamily_mem_compatible
          (centralAmbient radius) physical)).symm

#print axioms centralAmbientFaceReflectId_physical
#print axioms boxPlaquetteAt_centralAmbientFaceReflectId
#print axioms centralAmbientFaceReflectId_involutive
#print axioms centralReflectedUpperSupportAmbient_memberB_eq_physical
#print axioms centralReflectedCanonicalRoot_supported
#print axioms mem_centralReflectedCanonicalRoot_iff_reflectId_mem
#print axioms ambientFace_mem_centralSlab_of_time_lt
#print axioms centralStrictUpperCanonicalRoot_exterior_mem_slab
#print axioms faceLinkAdjacentB_centralAmbientFaceReflectId
#print axioms mem_strictLower_exterior_iff_reflectId_mem_strictUpper_exterior
#print axioms centralStrictReflectedSupportQueryEventB_eq_upperPhysical
#print axioms centralStrictUpperCylinderRoots_canonical
#print axioms centralStrictReflectedSupportQueryFingerprint_eq_upperPhysical
#print axioms centralStrictReflectedUpperSupportQueryFingerprint_eq_familyOccurrence

end YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery
