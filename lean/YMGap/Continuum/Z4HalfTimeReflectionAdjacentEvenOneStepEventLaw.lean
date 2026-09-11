/-
# Exact one-step marked-event reflection in the adjacent-even slab

The strict lower chart and its one-step upper translate fit in the common
adjacent-even ambient box.  This leaf turns their geometric reflection into an
exact equality of complete component-occurrence events.  Both occupied root
faces and the one-link exterior zero shell are transported, so the result is a
genuine canonical-component event law rather than a raw support heuristic.

Everything below is finite and decidable.  No Gram representation, Fubini
disintegration, or classical choice is used.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepQueryGeometry
import YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The source-ordered adjacent-even joint chart -/

def adjacentEvenStrictJointCylinderRoots
    (radius base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  adjacentEvenStrictLowerCylinderRoots radius base roots ++
    adjacentEvenStrictUpperCylinderRoots radius base roots

@[simp] theorem adjacentEvenStrictJointCylinderRoots_length
    (radius base : Nat) (roots : List (List Nat)) :
    (adjacentEvenStrictJointCylinderRoots radius base roots).length =
      roots.length + roots.length := by
  simp [adjacentEvenStrictJointCylinderRoots]

theorem adjacentEvenStrictJointCylinderRoots_canonical
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈
        adjacentEvenStrictJointCylinderRoots radius base roots →
      target ∈ canonicalSurfacePolymers (adjacentEvenAmbient radius) := by
  intro target htarget
  cases List.mem_append.mp htarget with
  | inl hlower =>
      obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hlower
      exact adjacentEvenStrictLowerCanonicalRoot_canonical
        hfit (hroots root hroot)
  | inr hupper =>
      obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hupper
      exact adjacentEvenStrictUpperCanonicalRoot_canonical
        hfit (hroots root hroot)

def adjacentEvenStrictJointPairFamilyEvent
    (radius base : Nat) (roots : List (List Nat))
    (left right : List Bool) : List (List Nat) → Bool :=
  sourceCylinderEvent
    (adjacentEvenStrictJointCylinderRoots radius base roots)
    (centralStrictJointPairPredicate roots.length left right)

/-- The joint event is exactly the ordered lower/upper pair of occurrence
fingerprints.  No length or nonemptiness premise is imposed. -/
theorem adjacentEvenStrictJointPairFamilyEvent_eq
    (radius base : Nat) (roots : List (List Nat))
    (left right : List Bool) (family : List (List Nat)) :
    adjacentEvenStrictJointPairFamilyEvent
        radius base roots left right family =
      decide
        (familyOccurrenceFingerprint
              (adjacentEvenStrictLowerCylinderRoots radius base roots) family =
            left ∧
          familyOccurrenceFingerprint
              (adjacentEvenStrictUpperCylinderRoots radius base roots) family =
            right) := by
  unfold adjacentEvenStrictJointPairFamilyEvent sourceCylinderEvent
    cylinderEvent centralStrictJointPairPredicate
    adjacentEvenStrictJointCylinderRoots
  rw [familyOccurrenceFingerprint_append]
  have hlength :
      (familyOccurrenceFingerprint
        (adjacentEvenStrictLowerCylinderRoots radius base roots)
        family).length = roots.length := by
    rw [familyOccurrenceFingerprint_length,
      adjacentEvenStrictLowerCylinderRoots_length]
  rw [← hlength, List.take_append_length, List.drop_append_length]

/-! ## 2. Canonical marked atoms -/

def adjacentEvenStrictJointCanonicalAtoms
    (radius base : Nat) (roots : List (List Nat))
    (hfit : strictQueryBase (base + 1) ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    List (CanonicalAtom (adjacentEvenAmbient radius)) :=
  familyCanonicalAtoms (adjacentEvenAmbient radius)
    (adjacentEvenStrictJointCylinderRoots radius base roots)
    (adjacentEvenStrictJointCylinderRoots_canonical hfit hroots)

theorem adjacentEvenStrictJointCanonicalAtoms_values
    (radius base : Nat) (roots : List (List Nat))
    (hfit : strictQueryBase (base + 1) ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (adjacentEvenStrictJointCanonicalAtoms
      radius base roots hfit hroots).map Subtype.val =
        adjacentEvenStrictJointCylinderRoots radius base roots := by
  unfold adjacentEvenStrictJointCanonicalAtoms
  exact familyCanonicalAtoms_values (adjacentEvenAmbient radius)
    (adjacentEvenStrictJointCylinderRoots radius base roots) _

@[simp] theorem adjacentEvenStrictJointCanonicalAtoms_length
    (radius base : Nat) (roots : List (List Nat))
    (hfit : strictQueryBase (base + 1) ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (adjacentEvenStrictJointCanonicalAtoms
      radius base roots hfit hroots).length =
        roots.length + roots.length := by
  have hvalues := congrArg List.length
    (adjacentEvenStrictJointCanonicalAtoms_values
      radius base roots hfit hroots)
  simpa only [List.length_map,
    adjacentEvenStrictJointCylinderRoots_length] using hvalues

theorem adjacentEvenStrictJointCanonicalAtoms_supported
    (radius base : Nat) (roots : List (List Nat))
    (hfit : strictQueryBase (base + 1) ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ atom, atom ∈ adjacentEvenStrictJointCanonicalAtoms
        radius base roots hfit hroots →
      canonicalPolymerSlabSupportedB (adjacentEvenExtent radius)
        atom.val = true := by
  intro atom hatom
  have hvalue : atom.val ∈
      (adjacentEvenStrictJointCanonicalAtoms
        radius base roots hfit hroots).map Subtype.val :=
    List.mem_map.mpr ⟨atom, hatom, rfl⟩
  rw [adjacentEvenStrictJointCanonicalAtoms_values] at hvalue
  cases List.mem_append.mp hvalue with
  | inl hlower =>
      obtain ⟨root, hroot, hvalueEq⟩ := List.mem_map.mp hlower
      rw [← hvalueEq]
      exact adjacentEvenStrictLowerCanonicalRoot_supported
        hfit (hroots root hroot)
  | inr hupper =>
      obtain ⟨root, hroot, hvalueEq⟩ := List.mem_map.mp hupper
      rw [← hvalueEq]
      exact adjacentEvenStrictUpperCanonicalRoot_supported
        hfit (hroots root hroot)

theorem adjacentEvenStrictJointMarkedCylinderEvent_eq
    (radius base : Nat) (roots : List (List Nat))
    (hfit : strictQueryBase (base + 1) ≤ radius)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    slabMarkedCylinderEvent
        (adjacentEvenStrictJointCanonicalAtoms
          radius base roots hfit hroots)
        (centralStrictJointPairPredicate roots.length left right) =
      adjacentEvenStrictJointPairFamilyEvent
        radius base roots left right := by
  funext family
  unfold slabMarkedCylinderEvent
    adjacentEvenStrictJointPairFamilyEvent sourceCylinderEvent
  exact congrArg
    (fun markedRoots => cylinderEvent markedRoots
      (centralStrictJointPairPredicate roots.length left right) family)
    (adjacentEvenStrictJointCanonicalAtoms_values
      radius base roots hfit hroots)

/-! ## 3. Zero extension intertwines physical reflection -/

private theorem slabPlaquetteAt_eq_of_enumerate_local
    {extent id : Nat} {plaquette : Z4Plaq}
    (hindexed : (id, plaquette) ∈
      enumerate (boundaryCompleteSlabPlaquettes extent)) :
    slabPlaquetteAt extent id = plaquette := by
  unfold slabPlaquetteAt
  exact enumerate_getD_of_mem fallbackPlaquette hindexed

/-- The occupied ambient support of a zero-extended slab labelling. -/
def adjacentEvenSlabAmbientSupport
    (radius : Nat) (physical : EdgeLabelling) : List Nat :=
  excitedPlaquetteIds (adjacentEvenAmbient radius)
    (slabToAmbientPhysical (adjacentEvenExtent radius) physical)

/-- On every physical ambient face belonging to the adjacent-even slab,
zero extension intertwines slab-coordinate reflection with the independently
defined ambient face reflection identifier. -/
theorem slabToAmbientPhysical_adjacentEven_reflection
    (radius : Nat) (physical : EdgeLabelling) {face : Nat}
    (hphysical :
      face ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hslab :
      boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
        boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius)) :
    slabToAmbientPhysical (adjacentEvenExtent radius)
        (reflectSupportedSlabFaceLabelling
          (adjacentEvenExtent radius) physical) face =
      slabToAmbientPhysical (adjacentEvenExtent radius) physical
        (adjacentEvenAmbientFaceReflectId radius face) := by
  obtain ⟨sourceId, hsourceIndexed⟩ := exists_mem_enumerate hslab
  have hsourcePhysical : sourceId ∈
      slabPhysicalFaceEdges (adjacentEvenExtent radius) := by
    unfold slabPhysicalFaceEdges
    exact List.mem_range.mpr (enumerate_index_lt hsourceIndexed)
  have hsourceAt :
      slabPlaquetteAt (adjacentEvenExtent radius) sourceId =
        boxPlaquetteAt (adjacentEvenAmbient radius) face :=
    slabPlaquetteAt_eq_of_enumerate_local hsourceIndexed
  have hfaceIndexed :
      (face, boxPlaquetteAt (adjacentEvenAmbient radius) face) ∈
        enumerate (boxPlaquettes (adjacentEvenAmbient radius)) :=
    boxPlaquetteAt_mem_enumerate (physicalFaceId_lt hphysical)
  have hreflectedPhysical :=
    adjacentEvenAmbientFaceReflectId_physical hphysical hslab
  have hreflectedIndexed :
      (adjacentEvenAmbientFaceReflectId radius face,
        boxPlaquetteAt (adjacentEvenAmbient radius)
          (adjacentEvenAmbientFaceReflectId radius face)) ∈
        enumerate (boxPlaquettes (adjacentEvenAmbient radius)) :=
    boxPlaquetteAt_mem_enumerate
      (physicalFaceId_lt hreflectedPhysical)
  have hreflectedSourcePhysical :=
    slabFaceReflectId_physical hsourcePhysical
  have hreflectedSourceIndexed :=
    slabPlaquetteAt_mem_enumerate hreflectedSourcePhysical
  have hreflectedAt :
      boxPlaquetteAt (adjacentEvenAmbient radius)
          (adjacentEvenAmbientFaceReflectId radius face) =
        slabPlaquetteAt (adjacentEvenExtent radius)
          (slabFaceReflectId (adjacentEvenExtent radius) sourceId) := by
    rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
        hphysical hslab,
      slabPlaquetteAt_slabFaceReflectId hsourcePhysical,
      hsourceAt]
  rw [slabToAmbientPhysical_eq_on_enumerate hfaceIndexed,
    slabGeometricSpin_eq_of_enumerate hsourceIndexed,
    reflectSupportedSlabFaceLabelling_eq_on_physical
      (adjacentEvenExtent radius) physical hsourcePhysical]
  unfold reflectSlabFaceLabelling
  rw [slabToAmbientPhysical_eq_on_enumerate hreflectedIndexed,
    hreflectedAt,
    slabGeometricSpin_eq_of_enumerate hreflectedSourceIndexed]

/-- Boolean membership in the complete occupied support is transported by the
same ambient reflection identifier. -/
theorem memberB_adjacentEvenSlabAmbientSupport_reflection
    (radius : Nat) (physical : EdgeLabelling) {face : Nat}
    (hphysical :
      face ∈ physicalFaceEdges (adjacentEvenAmbient radius))
    (hslab :
      boxPlaquetteAt (adjacentEvenAmbient radius) face ∈
        boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius)) :
    memberB
        (adjacentEvenSlabAmbientSupport radius
          (reflectSupportedSlabFaceLabelling
            (adjacentEvenExtent radius) physical)) face =
      memberB (adjacentEvenSlabAmbientSupport radius physical)
        (adjacentEvenAmbientFaceReflectId radius face) := by
  have hreflectedPhysical :=
    adjacentEvenAmbientFaceReflectId_physical hphysical hslab
  apply Bool.eq_iff_iff.mpr
  simp only [memberB_eq_true_iff, adjacentEvenSlabAmbientSupport,
    excitedPlaquetteIds, List.mem_filter, decide_eq_true_eq,
    hphysical, hreflectedPhysical, true_and]
  rw [slabToAmbientPhysical_adjacentEven_reflection
    radius physical hphysical hslab]

/-! ## 4. Complete component-query exchange -/

theorem adjacentEvenStrictLowerCylinderRoots_canonical
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target,
      target ∈ adjacentEvenStrictLowerCylinderRoots radius base roots →
      target ∈ canonicalSurfacePolymers
        (adjacentEvenAmbient radius) := by
  intro target htarget
  obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp htarget
  rw [← htargetEq]
  exact adjacentEvenStrictLowerCanonicalRoot_canonical
    hfit (hroots source hsource)

theorem adjacentEvenStrictUpperCylinderRoots_canonical
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target,
      target ∈ adjacentEvenStrictUpperCylinderRoots radius base roots →
      target ∈ canonicalSurfacePolymers
        (adjacentEvenAmbient radius) := by
  intro target htarget
  obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp htarget
  rw [← htargetEq]
  exact adjacentEvenStrictUpperCanonicalRoot_canonical
    hfit (hroots source hsource)

/-- Reflecting the slab labelling exchanges a complete lower component query
with the corresponding upper query, including the exterior zero shell. -/
theorem adjacentEvenStrictLowerSupportQueryEventB_reflection
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    (physical : EdgeLabelling) :
    canonicalPolymerSupportQueryEventB
        (adjacentEvenAmbient radius)
        (adjacentEvenStrictLowerCanonicalRoot radius base root)
        (adjacentEvenSlabAmbientSupport radius
          (reflectSupportedSlabFaceLabelling
            (adjacentEvenExtent radius) physical)) =
      canonicalPolymerSupportQueryEventB
        (adjacentEvenAmbient radius)
        (adjacentEvenStrictUpperCanonicalRoot radius base root)
        (adjacentEvenSlabAmbientSupport radius physical) := by
  have hlowerCanonical :=
    adjacentEvenStrictLowerCanonicalRoot_canonical hfit hroot
  have hupperCanonical :=
    adjacentEvenStrictUpperCanonicalRoot_canonical hfit hroot
  unfold canonicalPolymerSupportQueryEventB
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · intro hlowerQuery
    constructor
    · apply List.all_eq_true.mpr
      intro upperFace hupperFace
      have hupperPhysical := mem_of_mem_sublists
        (physicalFaceEdges (adjacentEvenAmbient radius))
        (adjacentEvenStrictUpperCanonicalRoot radius base root)
        (canonicalSurfacePolymer_mem_faceSupports hupperCanonical)
        upperFace hupperFace
      have hupperSlab :=
        adjacentEvenStrictUpperCanonicalRoot_face_mem_slab
          hfit hroot hupperFace
      let lowerFace :=
        adjacentEvenAmbientFaceReflectId radius upperFace
      have hlowerPhysical :=
        adjacentEvenAmbientFaceReflectId_physical
          hupperPhysical hupperSlab
      have hlowerSlab :
          boxPlaquetteAt (adjacentEvenAmbient radius) lowerFace ∈
            boundaryCompleteSlabPlaquettes
              (adjacentEvenExtent radius) := by
        rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
          hupperPhysical hupperSlab]
        exact timeReflectPlaquette_mem_boundaryCompleteSlab hupperSlab
      have hlowerFace : lowerFace ∈
          adjacentEvenStrictLowerCanonicalRoot radius base root := by
        apply (mem_adjacentEvenStrictLower_iff_reflectId_mem_upper
          hfit hroot hlowerPhysical hlowerSlab).2
        rw [adjacentEvenAmbientFaceReflectId_involutive
          hupperPhysical hupperSlab]
        exact hupperFace
      have hbit := List.all_eq_true.mp hlowerQuery.1
        lowerFace hlowerFace
      have hpoint :=
        memberB_adjacentEvenSlabAmbientSupport_reflection
          radius physical hlowerPhysical hlowerSlab
      rw [hpoint,
        adjacentEvenAmbientFaceReflectId_involutive
          hupperPhysical hupperSlab] at hbit
      exact hbit
    · apply List.all_eq_true.mpr
      intro upperFace hupperExterior
      have hupperPhysical :=
        (mem_canonicalPolymerExteriorFaceQueries_iff
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictUpperCanonicalRoot radius base root)
          upperFace).1 hupperExterior |>.1
      have hupperSlab :=
        adjacentEvenStrictUpperCanonicalRoot_exterior_mem_slab
          hfit hroot hupperExterior
      let lowerFace :=
        adjacentEvenAmbientFaceReflectId radius upperFace
      have hlowerPhysical :=
        adjacentEvenAmbientFaceReflectId_physical
          hupperPhysical hupperSlab
      have hlowerSlab :
          boxPlaquetteAt (adjacentEvenAmbient radius) lowerFace ∈
            boundaryCompleteSlabPlaquettes
              (adjacentEvenExtent radius) := by
        rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
          hupperPhysical hupperSlab]
        exact timeReflectPlaquette_mem_boundaryCompleteSlab hupperSlab
      have hlowerExterior : lowerFace ∈
          canonicalPolymerExteriorFaceQueries
            (adjacentEvenAmbient radius)
            (adjacentEvenStrictLowerCanonicalRoot radius base root) := by
        apply
          (mem_adjacentEvenStrictLower_exterior_iff_reflectId_mem_upper_exterior
            hfit hroot hlowerPhysical hlowerSlab).2
        rw [adjacentEvenAmbientFaceReflectId_involutive
          hupperPhysical hupperSlab]
        exact hupperExterior
      have hbit := List.all_eq_true.mp hlowerQuery.2
        lowerFace hlowerExterior
      have hpoint :=
        memberB_adjacentEvenSlabAmbientSupport_reflection
          radius physical hlowerPhysical hlowerSlab
      rw [hpoint,
        adjacentEvenAmbientFaceReflectId_involutive
          hupperPhysical hupperSlab] at hbit
      exact hbit
  · intro hupperQuery
    constructor
    · apply List.all_eq_true.mpr
      intro lowerFace hlowerFace
      have hlowerPhysical := mem_of_mem_sublists
        (physicalFaceEdges (adjacentEvenAmbient radius))
        (adjacentEvenStrictLowerCanonicalRoot radius base root)
        (canonicalSurfacePolymer_mem_faceSupports hlowerCanonical)
        lowerFace hlowerFace
      have hlowerSlab :=
        adjacentEvenStrictLowerCanonicalRoot_face_mem_slab
          hfit hroot hlowerFace
      have hupperFace :=
        (mem_adjacentEvenStrictLower_iff_reflectId_mem_upper
          hfit hroot hlowerPhysical hlowerSlab).1 hlowerFace
      have hbit := List.all_eq_true.mp hupperQuery.1
        (adjacentEvenAmbientFaceReflectId radius lowerFace)
        hupperFace
      rw [memberB_adjacentEvenSlabAmbientSupport_reflection
        radius physical hlowerPhysical hlowerSlab]
      exact hbit
    · apply List.all_eq_true.mpr
      intro lowerFace hlowerExterior
      have hlowerPhysical :=
        (mem_canonicalPolymerExteriorFaceQueries_iff
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictLowerCanonicalRoot radius base root)
          lowerFace).1 hlowerExterior |>.1
      have hlowerSlab :=
        adjacentEvenStrictLowerCanonicalRoot_exterior_mem_slab
          hfit hroot hlowerExterior
      have hupperExterior :=
        (mem_adjacentEvenStrictLower_exterior_iff_reflectId_mem_upper_exterior
          hfit hroot hlowerPhysical hlowerSlab).1 hlowerExterior
      have hbit := List.all_eq_true.mp hupperQuery.2
        (adjacentEvenAmbientFaceReflectId radius lowerFace)
        hupperExterior
      rw [memberB_adjacentEvenSlabAmbientSupport_reflection
        radius physical hlowerPhysical hlowerSlab]
      exact hbit

/-- The reverse component query is transported independently.  This avoids
deriving the result from an involutivity statement for a whole labelling,
which would require an unnecessary global slab-support hypothesis. -/
theorem adjacentEvenStrictUpperSupportQueryEventB_reflection
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    (physical : EdgeLabelling) :
    canonicalPolymerSupportQueryEventB
        (adjacentEvenAmbient radius)
        (adjacentEvenStrictUpperCanonicalRoot radius base root)
        (adjacentEvenSlabAmbientSupport radius
          (reflectSupportedSlabFaceLabelling
            (adjacentEvenExtent radius) physical)) =
      canonicalPolymerSupportQueryEventB
        (adjacentEvenAmbient radius)
        (adjacentEvenStrictLowerCanonicalRoot radius base root)
        (adjacentEvenSlabAmbientSupport radius physical) := by
  have hlowerCanonical :=
    adjacentEvenStrictLowerCanonicalRoot_canonical hfit hroot
  have hupperCanonical :=
    adjacentEvenStrictUpperCanonicalRoot_canonical hfit hroot
  unfold canonicalPolymerSupportQueryEventB
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · intro hupperQuery
    constructor
    · apply List.all_eq_true.mpr
      intro lowerFace hlowerFace
      have hlowerPhysical := mem_of_mem_sublists
        (physicalFaceEdges (adjacentEvenAmbient radius))
        (adjacentEvenStrictLowerCanonicalRoot radius base root)
        (canonicalSurfacePolymer_mem_faceSupports hlowerCanonical)
        lowerFace hlowerFace
      have hlowerSlab :=
        adjacentEvenStrictLowerCanonicalRoot_face_mem_slab
          hfit hroot hlowerFace
      let upperFace :=
        adjacentEvenAmbientFaceReflectId radius lowerFace
      have hupperPhysical :=
        adjacentEvenAmbientFaceReflectId_physical
          hlowerPhysical hlowerSlab
      have hupperSlab :
          boxPlaquetteAt (adjacentEvenAmbient radius) upperFace ∈
            boundaryCompleteSlabPlaquettes
              (adjacentEvenExtent radius) := by
        rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
          hlowerPhysical hlowerSlab]
        exact timeReflectPlaquette_mem_boundaryCompleteSlab hlowerSlab
      have hupperFace : upperFace ∈
          adjacentEvenStrictUpperCanonicalRoot radius base root :=
        (mem_adjacentEvenStrictLower_iff_reflectId_mem_upper
          hfit hroot hlowerPhysical hlowerSlab).1 hlowerFace
      have hbit := List.all_eq_true.mp hupperQuery.1
        upperFace hupperFace
      have hpoint :=
        memberB_adjacentEvenSlabAmbientSupport_reflection
          radius physical hupperPhysical hupperSlab
      rw [hpoint,
        adjacentEvenAmbientFaceReflectId_involutive
          hlowerPhysical hlowerSlab] at hbit
      exact hbit
    · apply List.all_eq_true.mpr
      intro lowerFace hlowerExterior
      have hlowerPhysical :=
        (mem_canonicalPolymerExteriorFaceQueries_iff
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictLowerCanonicalRoot radius base root)
          lowerFace).1 hlowerExterior |>.1
      have hlowerSlab :=
        adjacentEvenStrictLowerCanonicalRoot_exterior_mem_slab
          hfit hroot hlowerExterior
      let upperFace :=
        adjacentEvenAmbientFaceReflectId radius lowerFace
      have hupperPhysical :=
        adjacentEvenAmbientFaceReflectId_physical
          hlowerPhysical hlowerSlab
      have hupperSlab :
          boxPlaquetteAt (adjacentEvenAmbient radius) upperFace ∈
            boundaryCompleteSlabPlaquettes
              (adjacentEvenExtent radius) := by
        rw [boxPlaquetteAt_adjacentEvenAmbientFaceReflectId
          hlowerPhysical hlowerSlab]
        exact timeReflectPlaquette_mem_boundaryCompleteSlab hlowerSlab
      have hupperExterior : upperFace ∈
          canonicalPolymerExteriorFaceQueries
            (adjacentEvenAmbient radius)
            (adjacentEvenStrictUpperCanonicalRoot radius base root) :=
        (mem_adjacentEvenStrictLower_exterior_iff_reflectId_mem_upper_exterior
          hfit hroot hlowerPhysical hlowerSlab).1 hlowerExterior
      have hbit := List.all_eq_true.mp hupperQuery.2
        upperFace hupperExterior
      have hpoint :=
        memberB_adjacentEvenSlabAmbientSupport_reflection
          radius physical hupperPhysical hupperSlab
      rw [hpoint,
        adjacentEvenAmbientFaceReflectId_involutive
          hlowerPhysical hlowerSlab] at hbit
      exact hbit
  · intro hlowerQuery
    constructor
    · apply List.all_eq_true.mpr
      intro upperFace hupperFace
      have hupperPhysical := mem_of_mem_sublists
        (physicalFaceEdges (adjacentEvenAmbient radius))
        (adjacentEvenStrictUpperCanonicalRoot radius base root)
        (canonicalSurfacePolymer_mem_faceSupports hupperCanonical)
        upperFace hupperFace
      have hupperSlab :=
        adjacentEvenStrictUpperCanonicalRoot_face_mem_slab
          hfit hroot hupperFace
      let lowerFace :=
        adjacentEvenAmbientFaceReflectId radius upperFace
      have hlowerFace : lowerFace ∈
          adjacentEvenStrictLowerCanonicalRoot radius base root :=
        (reflectId_mem_lower_iff_mem_adjacentEvenStrictUpper
          hfit hroot hupperPhysical hupperSlab).2 hupperFace
      have hbit := List.all_eq_true.mp hlowerQuery.1
        lowerFace hlowerFace
      rw [memberB_adjacentEvenSlabAmbientSupport_reflection
        radius physical hupperPhysical hupperSlab]
      exact hbit
    · apply List.all_eq_true.mpr
      intro upperFace hupperExterior
      have hupperPhysical :=
        (mem_canonicalPolymerExteriorFaceQueries_iff
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictUpperCanonicalRoot radius base root)
          upperFace).1 hupperExterior |>.1
      have hupperSlab :=
        adjacentEvenStrictUpperCanonicalRoot_exterior_mem_slab
          hfit hroot hupperExterior
      let lowerFace :=
        adjacentEvenAmbientFaceReflectId radius upperFace
      have hlowerExterior : lowerFace ∈
          canonicalPolymerExteriorFaceQueries
            (adjacentEvenAmbient radius)
            (adjacentEvenStrictLowerCanonicalRoot radius base root) :=
        (reflectId_mem_lower_exterior_iff_mem_upper_exterior
          hfit hroot hupperPhysical hupperSlab).2 hupperExterior
      have hbit := List.all_eq_true.mp hlowerQuery.2
        lowerFace hlowerExterior
      rw [memberB_adjacentEvenSlabAmbientSupport_reflection
        radius physical hupperPhysical hupperSlab]
      exact hbit

/-! ## 5. Ordered support-query fingerprints -/

/-- Reflection sends the lower query fingerprint to the upper fingerprint,
with the original source order and every duplicate retained literally. -/
theorem adjacentEvenStrictLowerSupportQueryFingerprint_reflection
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (physical : EdgeLabelling) :
    canonicalRootsSupportQueryFingerprint
        (adjacentEvenAmbient radius)
        (adjacentEvenStrictLowerCylinderRoots radius base roots)
        (adjacentEvenSlabAmbientSupport radius
          (reflectSupportedSlabFaceLabelling
            (adjacentEvenExtent radius) physical)) =
      canonicalRootsSupportQueryFingerprint
        (adjacentEvenAmbient radius)
        (adjacentEvenStrictUpperCylinderRoots radius base roots)
        (adjacentEvenSlabAmbientSupport radius physical) := by
  unfold canonicalRootsSupportQueryFingerprint
    adjacentEvenStrictLowerCylinderRoots
    adjacentEvenStrictUpperCylinderRoots
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro root hroot
  exact adjacentEvenStrictLowerSupportQueryEventB_reflection
    hfit (hroots root hroot) physical

/-- The reverse ordered fingerprint exchange, proved from the reverse local
query theorem rather than from a global reflected-labelling assumption. -/
theorem adjacentEvenStrictUpperSupportQueryFingerprint_reflection
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (physical : EdgeLabelling) :
    canonicalRootsSupportQueryFingerprint
        (adjacentEvenAmbient radius)
        (adjacentEvenStrictUpperCylinderRoots radius base roots)
        (adjacentEvenSlabAmbientSupport radius
          (reflectSupportedSlabFaceLabelling
            (adjacentEvenExtent radius) physical)) =
      canonicalRootsSupportQueryFingerprint
        (adjacentEvenAmbient radius)
        (adjacentEvenStrictLowerCylinderRoots radius base roots)
        (adjacentEvenSlabAmbientSupport radius physical) := by
  unfold canonicalRootsSupportQueryFingerprint
    adjacentEvenStrictLowerCylinderRoots
    adjacentEvenStrictUpperCylinderRoots
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro root hroot
  exact adjacentEvenStrictUpperSupportQueryEventB_reflection
    hfit (hroots root hroot) physical

/-! ## 6. Exact component-occurrence fingerprints -/

/-- The lower occurrence fingerprint of the reflected physical family is the
upper occurrence fingerprint of the original family.  The conversion through
support queries is exact because the canonical physical family has union
support equal to the complete excited support. -/
theorem adjacentEvenStrictLowerOccurrenceFingerprint_reflection
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (physical : EdgeLabelling) :
    familyOccurrenceFingerprint
        (adjacentEvenStrictLowerCylinderRoots radius base roots)
        (physicalCanonicalAmbientFamily
          (adjacentEvenAmbient radius)
          (slabToAmbientPhysical (adjacentEvenExtent radius)
            (reflectSupportedSlabFaceLabelling
              (adjacentEvenExtent radius) physical))) =
      familyOccurrenceFingerprint
        (adjacentEvenStrictUpperCylinderRoots radius base roots)
        (physicalCanonicalAmbientFamily
          (adjacentEvenAmbient radius)
          (slabToAmbientPhysical
            (adjacentEvenExtent radius) physical)) := by
  calc
    _ = canonicalRootsSupportQueryFingerprint
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictLowerCylinderRoots radius base roots)
          (familyUnionSupport
            (adjacentEvenAmbient radius)
            (physicalCanonicalAmbientFamily
              (adjacentEvenAmbient radius)
              (slabToAmbientPhysical (adjacentEvenExtent radius)
                (reflectSupportedSlabFaceLabelling
                  (adjacentEvenExtent radius) physical)))) :=
      familyOccurrenceFingerprint_eq_supportQueryFingerprint
        (adjacentEvenStrictLowerCylinderRoots_canonical hfit hroots)
        (physicalCanonicalAmbientFamily_mem_compatible
          (adjacentEvenAmbient radius)
          (slabToAmbientPhysical (adjacentEvenExtent radius)
            (reflectSupportedSlabFaceLabelling
              (adjacentEvenExtent radius) physical)))
    _ = canonicalRootsSupportQueryFingerprint
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictLowerCylinderRoots radius base roots)
          (adjacentEvenSlabAmbientSupport radius
            (reflectSupportedSlabFaceLabelling
              (adjacentEvenExtent radius) physical)) := by
      rw [physicalCanonicalAmbientFamily_unionSupport]
      rfl
    _ = canonicalRootsSupportQueryFingerprint
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictUpperCylinderRoots radius base roots)
          (adjacentEvenSlabAmbientSupport radius physical) :=
      adjacentEvenStrictLowerSupportQueryFingerprint_reflection
        hfit hroots physical
    _ = canonicalRootsSupportQueryFingerprint
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictUpperCylinderRoots radius base roots)
          (familyUnionSupport
            (adjacentEvenAmbient radius)
            (physicalCanonicalAmbientFamily
              (adjacentEvenAmbient radius)
              (slabToAmbientPhysical
                (adjacentEvenExtent radius) physical))) := by
      rw [physicalCanonicalAmbientFamily_unionSupport]
      rfl
    _ = _ :=
      (familyOccurrenceFingerprint_eq_supportQueryFingerprint
        (adjacentEvenStrictUpperCylinderRoots_canonical hfit hroots)
        (physicalCanonicalAmbientFamily_mem_compatible
          (adjacentEvenAmbient radius)
          (slabToAmbientPhysical
            (adjacentEvenExtent radius) physical))).symm

/-- The complementary exact occurrence-fingerprint exchange. -/
theorem adjacentEvenStrictUpperOccurrenceFingerprint_reflection
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (physical : EdgeLabelling) :
    familyOccurrenceFingerprint
        (adjacentEvenStrictUpperCylinderRoots radius base roots)
        (physicalCanonicalAmbientFamily
          (adjacentEvenAmbient radius)
          (slabToAmbientPhysical (adjacentEvenExtent radius)
            (reflectSupportedSlabFaceLabelling
              (adjacentEvenExtent radius) physical))) =
      familyOccurrenceFingerprint
        (adjacentEvenStrictLowerCylinderRoots radius base roots)
        (physicalCanonicalAmbientFamily
          (adjacentEvenAmbient radius)
          (slabToAmbientPhysical
            (adjacentEvenExtent radius) physical)) := by
  calc
    _ = canonicalRootsSupportQueryFingerprint
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictUpperCylinderRoots radius base roots)
          (familyUnionSupport
            (adjacentEvenAmbient radius)
            (physicalCanonicalAmbientFamily
              (adjacentEvenAmbient radius)
              (slabToAmbientPhysical (adjacentEvenExtent radius)
                (reflectSupportedSlabFaceLabelling
                  (adjacentEvenExtent radius) physical)))) :=
      familyOccurrenceFingerprint_eq_supportQueryFingerprint
        (adjacentEvenStrictUpperCylinderRoots_canonical hfit hroots)
        (physicalCanonicalAmbientFamily_mem_compatible
          (adjacentEvenAmbient radius)
          (slabToAmbientPhysical (adjacentEvenExtent radius)
            (reflectSupportedSlabFaceLabelling
              (adjacentEvenExtent radius) physical)))
    _ = canonicalRootsSupportQueryFingerprint
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictUpperCylinderRoots radius base roots)
          (adjacentEvenSlabAmbientSupport radius
            (reflectSupportedSlabFaceLabelling
              (adjacentEvenExtent radius) physical)) := by
      rw [physicalCanonicalAmbientFamily_unionSupport]
      rfl
    _ = canonicalRootsSupportQueryFingerprint
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictLowerCylinderRoots radius base roots)
          (adjacentEvenSlabAmbientSupport radius physical) :=
      adjacentEvenStrictUpperSupportQueryFingerprint_reflection
        hfit hroots physical
    _ = canonicalRootsSupportQueryFingerprint
          (adjacentEvenAmbient radius)
          (adjacentEvenStrictLowerCylinderRoots radius base roots)
          (familyUnionSupport
            (adjacentEvenAmbient radius)
            (physicalCanonicalAmbientFamily
              (adjacentEvenAmbient radius)
              (slabToAmbientPhysical
                (adjacentEvenExtent radius) physical))) := by
      rw [physicalCanonicalAmbientFamily_unionSupport]
      rfl
    _ = _ :=
      (familyOccurrenceFingerprint_eq_supportQueryFingerprint
        (adjacentEvenStrictLowerCylinderRoots_canonical hfit hroots)
        (physicalCanonicalAmbientFamily_mem_compatible
          (adjacentEvenAmbient radius)
          (slabToAmbientPhysical
            (adjacentEvenExtent radius) physical))).symm

/-! ## 7. The reflected marked slab event -/

/-- The literal slab event obtained by zero-extending a physical labelling,
extracting its canonical ambient component family, and asking for the ordered
lower/upper occurrence pair. -/
def adjacentEvenStrictJointPairSlabEvent
    (radius base : Nat) (roots : List (List Nat))
    (left right : List Bool) : EdgeLabelling → Bool :=
  fun physical =>
    cutoffOneLiftedFamilyEvent (adjacentEvenAmbient radius)
      (adjacentEvenStrictJointPairFamilyEvent
        radius base roots left right)
      (slabToAmbientPhysical (adjacentEvenExtent radius) physical)

/-- Physical reflection swaps the lower and upper marked fingerprints
exactly, as functions on all slab-coordinate labellings. -/
theorem reflectSlabEvent_adjacentEvenStrictJointPair
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    reflectSlabEvent (adjacentEvenExtent radius)
        (adjacentEvenStrictJointPairSlabEvent
          radius base roots left right) =
      adjacentEvenStrictJointPairSlabEvent
        radius base roots right left := by
  funext physical
  unfold reflectSlabEvent adjacentEvenStrictJointPairSlabEvent
    cutoffOneLiftedFamilyEvent
  rw [adjacentEvenStrictJointPairFamilyEvent_eq,
    adjacentEvenStrictJointPairFamilyEvent_eq,
    adjacentEvenStrictLowerOccurrenceFingerprint_reflection
      hfit hroots physical,
    adjacentEvenStrictUpperOccurrenceFingerprint_reflection
      hfit hroots physical]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact and_comm

/-! ## 8. Exact finite-cutoff event laws -/

/-- The two ordered marked events have the same unnormalized slab weight at
every rational coupling and every finite character cutoff. -/
theorem slabEventNumerator_adjacentEvenStrictJointPair_eqv
    (coupling : Q') (cutoff : Nat)
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    slabEventNumerator coupling cutoff (adjacentEvenExtent radius)
        (adjacentEvenStrictJointPairSlabEvent
          radius base roots left right) ≈
      slabEventNumerator coupling cutoff (adjacentEvenExtent radius)
        (adjacentEvenStrictJointPairSlabEvent
          radius base roots right left) := by
  have hreflection := slabEventNumerator_reflection
    coupling cutoff (adjacentEvenExtent radius)
      (adjacentEvenStrictJointPairSlabEvent
        radius base roots left right)
  rw [reflectSlabEvent_adjacentEvenStrictJointPair
    hfit hroots left right] at hreflection
  exact Q'.eqv_symm hreflection

/-- The positive normalized slab law of the ordered adjacent-even marked
pair.  The denominator is the full corrected-slab partition. -/
def adjacentEvenStrictJointPairSlabProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius base : Nat) (roots : List (List Nat))
    (left right : List Bool) : Q' :=
  Q'.divPos
    (slabEventNumerator coupling cutoff (adjacentEvenExtent radius)
      (adjacentEvenStrictJointPairSlabEvent
        radius base roots left right))
    (slabParametricKPhysicalPartition
      coupling cutoff (adjacentEvenExtent radius))
    (slabParametricKPhysicalPartition_pos
      hcoupling cutoff (adjacentEvenExtent radius))

/-- After normalization by the positive full-slab partition, reflection still
exchanges the ordered marked pair exactly. -/
theorem adjacentEvenStrictJointPairSlabProbability_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat)
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    adjacentEvenStrictJointPairSlabProbability
        coupling hcoupling cutoff radius base roots left right ≈
      adjacentEvenStrictJointPairSlabProbability
        coupling hcoupling cutoff radius base roots right left := by
  unfold adjacentEvenStrictJointPairSlabProbability
  exact divPos_eqv_congr
    (slabParametricKPhysicalPartition_pos
      hcoupling cutoff (adjacentEvenExtent radius))
    (slabParametricKPhysicalPartition_pos
      hcoupling cutoff (adjacentEvenExtent radius))
    (slabEventNumerator_adjacentEvenStrictJointPair_eqv
      coupling cutoff hfit hroots left right)
    (Q'.eqv_refl _)

/-- The same event equality in the ambient presentation, with the exact
zero-extension support mask made explicit. -/
theorem parametricKEventNumerator_adjacentEvenStrictJointPair_masked_eqv
    (coupling : Q') (cutoff : Nat)
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    parametricKEventNumerator coupling cutoff
        (adjacentEvenAmbient radius)
        (fun physical =>
          ambientSlabSupportedB (adjacentEvenExtent radius) physical &&
            cutoffOneLiftedFamilyEvent (adjacentEvenAmbient radius)
              (adjacentEvenStrictJointPairFamilyEvent
                radius base roots left right) physical) ≈
      parametricKEventNumerator coupling cutoff
        (adjacentEvenAmbient radius)
        (fun physical =>
          ambientSlabSupportedB (adjacentEvenExtent radius) physical &&
            cutoffOneLiftedFamilyEvent (adjacentEvenAmbient radius)
              (adjacentEvenStrictJointPairFamilyEvent
                radius base roots right left) physical) := by
  have hleft := slabEventNumerator_zeroExtension_eqv_ambientMasked
    coupling cutoff (adjacentEvenExtent radius)
      (cutoffOneLiftedFamilyEvent (adjacentEvenAmbient radius)
        (adjacentEvenStrictJointPairFamilyEvent
          radius base roots left right))
  have hright := slabEventNumerator_zeroExtension_eqv_ambientMasked
    coupling cutoff (adjacentEvenExtent radius)
      (cutoffOneLiftedFamilyEvent (adjacentEvenAmbient radius)
        (adjacentEvenStrictJointPairFamilyEvent
          radius base roots right left))
  change slabEventNumerator coupling cutoff (adjacentEvenExtent radius)
      (adjacentEvenStrictJointPairSlabEvent
        radius base roots left right) ≈
    parametricKEventNumerator coupling cutoff
      (adjacentEvenAmbient radius)
      (fun physical =>
        ambientSlabSupportedB (adjacentEvenExtent radius) physical &&
          cutoffOneLiftedFamilyEvent (adjacentEvenAmbient radius)
            (adjacentEvenStrictJointPairFamilyEvent
              radius base roots left right) physical) at hleft
  change slabEventNumerator coupling cutoff (adjacentEvenExtent radius)
      (adjacentEvenStrictJointPairSlabEvent
        radius base roots right left) ≈
    parametricKEventNumerator coupling cutoff
      (adjacentEvenAmbient radius)
      (fun physical =>
        ambientSlabSupportedB (adjacentEvenExtent radius) physical &&
          cutoffOneLiftedFamilyEvent (adjacentEvenAmbient radius)
            (adjacentEvenStrictJointPairFamilyEvent
              radius base roots right left) physical) at hright
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _
      (slabEventNumerator_adjacentEvenStrictJointPair_eqv
        coupling cutoff hfit hroots left right)
      hright)

/-- Consequently, the exact finite physical law conditioned on slab support
is invariant under exchanging the lower and upper occurrence fingerprints. -/
theorem couplingParametricKPhysicalGivenSlab_adjacentEvenStrictJointPair_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat)
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling cutoff (adjacentEvenExtent radius)
        (adjacentEvenStrictJointPairFamilyEvent
          radius base roots left right) ≈
      couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling cutoff (adjacentEvenExtent radius)
        (adjacentEvenStrictJointPairFamilyEvent
          radius base roots right left) := by
  unfold couplingParametricKPhysicalGivenSlabProbability
  exact divPos_eqv_congr
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hcoupling cutoff (adjacentEvenExtent radius))
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hcoupling cutoff (adjacentEvenExtent radius))
    (parametricKEventNumerator_adjacentEvenStrictJointPair_masked_eqv
      coupling cutoff hfit hroots left right)
    (Q'.eqv_refl _)

#print axioms adjacentEvenStrictJointCylinderRoots_canonical
#print axioms adjacentEvenStrictJointPairFamilyEvent_eq
#print axioms adjacentEvenStrictJointCanonicalAtoms_values
#print axioms adjacentEvenStrictJointCanonicalAtoms_length
#print axioms adjacentEvenStrictJointCanonicalAtoms_supported
#print axioms adjacentEvenStrictJointMarkedCylinderEvent_eq
#print axioms slabToAmbientPhysical_adjacentEven_reflection
#print axioms memberB_adjacentEvenSlabAmbientSupport_reflection
#print axioms adjacentEvenStrictLowerCylinderRoots_canonical
#print axioms adjacentEvenStrictUpperCylinderRoots_canonical
#print axioms adjacentEvenStrictLowerSupportQueryEventB_reflection
#print axioms adjacentEvenStrictUpperSupportQueryEventB_reflection
#print axioms adjacentEvenStrictLowerSupportQueryFingerprint_reflection
#print axioms adjacentEvenStrictUpperSupportQueryFingerprint_reflection
#print axioms adjacentEvenStrictLowerOccurrenceFingerprint_reflection
#print axioms adjacentEvenStrictUpperOccurrenceFingerprint_reflection
#print axioms reflectSlabEvent_adjacentEvenStrictJointPair
#print axioms slabEventNumerator_adjacentEvenStrictJointPair_eqv
#print axioms adjacentEvenStrictJointPairSlabProbability_eqv
#print axioms parametricKEventNumerator_adjacentEvenStrictJointPair_masked_eqv
#print axioms couplingParametricKPhysicalGivenSlab_adjacentEvenStrictJointPair_eqv

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw
