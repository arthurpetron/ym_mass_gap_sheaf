/-
# Reading lower-half local face queries from support coordinates

A complete lower-half support is a list of corrected-slab face identifiers.
We turn it into a zero-one slab labelling, embed that labelling in the adjacent
ambient box, and read local canonical-polymer queries from its occupied ambient
faces.  On every geometrically lower ambient face this reconstruction has
exactly the same occupied bit as the original physical labelling.
-/

import YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
import YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
import YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram

namespace YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
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
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality

/-- Occupied ambient face identifiers reconstructed from one lower-half
support list; every fixed, upper, and non-slab face is zero. -/
def centralLowerSupportAmbientFaces
    (half : Nat) (support : List Nat) : List Nat :=
  excitedPlaquetteIds (centralAmbient half)
    (slabToAmbientPhysical (centralExtent half)
      (componentLabel support))

/-- Local canonical-root fingerprint of a complete lower-half support. -/
def centralLowerSupportQueryFingerprint
    (half : Nat) (roots : List (List Nat))
    (support : List Nat) : List Bool :=
  canonicalRootsSupportQueryFingerprint (centralAmbient half) roots
    (centralLowerSupportAmbientFaces half support)

theorem lowerAmbientFace_mem_centralSlab
    {half targetId : Nat}
    (htarget : targetId ∈ physicalFaceEdges (centralAmbient half))
    (hlower : plaquetteHalfSide half
      (boxPlaquetteAt (centralAmbient half) targetId) = .lower) :
    boxPlaquetteAt (centralAmbient half) targetId ∈
      boundaryCompleteSlabPlaquettes (centralExtent half) := by
  apply (mem_boundaryCompleteSlabPlaquettes _ _).2
  constructor
  · simpa only [centralAmbient] using
      (boxPlaquetteAt_mem_boxPlaquettes_of_physical htarget)
  · generalize hplaquette :
      boxPlaquetteAt (centralAmbient half) targetId = plaquette at hlower ⊢
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
    cases plane <;>
      simp only [plaquetteHalfSide] at hlower <;>
      by_cases hle : d ≤ half <;>
      by_cases hlt : d < half <;>
      by_cases heq : d = half <;>
      simp [spatialHalfSide, temporalHalfSide, hle, hlt, heq,
        plaquetteTimeAdmissible, centralExtent] at hlower ⊢ <;>
      omega

private theorem slabPlaquetteAt_eq_of_enumerate_local
    {extent id : Nat}
    {plaquette : YMGap.Continuum.ClusterCount4DProgress.Z4Plaq}
    (hindexed : (id, plaquette) ∈
      enumerate (boundaryCompleteSlabPlaquettes extent)) :
    slabPlaquetteAt extent id = plaquette := by
  unfold slabPlaquetteAt
  exact enumerate_getD_of_mem fallbackPlaquette hindexed

/-- The reconstructed lower-support bit equals the original physical bit on
every ambient face belonging to the geometric lower half. -/
theorem centralLowerSupportAmbient_memberB_eq_physical
    (half : Nat) (physical : EdgeLabelling) {targetId : Nat}
    (htarget : targetId ∈ physicalFaceEdges (centralAmbient half))
    (hlower : plaquetteHalfSide half
      (boxPlaquetteAt (centralAmbient half) targetId) = .lower) :
    memberB
        (centralLowerSupportAmbientFaces half
          (centralHalfSupportCode half
            (centralLowerRestriction half
              (ambientToSlabPhysical (centralExtent half) physical))))
        targetId =
      memberB (excitedPlaquetteIds (centralAmbient half) physical)
        targetId := by
  have hslab := lowerAmbientFace_mem_centralSlab htarget hlower
  obtain ⟨sourceId, hsourceIndexed⟩ :=
    exists_mem_enumerate hslab
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
    unfold physicalFaceEdges plaquetteEdgeCount at htarget
    exact List.mem_range.mp htarget
  apply Bool.eq_iff_iff.mpr
  simp only [memberB_eq_true_iff]
  constructor
  · intro hreconstructed
    have hpositiveReconstructed :=
      (List.mem_filter.mp hreconstructed).2
    simp only [decide_eq_true_eq] at hpositiveReconstructed
    unfold centralLowerSupportAmbientFaces at hreconstructed
    have hspin :
        slabToAmbientPhysical (centralExtent half)
            (componentLabel
              (centralHalfSupportCode half
                (centralLowerRestriction half
                  (ambientToSlabPhysical (centralExtent half) physical))))
            targetId =
          componentLabel
              (centralHalfSupportCode half
                (centralLowerRestriction half
                  (ambientToSlabPhysical (centralExtent half) physical)))
            sourceId := by
      rw [slabToAmbientPhysical_eq_on_enumerate htargetIndexed,
        slabGeometricSpin_eq_of_enumerate hsourceIndexed]
    rw [hspin] at hpositiveReconstructed
    have hsourceSupport : sourceId ∈
        centralHalfSupportCode half
          (centralLowerRestriction half
            (ambientToSlabPhysical (centralExtent half) physical)) := by
      by_cases hmem : sourceId ∈
          centralHalfSupportCode half
            (centralLowerRestriction half
              (ambientToSlabPhysical (centralExtent half) physical))
      · exact hmem
      · rw [componentLabel_eq_zero_of_not_mem hmem]
          at hpositiveReconstructed
        omega
    have hpositiveSource := (List.mem_filter.mp hsourceSupport).2
    simp only [decide_eq_true_eq] at hpositiveSource
    unfold centralLowerRestriction at hpositiveSource
    rw [if_pos hsourceLower,
      ambientToSlabPhysical_eq_on_physical hsourcePhysical,
      hsourceAt] at hpositiveSource
    change 1 ≤ geometricSpinOfPhysical (centralAmbient half) physical
      (boxPlaquetteAt (centralAmbient half) targetId) at hpositiveSource
    rw [geometricSpinOfPhysical_eq_of_enumerate htargetIndexed]
      at hpositiveSource
    apply List.mem_filter.mpr
    exact ⟨htarget, decide_eq_true hpositiveSource⟩
  · intro horiginal
    have hpositiveOriginal := (List.mem_filter.mp horiginal).2
    simp only [decide_eq_true_eq] at hpositiveOriginal
    have hpositiveSource : 1 ≤
        centralLowerRestriction half
          (ambientToSlabPhysical (centralExtent half) physical) sourceId := by
      unfold centralLowerRestriction
      rw [if_pos hsourceLower,
        ambientToSlabPhysical_eq_on_physical hsourcePhysical,
        hsourceAt]
      change 1 ≤ geometricSpinOfPhysical (centralAmbient half) physical
        (boxPlaquetteAt (centralAmbient half) targetId)
      rw [geometricSpinOfPhysical_eq_of_enumerate htargetIndexed]
      exact hpositiveOriginal
    have hsourceSupport : sourceId ∈
        centralHalfSupportCode half
          (centralLowerRestriction half
            (ambientToSlabPhysical (centralExtent half) physical)) := by
      unfold centralHalfSupportCode
      apply List.mem_filter.mpr
      exact ⟨hsourceLower, decide_eq_true hpositiveSource⟩
    have hcomponent :
        componentLabel
          (centralHalfSupportCode half
            (centralLowerRestriction half
              (ambientToSlabPhysical (centralExtent half) physical)))
          sourceId = 1 :=
      componentLabel_eq_one_iff.mpr hsourceSupport
    unfold centralLowerSupportAmbientFaces excitedPlaquetteIds
    apply List.mem_filter.mpr
    refine ⟨htarget, decide_eq_true ?_⟩
    rw [slabToAmbientPhysical_eq_on_enumerate htargetIndexed,
      slabGeometricSpin_eq_of_enumerate hsourceIndexed, hcomponent]
    exact Nat.le_refl 1

private theorem listAll_congr_on_local {A : Type}
    (left right : A → Bool) : ∀ xs : List A,
    (∀ x, x ∈ xs → left x = right x) →
      xs.all left = xs.all right
  | [], _ => rfl
  | head :: tail, h => by
      have hhead := h head List.mem_cons_self
      have htail : ∀ x, x ∈ tail → left x = right x :=
        fun x hx => h x (List.mem_cons_of_mem head hx)
      simp only [List.all_cons, hhead]
      rw [listAll_congr_on_local left right tail htail]

/-- Every local occurrence query supported strictly in the geometric lower
half is read exactly from the complete lower-support coordinate.  The
hypotheses explicitly include both the polymer faces and their one-link
exterior shell, because both are needed to decide a whole connected-component
occurrence. -/
theorem centralLowerSupportQueryFingerprint_physical
    (half : Nat) (roots : List (List Nat)) (physical : EdgeLabelling)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers (centralAmbient half))
    (hinternalLower : ∀ root, root ∈ roots →
      ∀ face, face ∈ root →
        plaquetteHalfSide half
          (boxPlaquetteAt (centralAmbient half) face) = .lower)
    (hexteriorLower : ∀ root, root ∈ roots →
      ∀ face, face ∈
        canonicalPolymerExteriorFaceQueries (centralAmbient half) root →
          plaquetteHalfSide half
            (boxPlaquetteAt (centralAmbient half) face) = .lower) :
    centralLowerSupportQueryFingerprint half roots
        (centralHalfSupportCode half
          (centralLowerRestriction half
            (ambientToSlabPhysical (centralExtent half) physical))) =
      canonicalRootsSupportQueryFingerprint (centralAmbient half) roots
        (excitedPlaquetteIds (centralAmbient half) physical) := by
  unfold centralLowerSupportQueryFingerprint
    canonicalRootsSupportQueryFingerprint
  apply List.map_congr_left
  intro root hroot
  unfold canonicalPolymerSupportQueryEventB
  have hinternal :
      root.all
          (memberB
            (centralLowerSupportAmbientFaces half
              (centralHalfSupportCode half
                (centralLowerRestriction half
                  (ambientToSlabPhysical (centralExtent half) physical))))) =
        root.all
          (memberB (excitedPlaquetteIds (centralAmbient half) physical)) := by
    apply listAll_congr_on_local
    intro face hface
    apply centralLowerSupportAmbient_memberB_eq_physical half physical
    · exact mem_of_mem_sublists (physicalFaceEdges (centralAmbient half))
        root (canonicalSurfacePolymer_mem_faceSupports (hroots root hroot))
        face hface
    · exact hinternalLower root hroot face hface
  have hexterior :
      (canonicalPolymerExteriorFaceQueries
          (centralAmbient half) root).all
          (fun face =>
            !(memberB
              (centralLowerSupportAmbientFaces half
                (centralHalfSupportCode half
                  (centralLowerRestriction half
                    (ambientToSlabPhysical (centralExtent half) physical))))
              face)) =
        (canonicalPolymerExteriorFaceQueries
          (centralAmbient half) root).all
          (fun face =>
            !(memberB
              (excitedPlaquetteIds (centralAmbient half) physical) face)) := by
    apply listAll_congr_on_local
    intro face hface
    apply congrArg Bool.not
    apply centralLowerSupportAmbient_memberB_eq_physical half physical
    · exact (mem_canonicalPolymerExteriorFaceQueries_iff
        (centralAmbient half) root face).1 hface |>.1
    · exact hexteriorLower root hroot face hface
  rw [hinternal, hexterior]

/-- The union-support presentation of the canonical component family is
literally the original occupied-face support, not merely pointwise
equivalent. -/
theorem physicalCanonicalAmbientFamily_unionSupport
    (n : Nat) (physical : EdgeLabelling) :
    familyUnionSupport n (physicalCanonicalAmbientFamily n physical) =
      excitedPlaquetteIds n physical := by
  unfold familyUnionSupport excitedPlaquetteIds
  apply List.filter_congr
  intro face hface
  apply Bool.eq_iff_iff.mpr
  simp only [familyContainsFaceB_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨polymer, hpolymer, hfacePolymer⟩
    have hexcited :=
      (mem_physicalCanonicalAmbientFamily_flatten_iff
        n physical face).1
        (List.mem_flatten.mpr
          ⟨polymer, hpolymer, hfacePolymer⟩)
    simpa only [decide_eq_true_eq] using
      (List.mem_filter.mp hexcited).2
  · intro hpositive
    have hexcited : face ∈ excitedPlaquetteIds n physical := by
      unfold excitedPlaquetteIds
      exact List.mem_filter.mpr ⟨hface, decide_eq_true hpositive⟩
    have hflatten :=
      (mem_physicalCanonicalAmbientFamily_flatten_iff
        n physical face).2 hexcited
    exact List.mem_flatten.mp hflatten

/-- Under the same explicit lower-query geometry, the complete lower support
coordinate decodes the canonical component-occurrence fingerprint of the
original physical configuration. -/
theorem centralLowerSupportQueryFingerprint_eq_familyOccurrence
    (half : Nat) (roots : List (List Nat)) (physical : EdgeLabelling)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers (centralAmbient half))
    (hinternalLower : ∀ root, root ∈ roots →
      ∀ face, face ∈ root →
        plaquetteHalfSide half
          (boxPlaquetteAt (centralAmbient half) face) = .lower)
    (hexteriorLower : ∀ root, root ∈ roots →
      ∀ face, face ∈
        canonicalPolymerExteriorFaceQueries (centralAmbient half) root →
          plaquetteHalfSide half
            (boxPlaquetteAt (centralAmbient half) face) = .lower) :
    centralLowerSupportQueryFingerprint half roots
        (centralHalfSupportCode half
          (centralLowerRestriction half
            (ambientToSlabPhysical (centralExtent half) physical))) =
      familyOccurrenceFingerprint roots
        (physicalCanonicalAmbientFamily (centralAmbient half) physical) := by
  calc
    centralLowerSupportQueryFingerprint half roots
        (centralHalfSupportCode half
          (centralLowerRestriction half
            (ambientToSlabPhysical (centralExtent half) physical))) =
        canonicalRootsSupportQueryFingerprint (centralAmbient half) roots
          (excitedPlaquetteIds (centralAmbient half) physical) :=
      centralLowerSupportQueryFingerprint_physical half roots physical
        hroots hinternalLower hexteriorLower
    _ = canonicalRootsSupportQueryFingerprint (centralAmbient half) roots
          (familyUnionSupport (centralAmbient half)
            (physicalCanonicalAmbientFamily (centralAmbient half) physical)) := by
      rw [physicalCanonicalAmbientFamily_unionSupport]
    _ = familyOccurrenceFingerprint roots
          (physicalCanonicalAmbientFamily (centralAmbient half) physical) :=
      (familyOccurrenceFingerprint_eq_supportQueryFingerprint hroots
        (physicalCanonicalAmbientFamily_mem_compatible
          (centralAmbient half) physical)).symm

#print axioms centralLowerSupportAmbient_memberB_eq_physical
#print axioms centralLowerSupportQueryFingerprint_physical
#print axioms physicalCanonicalAmbientFamily_unionSupport
#print axioms centralLowerSupportQueryFingerprint_eq_familyOccurrence

end YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
