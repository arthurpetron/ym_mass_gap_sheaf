/-
# Conditional stability of the adjacent-even one-step marked event

The exact adjacent-even EventLaw lives in the corrected even slab of extent
`2 * radius + 2`.  This leaf compares that conditioned law with the literal
ambient finite-volume law.  The one additional ambient layer gives the marked
root carrier a `stage + 4` size floor.  Internal root faces and the complete
one-link exterior query shell are treated separately.

All arguments are finite and decidable.  The only analytic restriction is the
existing strong-coupling interval needed by the carrier tail estimate.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw
import YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepConditionalStability

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierFixedSize
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStability
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionTopBoundaryTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open Dir4

local infix:50 " ≈ " => Q'.eqv

private theorem timeCoordinate_linf_floor_adjacentEven
    {root q : Z4Plaq} {rootTime qTime distance : Nat}
    (hrootTime : root.1.2.2.2 = rootTime)
    (hqTime : q.1.2.2.2 = qTime)
    (hseparation : rootTime + distance ≤ qTime) :
    distance ≤ linfDist root q := by
  have hmetric := le_linfDist_comp root q x3
  obtain ⟨⟨a, b, c, d⟩, rootPlane⟩ := root
  obtain ⟨⟨e, f, g, h⟩, qPlane⟩ := q
  change d = rootTime at hrootTime
  change h = qTime at hqTime
  simp only [natDist, cPlaq, vComp] at hmetric
  omega

/-! ## 1. Internal and exterior geometric carrier floors -/

/-- Every marked root face is at least `stage + 3` in `linfDist` from a
plaquette omitted by the adjacent-even corrected slab. -/
theorem adjacentEvenStrictJointRoot_nonSlab_linf_floor
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    {target : List Nat}
    (htarget : target ∈ adjacentEvenStrictJointCylinderRoots
      (strictQueryBase (base + 1) + stage) base roots)
    {face : Nat} (hface : face ∈ target)
    {q : Z4Plaq}
    (hqBox : q ∈ boxPlaquettes
      (adjacentEvenAmbient (strictQueryBase (base + 1) + stage)))
    (hqNot : q ∉ boundaryCompleteSlabPlaquettes
      (adjacentEvenExtent (strictQueryBase (base + 1) + stage))) :
    stage + 3 ≤ linfDist
      (boxPlaquetteAt
        (adjacentEvenAmbient (strictQueryBase (base + 1) + stage)) face) q := by
  have hfit : strictQueryBase (base + 1) ≤
      strictQueryBase (base + 1) + stage :=
    Nat.le_add_right (strictQueryBase (base + 1)) stage
  have hparts := List.mem_append.mp htarget
  cases hparts with
  | inl hlower =>
      obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp hlower
      rw [← htargetEq] at hface
      have hrootTime :=
        adjacentEvenStrictLowerCanonicalRoot_time_add_two_le
          hfit (hroots source hsource) hface
      have hqTime := ambient_nonSlab_time_eq_extent hqBox hqNot
      apply timeCoordinate_linf_floor_adjacentEven
        (rootTime :=
          (boxPlaquetteAt
            (adjacentEvenAmbient
              (strictQueryBase (base + 1) + stage)) face).1.2.2.2)
        (qTime := adjacentEvenExtent
          (strictQueryBase (base + 1) + stage))
      · rfl
      · exact hqTime
      · unfold adjacentEvenExtent centralExtent
        omega
  | inr hupper =>
      obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp hupper
      rw [← htargetEq] at hface
      have hrootTime := adjacentEvenStrictUpperCanonicalRoot_time_lt
        hfit (hroots source hsource) hface
      have hqTime := ambient_nonSlab_time_eq_extent hqBox hqNot
      apply timeCoordinate_linf_floor_adjacentEven
        (rootTime :=
          (boxPlaquetteAt
            (adjacentEvenAmbient
              (strictQueryBase (base + 1) + stage)) face).1.2.2.2)
        (qTime := adjacentEvenExtent
          (strictQueryBase (base + 1) + stage))
      · rfl
      · exact hqTime
      · unfold adjacentEvenExtent centralExtent
        omega

/-- The complete upper exterior shell obeys the sharper time estimate needed
to retain a growing boundary margin; its previously exposed slab-membership
bound alone would forget this quantitative information. -/
theorem adjacentEvenStrictUpperCanonicalRoot_exterior_time_le_shiftedBase
    {radius base : Nat}
    (hfit : strictQueryBase (base + 1) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictUpperCanonicalRoot radius base root)) :
    (boxPlaquetteAt (adjacentEvenAmbient radius) face).1.2.2.2 ≤
      radius + strictQueryBase (base + 1) := by
  obtain ⟨_hphysical, _houtside, inside, hinside, hadj⟩ :=
    (mem_canonicalPolymerExteriorFaceQueries_iff
      (adjacentEvenAmbient radius)
      (adjacentEvenStrictUpperCanonicalRoot radius base root) face).1 hface
  have hinsideTime := adjacentEvenStrictUpperCanonicalRoot_time_lt
    hfit hroot hinside
  have hforward := actualAdjacentOfFaceLinkAdjacent hadj
  have hreverse : z4Chain.toLattice.Adjacent
      (boxPlaquetteAt (adjacentEvenAmbient radius) face)
      (boxPlaquetteAt (adjacentEvenAmbient radius) inside) := {
    link := hforward.link
    on_p := hforward.on_q
    on_q := hforward.on_p
  }
  have htimeStep := adjacent_time_le_add_one hreverse
  omega

/-- Every face in the complete one-link exterior query shell retains the sharp
one-step-smaller `stage + 2` lower bound from the omitted ambient layer. -/
theorem adjacentEvenStrictJointExterior_nonSlab_linf_floor
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    {target : List Nat}
    (htarget : target ∈ adjacentEvenStrictJointCylinderRoots
      (strictQueryBase (base + 1) + stage) base roots)
    {face : Nat}
    (hface : face ∈ canonicalPolymerExteriorFaceQueries
      (adjacentEvenAmbient (strictQueryBase (base + 1) + stage)) target)
    {q : Z4Plaq}
    (hqBox : q ∈ boxPlaquettes
      (adjacentEvenAmbient (strictQueryBase (base + 1) + stage)))
    (hqNot : q ∉ boundaryCompleteSlabPlaquettes
      (adjacentEvenExtent (strictQueryBase (base + 1) + stage))) :
    stage + 2 ≤ linfDist
      (boxPlaquetteAt
        (adjacentEvenAmbient (strictQueryBase (base + 1) + stage)) face) q := by
  have hfit : strictQueryBase (base + 1) ≤
      strictQueryBase (base + 1) + stage :=
    Nat.le_add_right (strictQueryBase (base + 1)) stage
  have hparts := List.mem_append.mp htarget
  cases hparts with
  | inl hlower =>
      obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp hlower
      rw [← htargetEq] at hface
      have hrootTime :=
        adjacentEvenStrictLowerCanonicalRoot_exterior_time_add_one_le
          hfit (hroots source hsource) hface
      have hqTime := ambient_nonSlab_time_eq_extent hqBox hqNot
      apply timeCoordinate_linf_floor_adjacentEven
        (rootTime :=
          (boxPlaquetteAt
            (adjacentEvenAmbient
              (strictQueryBase (base + 1) + stage)) face).1.2.2.2)
        (qTime := adjacentEvenExtent
          (strictQueryBase (base + 1) + stage))
      · rfl
      · exact hqTime
      · unfold adjacentEvenExtent centralExtent
        omega
  | inr hupper =>
      obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp hupper
      rw [← htargetEq] at hface
      have hrootTime :=
        adjacentEvenStrictUpperCanonicalRoot_exterior_time_le_shiftedBase
          hfit (hroots source hsource) hface
      have hqTime := ambient_nonSlab_time_eq_extent hqBox hqNot
      apply timeCoordinate_linf_floor_adjacentEven
        (rootTime :=
          (boxPlaquetteAt
            (adjacentEvenAmbient
              (strictQueryBase (base + 1) + stage)) face).1.2.2.2)
        (qTime := adjacentEvenExtent
          (strictQueryBase (base + 1) + stage))
      · rfl
      · exact hqTime
      · unfold adjacentEvenExtent centralExtent
        omega

/-! ## 2. The `stage + 4` connected-carrier floor -/

/-- A connected switched residue selected by any Boolean predicate contains a
carrier with at least `stage + 4` plaquettes.  The proof is independent of the
predicate, so it applies unchanged to its Boolean complement. -/
theorem adjacentEvenStrictJointConnectedCarrierSupport_floor
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom
      (adjacentEvenAmbient (strictQueryBase (base + 1) + stage)))
    (entry : SlabConnectedSourceEntry
      (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
      (adjacentEvenStrictJointCanonicalAtoms
        (strictQueryBase (base + 1) + stage) base roots
        (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots)
      predicate) :
    stage + 4 ≤
      (slabConnectedCarrierSupport defaultRoot entry).length := by
  let atoms := adjacentEvenStrictJointCanonicalAtoms
    (strictQueryBase (base + 1) + stage) base roots
    (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots
  let selected := slabSourceRootAtom defaultRoot entry.val
  have hselected : selected ∈ atoms :=
    (slabSourceRootAtom_spec defaultRoot entry.val entry.property).2
  have hselectedValue : selected.val ∈
      adjacentEvenStrictJointCylinderRoots
        (strictQueryBase (base + 1) + stage) base roots := by
    have hmapped : selected.val ∈ atoms.map Subtype.val :=
      List.mem_map.mpr ⟨selected, hselected, rfl⟩
    simpa only [atoms,
      adjacentEvenStrictJointCanonicalAtoms_values] using hmapped
  have hrootFace := slabCanonicalAtomFirstFace_mem selected
  apply slabConnectedCarrierSupport_linf_size_floor
    defaultRoot
    (adjacentEvenStrictJointCanonicalAtoms_supported
      (strictQueryBase (base + 1) + stage) base roots
      (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots)
    entry hrootFace
  intro q hqBox hqOutside
  exact adjacentEvenStrictJointRoot_nonSlab_linf_floor
    hroots hselectedValue hrootFace hqBox hqOutside

/-! ## 3. Ambient-versus-conditioned probability bounds -/

/-- Predicate-uniform adjacent-even conditional stability.  The bound is
uniform in the finite character cutoff and has the exact doubled marked-root
count and the improved `stage + 4` carrier floor. -/
theorem couplingPhysicalAdjacentEvenStrictJointPredicate_givenSlab_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool)
    (defaultRoot : CanonicalAtom
      (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))) :
    let atoms := adjacentEvenStrictJointCanonicalAtoms
      (strictQueryBase (base + 1) + stage) base roots
      (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots
    Q'.abs
        (couplingKFamilyEventProbability coupling hcoupling cutoff
            (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))
            (slabMarkedCylinderEvent atoms predicate) -
          couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
            (slabMarkedCylinderEvent atoms predicate)) ≤
      couplingSlabConditionalBoundaryEpsilon
        (2 * roots.length) (stage + 4) := by
  dsimp only
  let atoms := adjacentEvenStrictJointCanonicalAtoms
    (strictQueryBase (base + 1) + stage) base roots
    (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots
  have hsupported : ∀ atom, atom ∈ atoms →
      canonicalPolymerSlabSupportedB
        (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
        atom.val = true := by
    simpa only [atoms] using
      (adjacentEvenStrictJointCanonicalAtoms_supported
        (strictQueryBase (base + 1) + stage) base roots
        (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots)
  have hfloorPredicate :
      ∀ entry : SlabConnectedSourceEntry
          (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
          atoms predicate,
        stage + 4 ≤
          (slabConnectedCarrierSupport defaultRoot entry).length := by
    intro entry
    simpa only [atoms] using
      (adjacentEvenStrictJointConnectedCarrierSupport_floor
        hroots defaultRoot entry)
  have hfloorComplement :
      ∀ entry : SlabConnectedSourceEntry
          (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
          atoms (complementSlabPredicate predicate),
        stage + 4 ≤
          (slabConnectedCarrierSupport defaultRoot entry).length := by
    intro entry
    simpa only [atoms] using
      (adjacentEvenStrictJointConnectedCarrierSupport_floor
        hroots defaultRoot entry)
  have hbound :=
    couplingPhysicalAmbient_givenSlabProbability_abs_sub_le_of_floors
      (extent :=
        adjacentEvenExtent (strictQueryBase (base + 1) + stage))
      (roots := atoms) hcoupling hle cutoff predicate defaultRoot
      hsupported (stage + 4) hfloorPredicate hfloorComplement
  have hlength : atoms.length = roots.length + roots.length := by
    simpa only [atoms] using
      (adjacentEvenStrictJointCanonicalAtoms_length
        (strictQueryBase (base + 1) + stage) base roots
        (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots)
  have hcount : atoms.length = 2 * roots.length := by
    omega
  have hboundRoots := hcount ▸ hbound
  simpa only [atoms, adjacentEvenAmbient] using hboundRoots

/-- The same stability estimate stated for the source-ordered lower/upper
pair-family event used by the exact EventLaw. -/
theorem couplingPhysicalAdjacentEvenStrictJointPair_givenSlab_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool)
    (defaultRoot : CanonicalAtom
      (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))) :
    Q'.abs
        (couplingKFamilyEventProbability coupling hcoupling cutoff
            (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))
            (adjacentEvenStrictJointPairFamilyEvent
              (strictQueryBase (base + 1) + stage)
              base roots left right) -
          couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
            (adjacentEvenStrictJointPairFamilyEvent
              (strictQueryBase (base + 1) + stage)
              base roots left right)) ≤
      couplingSlabConditionalBoundaryEpsilon
        (2 * roots.length) (stage + 4) := by
  have hbound :=
    couplingPhysicalAdjacentEvenStrictJointPredicate_givenSlab_abs_sub_le
      hcoupling hle cutoff hroots
      (centralStrictJointPairPredicate roots.length left right) defaultRoot
  dsimp only at hbound
  rw [adjacentEvenStrictJointMarkedCylinderEvent_eq
    (strictQueryBase (base + 1) + stage) base roots
    (Nat.le_add_right (strictQueryBase (base + 1)) stage)
    hroots left right] at hbound
  exact hbound

#print axioms adjacentEvenStrictJointRoot_nonSlab_linf_floor
#print axioms adjacentEvenStrictUpperCanonicalRoot_exterior_time_le_shiftedBase
#print axioms adjacentEvenStrictJointExterior_nonSlab_linf_floor
#print axioms adjacentEvenStrictJointConnectedCarrierSupport_floor
#print axioms couplingPhysicalAdjacentEvenStrictJointPredicate_givenSlab_abs_sub_le
#print axioms couplingPhysicalAdjacentEvenStrictJointPair_givenSlab_abs_sub_le

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepConditionalStability
