/-
# Decoding a canonical polymer occurrence from local face queries

Occurrence of one connected canonical polymer is a local property of the
occupied-face support.  It holds exactly when every face of the polymer is
occupied and every exterior face sharing a physical link with the polymer is
empty.  Thus a finite list of fixed local polymers can keep its original
constant-size marked-root chart for the carrier argument while its occurrence
fingerprint is read entirely from face-support data.
-/

import YMGap.Continuum.Z4CanonicalCylinderEventTransport
import YMGap.Continuum.Z4CanonicalPolymerRange

namespace YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphComponentUniqueness
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4PhysicalSurfaceComponents

/-! ## 1. The one-link exterior query shell -/

/-- Physical faces outside `polymer` that share a physical link with one of
its faces.  This is the complete one-link shell needed to decide whether the
polymer is a whole connected component rather than a strict sub-support. -/
def canonicalPolymerExteriorFaceQueries
    (n : Nat) (polymer : List Nat) : List Nat :=
  (physicalFaceEdges n).filter (fun outside =>
    (!(decide (outside ∈ polymer))) &&
      polymer.any (fun inside => faceLinkAdjacentB n inside outside))

theorem mem_canonicalPolymerExteriorFaceQueries_iff
    (n : Nat) (polymer : List Nat) (outside : Nat) :
    outside ∈ canonicalPolymerExteriorFaceQueries n polymer ↔
      outside ∈ physicalFaceEdges n ∧ outside ∉ polymer ∧
        ∃ inside, inside ∈ polymer ∧
          faceLinkAdjacentB n inside outside = true := by
  unfold canonicalPolymerExteriorFaceQueries
  rw [List.mem_filter]
  constructor
  · intro h
    have hparts := (Bool.and_eq_true _ _).mp h.2
    have houtside : outside ∉ polymer := by
      intro hmem
      have hdecision : decide (outside ∈ polymer) = true :=
        decide_eq_true hmem
      rw [hdecision] at hparts
      cases hparts.1
    obtain ⟨inside, hinside, hadj⟩ := List.any_eq_true.mp hparts.2
    exact ⟨h.1, houtside, inside, hinside, hadj⟩
  · rintro ⟨hphysical, houtside, inside, hinside, hadj⟩
    refine ⟨hphysical, (Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩⟩
    · have hdecision : decide (outside ∈ polymer) = false :=
        decide_eq_false houtside
      simp only [hdecision, Bool.not_false]
    · exact List.any_eq_true.mpr ⟨inside, hinside, hadj⟩

/-- The literal face-query test for occurrence of `polymer` in `family`:
all internal faces are occupied and all one-link exterior faces are empty. -/
def canonicalPolymerFaceQueryEventB
    (n : Nat) (polymer : List Nat)
    (family : List (List Nat)) : Bool :=
  polymer.all (fun face => familyContainsFaceB face family) &&
    (canonicalPolymerExteriorFaceQueries n polymer).all
      (fun face => !(familyContainsFaceB face family))

/-! ## 2. Exact local decoding on corrected-compatible families -/

theorem canonicalPolymerFaceQueryEventB_true_iff
    {n : Nat} {polymer : List Nat} {family : List (List Nat)}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    canonicalPolymerFaceQueryEventB n polymer family = true ↔
      polymer ∈ family := by
  constructor
  · intro hquery
    have hparts := (Bool.and_eq_true _ _).mp hquery
    have hinternal := List.all_eq_true.mp hparts.1
    have hexterior := List.all_eq_true.mp hparts.2
    obtain ⟨seed, hseedPolymer⟩ :=
      canonicalSurfacePolymers_allNonempty n polymer hpolymer
    have hseedOccupied : familyContainsFaceB seed family = true :=
      hinternal seed hseedPolymer
    obtain ⟨candidate, hcandidate, hseedCandidate⟩ :=
      (familyContainsFaceB_true_iff seed family).1 hseedOccupied
    have hcover := compatibleAmbientFamily_union_covers hfamily
    have hseparated := (compatibleAmbientFamily_invariants hfamily).2
    have hpolymerSubsetUnion : ∀ face, face ∈ polymer →
        face ∈ familyUnionSupport n family := by
      intro face hface
      rw [mem_familyUnionSupport_iff]
      refine ⟨mem_of_mem_sublists (physicalFaceEdges n) polymer
          (canonicalSurfacePolymer_mem_faceSupports hpolymer) face hface,
        ?_⟩
      exact (familyContainsFaceB_true_iff face family).1
        (hinternal face hface)
    have hpolymerSubsetCandidate : ∀ face, face ∈ polymer →
        face ∈ candidate := by
      intro face hface
      have hchain := canonicalSurfacePolymers_allConnected n polymer
        hpolymer seed face hseedPolymer hface
      exact chain_stays_in_separated_component hcover hseparated
        hcandidate hpolymerSubsetUnion hchain hseedCandidate
    have hcandidateFaceSupport :=
      compatibleAmbientFamily_member_faceSupport hfamily hcandidate
    have hcandidateSubsetPolymer : ∀ face, face ∈ candidate →
        face ∈ polymer := by
      intro face hface
      have hchain := compatibleAmbientFamily_allConnected hfamily
        candidate hcandidate seed face hseedCandidate hface
      induction hchain with
      | refl point => exact hseedPolymer
      | @step source next destination hadj hnext rest ih =>
          have hsourcePolymer : source ∈ polymer := by assumption
          have hnextPolymer : next ∈ polymer := by
            by_cases hnextInside : next ∈ polymer
            · exact hnextInside
            ·
              have hnextPhysical : next ∈ physicalFaceEdges n :=
                mem_of_mem_sublists (physicalFaceEdges n) candidate
                  hcandidateFaceSupport next hnext
              have hboundary : next ∈
                  canonicalPolymerExteriorFaceQueries n polymer :=
                (mem_canonicalPolymerExteriorFaceQueries_iff
                  n polymer next).2
                  ⟨hnextPhysical, hnextInside,
                    source, hsourcePolymer, hadj⟩
              have hempty := hexterior next hboundary
              have hoccupied : familyContainsFaceB next family = true :=
                (familyContainsFaceB_true_iff next family).2
                  ⟨candidate, hcandidate, hnext⟩
              rw [hoccupied] at hempty
              cases hempty
          have hnextOccupied : familyContainsFaceB next family = true :=
            (familyContainsFaceB_true_iff next family).2
              ⟨candidate, hcandidate, hnext⟩
          exact ih hnextPolymer hnextOccupied hnext hface
    have heq : polymer = candidate := by
      apply sublists_eq_of_mem_iff (physicalFaceEdges n)
        polymer candidate (physicalFaceEdges_nodup n)
        (canonicalSurfacePolymer_mem_faceSupports hpolymer)
        hcandidateFaceSupport
      intro face
      exact ⟨hpolymerSubsetCandidate face,
        hcandidateSubsetPolymer face⟩
    rw [heq]
    exact hcandidate
  · intro hoccurs
    apply (Bool.and_eq_true _ _).mpr
    constructor
    · apply List.all_eq_true.mpr
      intro face hface
      exact (familyContainsFaceB_true_iff face family).2
        ⟨polymer, hoccurs, hface⟩
    · apply List.all_eq_true.mpr
      intro outside houtsideQuery
      have houtsideData :=
        (mem_canonicalPolymerExteriorFaceQueries_iff
          n polymer outside).1 houtsideQuery
      cases hcontains : familyContainsFaceB outside family with
      | false => rfl
      | true =>
          obtain ⟨other, hother, houtsideOther⟩ :=
            (familyContainsFaceB_true_iff outside family).1 hcontains
          have hne : polymer ≠ other := by
            intro heq
            rw [← heq] at houtsideOther
            exact houtsideData.2.1 houtsideOther
          obtain ⟨inside, hinside, hadj⟩ := houtsideData.2.2
          have hfalse := (compatibleAmbientFamily_invariants hfamily).2
            polymer hoccurs other hother hne inside hinside
              outside houtsideOther
          rw [hadj] at hfalse
          cases hfalse

theorem familyContainsPolymerB_eq_faceQueryEventB
    {n : Nat} {polymer : List Nat} {family : List (List Nat)}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    familyContainsPolymerB polymer family =
      canonicalPolymerFaceQueryEventB n polymer family := by
  apply Bool.eq_iff_iff.mpr
  rw [familyContainsPolymerB]
  simp only [decide_eq_true_eq]
  exact (canonicalPolymerFaceQueryEventB_true_iff
    hpolymer hfamily).symm

/-! ## 3. Reading the same queries from the literal union support -/

def canonicalPolymerSupportQueryEventB
    (n : Nat) (polymer support : List Nat) : Bool :=
  polymer.all (memberB support) &&
    (canonicalPolymerExteriorFaceQueries n polymer).all
      (fun face => !(memberB support face))

theorem familyContainsFaceB_eq_memberB_unionSupport
    {n : Nat} {family : List (List Nat)} {face : Nat}
    (hphysical : face ∈ physicalFaceEdges n) :
    familyContainsFaceB face family =
      memberB (familyUnionSupport n family) face := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hcontains
    apply (memberB_eq_true_iff _ _).2
    rw [mem_familyUnionSupport_iff]
    exact ⟨hphysical,
      (familyContainsFaceB_true_iff face family).1 hcontains⟩
  · intro hsupport
    have hmem := (memberB_eq_true_iff _ _).1 hsupport
    rw [mem_familyUnionSupport_iff] at hmem
    exact (familyContainsFaceB_true_iff face family).2 hmem.2

private theorem listAll_congr_on {A : Type}
    (left right : A → Bool) : ∀ xs : List A,
    (∀ x, x ∈ xs → left x = right x) →
      xs.all left = xs.all right
  | [], _ => rfl
  | head :: tail, h => by
      have hhead := h head List.mem_cons_self
      have htail : ∀ x, x ∈ tail → left x = right x :=
        fun x hx => h x (List.mem_cons_of_mem head hx)
      simp only [List.all_cons, hhead]
      rw [listAll_congr_on left right tail htail]

theorem canonicalPolymerFaceQueryEventB_eq_supportQueryEventB
    {n : Nat} {polymer : List Nat} {family : List (List Nat)}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    canonicalPolymerFaceQueryEventB n polymer family =
      canonicalPolymerSupportQueryEventB n polymer
        (familyUnionSupport n family) := by
  unfold canonicalPolymerFaceQueryEventB
    canonicalPolymerSupportQueryEventB
  have hinternal :
      polymer.all (fun face => familyContainsFaceB face family) =
        polymer.all (memberB (familyUnionSupport n family)) := by
    apply listAll_congr_on
    intro face hface
    exact familyContainsFaceB_eq_memberB_unionSupport
      (mem_of_mem_sublists (physicalFaceEdges n) polymer
        (canonicalSurfacePolymer_mem_faceSupports hpolymer) face hface)
  have hexterior :
      (canonicalPolymerExteriorFaceQueries n polymer).all
          (fun face => !(familyContainsFaceB face family)) =
        (canonicalPolymerExteriorFaceQueries n polymer).all
          (fun face => !(memberB (familyUnionSupport n family) face)) := by
    apply listAll_congr_on
    intro face hface
    exact congrArg Bool.not
      (familyContainsFaceB_eq_memberB_unionSupport
        ((mem_canonicalPolymerExteriorFaceQueries_iff
          n polymer face).1 hface).1)
  rw [hinternal, hexterior]

theorem familyContainsPolymerB_eq_supportQueryEventB
    {n : Nat} {polymer : List Nat} {family : List (List Nat)}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    familyContainsPolymerB polymer family =
      canonicalPolymerSupportQueryEventB n polymer
        (familyUnionSupport n family) := by
  rw [familyContainsPolymerB_eq_faceQueryEventB hpolymer hfamily,
    canonicalPolymerFaceQueryEventB_eq_supportQueryEventB hpolymer]

/-! ## 4. Finite marked-root fingerprints use only local face queries -/

def canonicalRootsFaceQueryFingerprint
    (n : Nat) (roots : List (List Nat))
    (family : List (List Nat)) : List Bool :=
  roots.map (fun root =>
    canonicalPolymerFaceQueryEventB n root family)

def canonicalRootsSupportQueryFingerprint
    (n : Nat) (roots : List (List Nat))
    (support : List Nat) : List Bool :=
  roots.map (fun root =>
    canonicalPolymerSupportQueryEventB n root support)

theorem familyOccurrenceFingerprint_eq_faceQueryFingerprint
    {n : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers n)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    familyOccurrenceFingerprint roots family =
      canonicalRootsFaceQueryFingerprint n roots family := by
  unfold familyOccurrenceFingerprint canonicalRootsFaceQueryFingerprint
  apply List.map_congr_left
  intro root hroot
  exact familyContainsPolymerB_eq_faceQueryEventB
    (hroots root hroot) hfamily

theorem familyOccurrenceFingerprint_eq_supportQueryFingerprint
    {n : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers n)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    familyOccurrenceFingerprint roots family =
      canonicalRootsSupportQueryFingerprint n roots
        (familyUnionSupport n family) := by
  unfold familyOccurrenceFingerprint
    canonicalRootsSupportQueryFingerprint
  apply List.map_congr_left
  intro root hroot
  exact familyContainsPolymerB_eq_supportQueryEventB
    (hroots root hroot) hfamily

theorem sourceCylinderEvent_eq_faceQueryEvent
    {n : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers n)
    (predicate : List Bool → Bool)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    sourceCylinderEvent roots predicate family =
      predicate (canonicalRootsFaceQueryFingerprint n roots family) := by
  unfold sourceCylinderEvent cylinderEvent
  rw [familyOccurrenceFingerprint_eq_faceQueryFingerprint hroots hfamily]

theorem sourceCylinderEvent_eq_supportQueryEvent
    {n : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers n)
    (predicate : List Bool → Bool)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    sourceCylinderEvent roots predicate family =
      predicate (canonicalRootsSupportQueryFingerprint n roots
        (familyUnionSupport n family)) := by
  unfold sourceCylinderEvent cylinderEvent
  rw [familyOccurrenceFingerprint_eq_supportQueryFingerprint
    hroots hfamily]

#print axioms mem_canonicalPolymerExteriorFaceQueries_iff
#print axioms canonicalPolymerFaceQueryEventB_true_iff
#print axioms familyContainsPolymerB_eq_faceQueryEventB
#print axioms familyContainsFaceB_eq_memberB_unionSupport
#print axioms canonicalPolymerFaceQueryEventB_eq_supportQueryEventB
#print axioms familyContainsPolymerB_eq_supportQueryEventB
#print axioms familyOccurrenceFingerprint_eq_faceQueryFingerprint
#print axioms familyOccurrenceFingerprint_eq_supportQueryFingerprint
#print axioms sourceCylinderEvent_eq_faceQueryEvent
#print axioms sourceCylinderEvent_eq_supportQueryEvent

end YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
