/-
# Geometric size floor for canonical incompatibility walks

Two corrected-canonical polymers are incompatible exactly when some pair of
their numerical plaquettes is equal or shares an actual lattice link.  This
module extracts that witness constructively and packages finite chains of such
contacts.  A chain starting at one plaquette and ending at another has total
plaquette count at least their L-infinity separation plus one.

Thus a connected incompatibility cluster joining a local polymer to a remote
box boundary must pay total surface size.  This is the geometric input for the
next KP/Penrose summation; no cancellation or probability bound is asserted
here.
-/

import YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

namespace YMGap.Continuum.Z4CanonicalIncompatibilityWalk

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4PhysicalSurfaceComponents

/-! ## 1. Constructive witnesses for corrected incompatibility -/

private theorem exists_false_of_all_false {A : Type} (test : A → Bool) :
    ∀ xs : List A, xs.all test = false →
      ∃ item, item ∈ xs ∧ test item = false
  | [], h => by cases h
  | head :: tail, h => by
      cases hhead : test head with
      | false => exact ⟨head, List.mem_cons_self, hhead⟩
      | true =>
          have htail : tail.all test = false := by
            simpa only [List.all_cons, hhead, Bool.true_and] using h
          obtain ⟨item, hitem, hfalse⟩ :=
            exists_false_of_all_false test tail htail
          exact ⟨item, List.mem_cons_of_mem head hitem, hfalse⟩

private theorem all_false_of_mem_false {A : Type} (test : A → Bool) :
    ∀ {xs : List A} {item : A}, item ∈ xs → test item = false →
      xs.all test = false
  | [], _, hmem, _ => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem, hfalse => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp only [List.all_cons, hfalse, Bool.false_and]
      · cases hhead : test head with
        | false => simp only [List.all_cons, hhead, Bool.false_and]
        | true =>
            simp only [List.all_cons, hhead, Bool.true_and]
            exact all_false_of_mem_false test htail hfalse

/-- A false corrected-compatibility test exposes an actual same-face or
shared-link contact. -/
theorem canonicalPolymer_incompatible_contact
    {n : Nat} {left right : List Nat}
    (hincompatible : canonicalPolymerCompatibleB n left right = false) :
    ∃ leftFace, leftFace ∈ left ∧
      ∃ rightFace, rightFace ∈ right ∧
        (leftFace = rightFace ∨
          faceLinkAdjacentB n leftFace rightFace = true) := by
  unfold canonicalPolymerCompatibleB at hincompatible
  obtain ⟨leftFace, hleft, hrightAll⟩ :=
    exists_false_of_all_false _ left hincompatible
  obtain ⟨rightFace, hright, hpair⟩ :=
    exists_false_of_all_false _ right hrightAll
  refine ⟨leftFace, hleft, rightFace, hright, ?_⟩
  cases heq : decide (leftFace = rightFace) with
  | true => exact Or.inl (of_decide_eq_true heq)
  | false =>
      cases hadj : faceLinkAdjacentB n leftFace rightFace with
      | true => exact Or.inr rfl
      | false =>
          simp only [heq, Bool.not_false, hadj, Bool.true_and] at hpair
          cases hpair

/-- Conversely, a displayed same-face/shared-link contact forces the
corrected compatibility test to be false. -/
theorem canonicalPolymerCompatibleB_false_of_contact
    {n : Nat} {left right : List Nat}
    {leftFace rightFace : Nat}
    (hleft : leftFace ∈ left) (hright : rightFace ∈ right)
    (hcontact : leftFace = rightFace ∨
      faceLinkAdjacentB n leftFace rightFace = true) :
    canonicalPolymerCompatibleB n left right = false := by
  unfold canonicalPolymerCompatibleB
  apply all_false_of_mem_false _ hleft
  apply all_false_of_mem_false _ hright
  rcases hcontact with heq | hadj
  · subst rightFace
    simp
  · cases heq : decide (leftFace = rightFace) <;>
      simp [hadj]

/-- Corrected canonical compatibility is symmetric. -/
theorem canonicalPolymerCompatibleB_symm
    (n : Nat) (left right : List Nat) :
    canonicalPolymerCompatibleB n left right =
      canonicalPolymerCompatibleB n right left := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hleft
    cases hright : canonicalPolymerCompatibleB n right left with
    | true => rfl
    | false =>
        obtain ⟨rightFace, hrightFace, leftFace, hleftFace, hcontact⟩ :=
          canonicalPolymer_incompatible_contact hright
        have hreversed : leftFace = rightFace ∨
            faceLinkAdjacentB n leftFace rightFace = true := by
          rcases hcontact with heq | hadj
          · exact Or.inl heq.symm
          · apply Or.inr
            rw [faceLinkAdjacentB_symm n leftFace rightFace]
            exact hadj
        have hfalse := canonicalPolymerCompatibleB_false_of_contact
          hleftFace hrightFace hreversed
        rw [hfalse] at hleft
        cases hleft
  · intro hright
    cases hleft : canonicalPolymerCompatibleB n left right with
    | true => rfl
    | false =>
        obtain ⟨leftFace, hleftFace, rightFace, hrightFace, hcontact⟩ :=
          canonicalPolymer_incompatible_contact hleft
        have hreversed : rightFace = leftFace ∨
            faceLinkAdjacentB n rightFace leftFace = true := by
          rcases hcontact with heq | hadj
          · exact Or.inl heq.symm
          · apply Or.inr
            rw [faceLinkAdjacentB_symm n rightFace leftFace]
            exact hadj
        have hfalse := canonicalPolymerCompatibleB_false_of_contact
          hrightFace hleftFace hreversed
        rw [hfalse] at hright
        cases hright

/-- A corrected incompatibility contact moves L-infinity distance at most
one in the actual Z4 plaquette geometry. -/
theorem incompatible_contact_linfDist_le_one
    {n leftFace rightFace : Nat}
    (hcontact : leftFace = rightFace ∨
      faceLinkAdjacentB n leftFace rightFace = true) :
    linfDist (boxPlaquetteAt n leftFace)
      (boxPlaquetteAt n rightFace) ≤ 1 := by
  rcases hcontact with heq | hadj
  · subst rightFace
    unfold linfDist
    simp only [natDist_self, Nat.max_self]
    omega
  · exact z4_nbrs_linfDist_le _ _
      (z4Chain.adjacent_mem_nbrs _ _
        (actualAdjacentOfFaceLinkAdjacent hadj))

/-! ## 2. Finite incompatibility walks -/

/-- A finite canonical incompatibility walk with explicit contact witnesses.
The first and last numerical faces are indexed in the type. -/
inductive CanonicalIncompatibilityWalk (n : Nat) :
    Nat → Nat → List (List Nat) → Type
  | single {polymer : List Nat} {start finish : Nat}
      (hpolymer : polymer ∈ canonicalSurfacePolymers n)
      (hstart : start ∈ polymer) (hfinish : finish ∈ polymer) :
      CanonicalIncompatibilityWalk n start finish [polymer]
  | cons {polymer next : List Nat} {rest : List (List Nat)}
      {start leftContact rightContact finish : Nat}
      (hpolymer : polymer ∈ canonicalSurfacePolymers n)
      (hstart : start ∈ polymer)
      (hleftContact : leftContact ∈ polymer)
      (hrightContact : rightContact ∈ next)
      (hcontact : leftContact = rightContact ∨
        faceLinkAdjacentB n leftContact rightContact = true)
      (tail : CanonicalIncompatibilityWalk n rightContact finish
        (next :: rest)) :
      CanonicalIncompatibilityWalk n start finish
        (polymer :: next :: rest)

/-- Every displayed walk edge is genuinely incompatible for the corrected
canonical test. -/
theorem walk_cons_head_incompatible
    {n : Nat} {polymer next : List Nat} {rest : List (List Nat)}
    {start leftContact rightContact finish : Nat}
    (_hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (_hstart : start ∈ polymer)
    (hleftContact : leftContact ∈ polymer)
    (hrightContact : rightContact ∈ next)
    (hcontact : leftContact = rightContact ∨
      faceLinkAdjacentB n leftContact rightContact = true)
    (_tail : CanonicalIncompatibilityWalk n rightContact finish
      (next :: rest)) :
    canonicalPolymerCompatibleB n polymer next = false :=
  canonicalPolymerCompatibleB_false_of_contact
    hleftContact hrightContact hcontact

/-! ## 3. Total-size payment for geometric separation -/

/-- The total number of plaquettes in an incompatibility walk pays its full
endpoint separation. -/
theorem canonicalIncompatibilityWalk_faceCount_floor
    {n start finish : Nat} {family : List (List Nat)}
    (walk : CanonicalIncompatibilityWalk n start finish family) :
    linfDist (boxPlaquetteAt n start) (boxPlaquetteAt n finish) + 1 ≤
      familyFaceCount family := by
  induction walk with
  | @single polymer start finish hpolymer hstart hfinish =>
      change linfDist (boxPlaquetteAt n start)
          (boxPlaquetteAt n finish) + 1 ≤ polymer.length
      exact canonicalSurfacePolymer_linf_size_floor
        hpolymer hstart
        (List.mem_map.mpr ⟨finish, hfinish, rfl⟩)
        (Nat.le_refl _)
  | @cons polymer next rest start leftContact rightContact finish
      hpolymer hstart hleftContact hrightContact hcontact tail ih =>
      change linfDist (boxPlaquetteAt n start)
          (boxPlaquetteAt n finish) + 1 ≤
        polymer.length + familyFaceCount (next :: rest)
      have hhead :
          linfDist (boxPlaquetteAt n start)
              (boxPlaquetteAt n leftContact) + 1 ≤ polymer.length :=
        canonicalSurfacePolymer_linf_size_floor
          hpolymer hstart
          (List.mem_map.mpr ⟨leftContact, hleftContact, rfl⟩)
          (Nat.le_refl _)
      have hedge := incompatible_contact_linfDist_le_one hcontact
      have htriFirst :
          linfDist (boxPlaquetteAt n start)
              (boxPlaquetteAt n rightContact) ≤
            linfDist (boxPlaquetteAt n start)
                (boxPlaquetteAt n leftContact) +
              linfDist (boxPlaquetteAt n leftContact)
                (boxPlaquetteAt n rightContact) := by
        have h := z4SepLinf.dist_triangle
          (boxPlaquetteAt n start)
          (boxPlaquetteAt n leftContact)
          (boxPlaquetteAt n rightContact)
        exact h
      have htriSecond :
          linfDist (boxPlaquetteAt n start)
              (boxPlaquetteAt n finish) ≤
            linfDist (boxPlaquetteAt n start)
                (boxPlaquetteAt n rightContact) +
              linfDist (boxPlaquetteAt n rightContact)
                (boxPlaquetteAt n finish) := by
        have h := z4SepLinf.dist_triangle
          (boxPlaquetteAt n start)
          (boxPlaquetteAt n rightContact)
          (boxPlaquetteAt n finish)
        exact h
      omega

/-- If a walk begins in an inner box and ends outside its distance-expanded
box, then its total plaquette count is at least `distance + 2`. -/
theorem canonicalIncompatibilityWalk_outside_box_faceCount_floor
    {n start finish inner distance : Nat}
    {family : List (List Nat)}
    (walk : CanonicalIncompatibilityWalk n start finish family)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hout : outsideBoxB (inner + distance)
      (boxPlaquetteAt n finish) = true) :
    distance + 2 ≤ familyFaceCount family := by
  have hsep := outside_expanded_box_linf_floor hstartInner hout
  have hsize := canonicalIncompatibilityWalk_faceCount_floor walk
  omega

end YMGap.Continuum.Z4CanonicalIncompatibilityWalk

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalIncompatibilityWalk.canonicalPolymer_incompatible_contact
#print axioms YMGap.Continuum.Z4CanonicalIncompatibilityWalk.canonicalPolymerCompatibleB_false_of_contact
#print axioms YMGap.Continuum.Z4CanonicalIncompatibilityWalk.canonicalPolymerCompatibleB_symm
#print axioms YMGap.Continuum.Z4CanonicalIncompatibilityWalk.incompatible_contact_linfDist_le_one
#print axioms YMGap.Continuum.Z4CanonicalIncompatibilityWalk.walk_cons_head_incompatible
#print axioms YMGap.Continuum.Z4CanonicalIncompatibilityWalk.canonicalIncompatibilityWalk_faceCount_floor
#print axioms YMGap.Continuum.Z4CanonicalIncompatibilityWalk.canonicalIncompatibilityWalk_outside_box_faceCount_floor
