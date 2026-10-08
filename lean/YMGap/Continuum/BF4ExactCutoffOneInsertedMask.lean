/-
# Literal cutoff-one insertions and affine binary-surface parity

The insertion carrier is an occurrence list of actual face IDs.  Its XOR
charge records only parity: repeated insertions remain in the polynomial and
in its full block degree.  The original action mask and all original heat
weights remain unchanged.  Closure of action XOR charge is precisely
membership in the existing 128 closed masks; a nonclosed affine mask
annihilates the actual inserted 116-link Haar summand.

No active-carrier reduction or charged contraction value is asserted.
-/

import YMGap.Continuum.BF4ExactCutoffOneInsertedDegree

namespace YMGap.Continuum.BF4ExactCutoffOneInsertedMask

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneInsertedDegree
open YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex
open YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- Parity charge of an occurrence list, without deleting repeated factors. -/
def insertionMask : List Nat → Nat
  | [] => 0
  | id :: rest => Nat.xor (2 ^ id) (insertionMask rest)

/-- The actual corrected-slab faces, in the original occurrence order. -/
def insertedFaces (ids : List Nat) :
    List YMGap.Continuum.ClusterCount4DProgress.Z4Plaq :=
  ids.map (slabPlaquetteAt 1)

/-- Action mask XOR insertion charge; this is not a replacement action mask
inside the weighted integrand. -/
def affineMask (physical : EdgeLabelling) (ids : List Nat) : Nat :=
  Nat.xor (cutoffOneSlabMask physical) (insertionMask ids)

private theorem count_xor_right : ∀ width row left right,
    bitIntersectionCountBelow width row (Nat.xor left right) % 2 =
      (bitIntersectionCountBelow width row left +
        bitIntersectionCountBelow width row right) % 2
  | 0, _, _, _ => by simp [bitIntersectionCountBelow]
  | width + 1, row, left, right => by
      have ih := count_xor_right width row left right
      simp only [bitIntersectionCountBelow]
      have hbit : (Nat.xor left right).testBit width =
          (left.testBit width ^^ right.testBit width) := by
        change (left ^^^ right).testBit width = _
        exact Nat.testBit_xor left right width
      rw [hbit]
      generalize row.testBit width = rb
      generalize left.testBit width = lb
      generalize right.testBit width = qb
      cases rb <;> cases lb <;> cases qb <;> simp_all <;> omega

private theorem count_singleton : ∀ width row id,
    bitIntersectionCountBelow width row (2 ^ id) =
      if id < width then (if row.testBit id then 1 else 0) else 0
  | 0, _, _ => by
      simp only [bitIntersectionCountBelow, Nat.not_lt_zero, if_false]
  | width + 1, row, id => by
      simp only [bitIntersectionCountBelow, Nat.testBit_two_pow]
      cases hd : decide (id = width) with
      | false =>
          have hne : id ≠ width := of_decide_eq_false hd
          rw [count_singleton width row id]
          have hlt : id < width + 1 ↔ id < width := by
            constructor <;> intro h <;> omega
          simp only [Bool.and_false, Bool.false_eq_true, if_false,
            Nat.zero_add, hlt]
      | true =>
          have heq : id = width := of_decide_eq_true hd
          subst id
          rw [count_singleton width row width]
          simp only [Bool.and_true, Nat.lt_irrefl, Nat.lt_succ_self,
            if_false, if_true, Nat.add_zero]

private theorem count_zero : ∀ width row,
    bitIntersectionCountBelow width row 0 = 0
  | 0, _ => rfl
  | width + 1, row => by
      simp [bitIntersectionCountBelow, count_zero width row]

private theorem slab_count_xor (row left right : Nat) :
    slabMaskIntersectionCount row (Nat.xor left right) % 2 =
      (slabMaskIntersectionCount row left +
        slabMaskIntersectionCount row right) % 2 := by
  simp only [slabMaskIntersectionCount_eq_list,
    listIntersectionCountBelow_eq_recursive]
  exact count_xor_right 72 row left right

private theorem slab_count_singleton (row id : Nat) (hid : id < 72) :
    slabMaskIntersectionCount row (2 ^ id) =
      if row.testBit id then 1 else 0 := by
  simp only [slabMaskIntersectionCount_eq_list,
    listIntersectionCountBelow_eq_recursive]
  rw [count_singleton, if_pos hid]

theorem insertedFaces_physical (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id < 72) :
    ∀ face, face ∈ insertedFaces ids →
      face ∈ boundaryCompleteSlabPlaquettes 1 := by
  intro face hface
  unfold insertedFaces at hface
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hface
  apply slabPlaquetteAt_mem
  unfold slabPhysicalFaceEdges
  rw [correctedSlabPlaquettes_extent_one_length]
  exact List.mem_range.mpr (hids id hid)

theorem insertionMask_lt : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id < 72) → insertionMask ids < 2 ^ 72
  | [], _ => by simpa only [insertionMask] using Nat.two_pow_pos 72
  | id :: rest, hids => by
      have hid : id < 72 := hids id List.mem_cons_self
      have hpow : 2 ^ id < 2 ^ 72 := by
        have hstep : 2 ^ id < 2 ^ (id + 1) := by
          rw [Nat.pow_succ]
          have hpos := Nat.two_pow_pos id
          omega
        exact Nat.lt_of_lt_of_le hstep
          (Nat.pow_le_pow_right (by decide) (by omega))
      simp only [insertionMask, Nat.xor]
      apply Nat.bitwise_lt_two_pow
      · exact hpow
      · exact insertionMask_lt rest
          (fun other hother => hids other (List.mem_cons_of_mem id hother))

theorem affineMask_lt (physical : EdgeLabelling) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id < 72) :
    affineMask physical ids < 2 ^ 72 := by
  unfold affineMask Nat.xor
  exact Nat.bitwise_lt_two_pow (cutoffOneSlabMask_lt physical)
    (insertionMask_lt ids hids)

/-- Full insertion degree and XOR charge agree only modulo two. -/
theorem inserted_degree_parity (block : Nat) (hblock : block < 116) :
    ∀ ids : List Nat, (∀ id, id ∈ ids → id < 72) →
      slabFacesBlockDegree block (insertedFaces ids) % 2 =
        slabMaskIntersectionCount (slabEdgeFaceIncidenceMask block)
          (insertionMask ids) % 2
  | [], _ => by
      change 0 = slabMaskIntersectionCount
        (slabEdgeFaceIncidenceMask block) 0 % 2
      simp only [slabMaskIntersectionCount_eq_list,
        listIntersectionCountBelow_eq_recursive, count_zero]
  | id :: rest, hids => by
      have hid : id < 72 := hids id List.mem_cons_self
      have ih := inserted_degree_parity block hblock rest
        (fun other hother => hids other (List.mem_cons_of_mem id hother))
      simp only [insertedFaces, List.map_cons, slabFacesBlockDegree,
        insertionMask]
      rw [slabFaceBlockDegree_eq_incidenceBit block id hblock hid,
        slab_count_xor,
        slab_count_singleton (slabEdgeFaceIncidenceMask block) id hid]
      change (_ + slabFacesBlockDegree block (insertedFaces rest)) % 2 = _
      omega

/-- Parity of the actual original weighted polynomial's total degree is
exactly incidence of the affine mask, for every actual slab link. -/
theorem inserted_totalDegree_parity (physical : EdgeLabelling)
    (hlabel : ∀ id, physical id ≤ 1) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id < 72)
    (block : Nat) (hblock : block < 116) :
    (cutoffOneSlabSelectedBlockDegree block physical +
      slabFacesBlockDegree block (insertedFaces ids)) % 2 =
      slabMaskIntersectionCount (slabEdgeFaceIncidenceMask block)
        (affineMask physical ids) % 2 := by
  rw [cutoffOneSlabSelectedBlockDegree_eq_maskIntersectionCount
    block hblock physical hlabel]
  unfold affineMask
  rw [slab_count_xor]
  have hi := inserted_degree_parity block hblock ids hids
  omega

/-- This candidate criterion concerns parity only; it asserts neither a
nonzero Haar value nor the absence of repeated insertion factors. -/
theorem inserted_parity_allowed_iff_mem (physical : EdgeLabelling)
    (hlabel : ∀ id, physical id ≤ 1) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id < 72) :
    (∀ block, block < 116 →
      (cutoffOneSlabSelectedBlockDegree block physical +
        slabFacesBlockDegree block (insertedFaces ids)) % 2 = 0) ↔
      affineMask physical ids ∈ embeddedBinarySurfaceMasks := by
  rw [← slabSurfaceIsClosed_iff_mem_embeddedBinarySurfaceMasks
    (affineMask physical ids) (affineMask_lt physical ids hids)]
  unfold slabSurfaceIsClosed
  rw [correctedSlabLinks_extent_one_length]
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro block hb
    apply decide_eq_true
    rw [← inserted_totalDegree_parity physical hlabel ids hids block
      (List.mem_range.mp hb)]
    exact h block (List.mem_range.mp hb)
  · intro h block hb
    have heven := of_decide_eq_true
      (List.all_eq_true.mp h block (List.mem_range.mpr hb))
    rw [inserted_totalDegree_parity physical hlabel ids hids block hb]
    exact heven

private theorem listAll_false_witness {A : Type}
    (predicate : A → Bool) (items : List A)
    (hfalse : items.all predicate = false) :
    ∃ item, item ∈ items ∧ predicate item = false := by
  induction items with
  | nil =>
      change true = false at hfalse
      cases hfalse
  | cons head tail ih =>
      cases hh : predicate head with
      | false => exact ⟨head, List.mem_cons_self, hh⟩
      | true =>
          simp only [List.all_cons, hh, Bool.true_and] at hfalse
          exact Exists.elim (ih hfalse) fun item h =>
            ⟨item, List.mem_cons_of_mem head h.1, h.2⟩

/-- A nonclosed affine mask kills the literal inserted Haar summand, with
actual physicality and support produced rather than assumed as conclusions. -/
theorem exactCutoffOneInsertedHaar_eq_zero_of_affine_not_closed
    (w : Q') (physical : EdgeLabelling) (hlabel : ∀ id, physical id ≤ 1)
    (ids : List Nat) (hids : ∀ id, id ∈ ids → id < 72)
    (hclosed : slabSurfaceIsClosed (affineMask physical ids) = false) :
    quaternionHaar 116
      (exactCutoffOneInsertedIntegrand w physical (insertedFaces ids)) ≈ 0 := by
  unfold slabSurfaceIsClosed at hclosed
  rw [correctedSlabLinks_extent_one_length] at hclosed
  obtain ⟨block, hmem, hfalse⟩ := listAll_false_witness _ _ hclosed
  have hb : block < 116 := List.mem_range.mp hmem
  have hnot := of_decide_eq_false hfalse
  have hodd : slabMaskIntersectionCount (slabEdgeFaceIncidenceMask block)
      (affineMask physical ids) % 2 = 1 := by omega
  apply exactCutoffOneInsertedHaar_eq_zero_of_odd_degree
    w physical (insertedFaces ids) block hb hlabel
    (insertedFaces_physical ids hids)
  rw [inserted_totalDegree_parity physical hlabel ids hids block hb]
  exact hodd

#print axioms insertionMask
#print axioms insertedFaces
#print axioms affineMask
#print axioms insertedFaces_physical
#print axioms insertionMask_lt
#print axioms affineMask_lt
#print axioms inserted_degree_parity
#print axioms inserted_totalDegree_parity
#print axioms inserted_parity_allowed_iff_mem
#print axioms exactCutoffOneInsertedHaar_eq_zero_of_affine_not_closed
#print axioms count_xor_right
#print axioms count_singleton
#print axioms count_zero
#print axioms slab_count_xor
#print axioms slab_count_singleton
#print axioms slabFaceBlockDegree_eq_incidenceBit
#print axioms cutoffOneSlabSelectedBlockDegree_eq_maskIntersectionCount
#print axioms slabMaskIntersectionCount_eq_list
#print axioms listIntersectionCountBelow_eq_recursive

end YMGap.Continuum.BF4ExactCutoffOneInsertedMask
