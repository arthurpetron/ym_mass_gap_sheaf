/-
# Arbitrary named Boolean words and positional assignments

The canonical named/list bridge uses the consecutive word `List.range depth`.
Face-by-face Fubini for the elementary cube first produces a positional list
whose entries instead follow the flattened face-major tag word.  This leaf
supplies the complementary representation theorem for an arbitrary finite
word of names.

The construction is wholly post-Haar and additive.  It recurses on the tag
word and the already symbolic Boolean sum; it never constructs an assignment
carrier or unfolds a concrete depth-twenty-four tree.  Repeated names remain
valid; because the head update is applied outside the recursive tail, the
leftmost occurrence of a repeated name wins, exactly as in the named sum.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolSum

namespace YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolWord

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolSum

/-! ## 1. Pairing a name word with a bit word -/

/-- Pair an arbitrary finite word of names with a positional Boolean list.
Every name is updated, using the corresponding bit when present and `false`
after the bit word is exhausted.  This totalized short-word convention is
irrelevant on the exact-length branches produced by `rationalComplexBoolSum`,
but makes the structural tag/position lemmas below valid for every opaque
list supplied to a congruence theorem. -/
def boolTagWordEnvironment : List Nat → List Bool → Nat → Bool
  | [], _, _ => false
  | tag :: tags, [], query =>
      boolTagUpdate
        (boolTagWordEnvironment tags []) tag false query
  | tag :: tags, bit :: tail, query =>
      boolTagUpdate
        (boolTagWordEnvironment tags tail) tag bit query

theorem boolTagWordEnvironment_nil (assignment : List Bool) :
    boolTagWordEnvironment [] assignment = (fun _ => false) := by
  rfl

/-- Peeling one positional bit is exactly the corresponding named update. -/
theorem boolTagWordEnvironment_cons
    (tag : Nat) (tags : List Nat) (bit : Bool) (tail : List Bool) :
    boolTagWordEnvironment (tag :: tags) (bit :: tail) =
      boolTagUpdate (boolTagWordEnvironment tags tail) tag bit := by
  rfl

/-- The leading name reads the leading bit, with the same `false` default as
`List.getD` when the positional word is short. -/
theorem boolTagWordEnvironment_cons_self
    (tag : Nat) (tags : List Nat) (assignment : List Bool) :
    boolTagWordEnvironment (tag :: tags) assignment tag =
      assignment.getD 0 false := by
  cases assignment with
  | nil =>
      exact boolTagUpdate_self
        (boolTagWordEnvironment tags []) tag false
  | cons bit tail =>
      exact boolTagUpdate_self
        (boolTagWordEnvironment tags tail) tag bit

/-- A query absent from a leading name word ignores all of its updates and
is read from the suffix paired with the correspondingly dropped bit word. -/
theorem boolTagWordEnvironment_append_of_not_mem :
    ∀ (leading suffix : List Nat) (assignment : List Bool) (query : Nat),
      query ∉ leading →
      boolTagWordEnvironment (leading ++ suffix) assignment query =
        boolTagWordEnvironment suffix
          (assignment.drop leading.length) query
  | [], suffix, assignment, query, _ => by
      rfl
  | head :: leading, suffix, assignment, query, hnot => by
      have hhead : query ≠ head := by
        intro heq
        subst query
        exact hnot List.mem_cons_self
      have htail : query ∉ leading := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      cases assignment with
      | nil =>
          rw [List.cons_append]
          simp only [boolTagWordEnvironment]
          rw [boolTagUpdate_of_ne _ head query false hhead]
          simpa only [List.length_cons, List.drop_nil] using
            (boolTagWordEnvironment_append_of_not_mem
              leading suffix [] query htail)
      | cons bit tail =>
          rw [List.cons_append]
          simp only [boolTagWordEnvironment]
          rw [boolTagUpdate_of_ne _ head query bit hhead]
          simpa only [List.length_cons, List.drop_succ_cons] using
            (boolTagWordEnvironment_append_of_not_mem
              leading suffix tail query htail)

private theorem getD_drop_zero
    (assignment : List Bool) (offset : Nat) (fallback : Bool) :
    (assignment.drop offset).getD 0 fallback =
      assignment.getD offset fallback := by
  induction offset generalizing assignment with
  | zero => rfl
  | succ offset ih =>
      cases assignment with
      | nil => rfl
      | cons bit tail =>
          simpa only [List.drop_succ_cons, List.getD_cons_succ] using
            ih tail

/-- A duplicate-free prefix gives the exact positional value of the next
named coordinate.  No length hypothesis on the bit word is needed. -/
theorem boolTagWordEnvironment_append_lookup
    (leading suffix : List Nat) (assignment : List Bool) (tag : Nat)
    (hnot : tag ∉ leading) :
    boolTagWordEnvironment (leading ++ tag :: suffix) assignment tag =
      assignment.getD leading.length false := by
  rw [boolTagWordEnvironment_append_of_not_mem
    leading (tag :: suffix) assignment tag hnot]
  exact Eq.trans
    (boolTagWordEnvironment_cons_self tag suffix
      (assignment.drop leading.length))
    (getD_drop_zero assignment leading.length false)

/-- Duplicate-freeness of the complete tag word supplies the freshness
hypothesis for positional lookup at any displayed split. -/
theorem boolTagWordEnvironment_append_lookup_of_nodup
    (leading suffix : List Nat) (assignment : List Bool) (tag : Nat)
    (hnodup : (leading ++ tag :: suffix).Nodup) :
    boolTagWordEnvironment (leading ++ tag :: suffix) assignment tag =
      assignment.getD leading.length false :=
  boolTagWordEnvironment_append_lookup
    leading suffix assignment tag (by
      intro hmem
      exact (List.nodup_append.mp hnodup).2.2
        tag hmem tag List.mem_cons_self rfl)

/-! ## 2. Structural named/positional equivalence -/

/-- **Arbitrary tag-word bridge.**  A named Boolean sum agrees with the
ordinary positional Boolean-list sum whose entries are paired with the same
tag word.  The theorem is structural in `tags`; it is safe to specialize to
a length-twenty-four word because no concrete Boolean tree is reduced. -/
theorem rationalComplexNamedBoolSum_tagWord :
    ∀ (tags : List Nat)
      (family : (Nat → Bool) → RationalComplex),
      RationalComplexEqv
        (rationalComplexNamedBoolSum tags family)
        (rationalComplexBoolSum tags.length (fun assignment =>
          family (boolTagWordEnvironment tags assignment)))
  | [], family => by
      simp only [rationalComplexNamedBoolSum, List.length_nil,
        rationalComplexBoolSum, boolTagWordEnvironment]
      exact rationalComplexEqv_refl _
  | tag :: tags, family => by
      simp only [rationalComplexNamedBoolSum, List.length_cons,
        rationalComplexBoolSum, rationalComplexBoolBind]
      exact rationalComplexAdd_congr
        (rationalComplexEqv_trans
          (rationalComplexNamedBoolSum_tagWord tags (fun environment =>
            family (boolTagUpdate environment tag false)))
          (rationalComplexBoolSum_congr tags.length (fun assignment => by
            rw [boolTagWordEnvironment_cons]
            exact rationalComplexEqv_refl _)))
        (rationalComplexEqv_trans
          (rationalComplexNamedBoolSum_tagWord tags (fun environment =>
            family (boolTagUpdate environment tag true)))
          (rationalComplexBoolSum_congr tags.length (fun assignment => by
            rw [boolTagWordEnvironment_cons]
            exact rationalComplexEqv_refl _)))

#print axioms boolTagWordEnvironment_nil
#print axioms boolTagWordEnvironment_cons
#print axioms boolTagWordEnvironment_cons_self
#print axioms boolTagWordEnvironment_append_of_not_mem
#print axioms boolTagWordEnvironment_append_lookup
#print axioms boolTagWordEnvironment_append_lookup_of_nodup
#print axioms rationalComplexNamedBoolSum_tagWord

end YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolWord
