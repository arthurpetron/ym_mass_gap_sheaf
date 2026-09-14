/-
# Four-edge minimum from absence of leaves, not parity

A nonempty simple bipartite edge list without degree-one vertices has
at least four edges. With at most three edges, absence of a left leaf
forces every left endpoint equal; the right side does the same. Two
edges then coincide. Odd degrees greater than one are permitted.
-/

import YMGap.Continuum.EvenBipartiteEdgeMinimum

namespace YMGap.Continuum.LeaflessBipartiteEdgeMinimum

set_option autoImplicit false

open YMGap.Continuum.EvenBipartiteEdgeMinimum

private theorem three_equal {A : Type} [DecidableEq A] (a b c : A)
    (h : ∀ x, (if a = x then 1 else 0) + (if b = x then 1 else 0) +
      (if c = x then 1 else 0) ≠ (1 : Nat)) : b = a ∧ c = a := by
  by_cases hb : b = a
  · by_cases hc : c = a
    · exact ⟨hb,hc⟩
    · have hx := h c
      simp only [hb, if_neg (Ne.symm hc), ↓reduceIte, Nat.zero_add] at hx
      exact False.elim (hx rfl)
  · by_cases hc : c = a
    · have hx := h b
      simp only [hc, if_neg (Ne.symm hb), ↓reduceIte, Nat.zero_add, Nat.add_zero] at hx
      exact False.elim (hx rfl)
    · have hx := h a
      simp only [if_neg hb, if_neg hc, ↓reduceIte, Nat.add_zero] at hx
      exact False.elim (hx rfl)

theorem minimum_four {A B : Type} [DecidableEq A] [DecidableEq B]
    (edges : List (A × B)) (hn : edges.Nodup) (hne : edges ≠ [])
    (hl : ∀ a, leftDegree a edges ≠ 1) (hr : ∀ b, rightDegree b edges ≠ 1) :
    4 ≤ edges.length := by
  cases edges with
  | nil => exact False.elim (hne rfl)
  | cons e es =>
    cases es with
    | nil => have h := hl e.1; simp [leftDegree] at h
    | cons f fs =>
      cases fs with
      | nil =>
        have hf : f.1 = e.1 := by
          by_cases h : f.1 = e.1
          · exact h
          · have hh := hl e.1; simp [leftDegree, h] at hh
        have hg : f.2 = e.2 := by
          by_cases h : f.2 = e.2
          · exact h
          · have hh := hr e.2; simp [rightDegree, h] at hh
        have heq : f = e := Prod.ext hf hg
        subst f
        simp at hn
      | cons g gs =>
        cases gs with
        | nil =>
          have hleft := three_equal e.1 f.1 g.1 (fun a => by
            simpa only [leftDegree, Nat.add_zero, Nat.add_assoc] using hl a)
          have hright := three_equal e.2 f.2 g.2 (fun b => by
            simpa only [rightDegree, Nat.add_zero, Nat.add_assoc] using hr b)
          have heq : f = e := Prod.ext hleft.1 hright.1
          subst f
          simp at hn
        | cons _ _ => simp only [List.length_cons]; omega

end YMGap.Continuum.LeaflessBipartiteEdgeMinimum

#print axioms YMGap.Continuum.LeaflessBipartiteEdgeMinimum.minimum_four
