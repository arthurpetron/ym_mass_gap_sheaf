/-
# Four-edge minimum without a cycle-extraction oracle

In a finite simple bipartite edge list, nonempty support and even degree
at every endpoint force at least four edges. One and three edges violate
left degree parity. Two edges must have both endpoints equal, violating
simplicity. No graph search, infinite choice or analytic hypothesis.
-/

import YMGap.Continuum.ClusterCount4DProgress

namespace YMGap.Continuum.EvenBipartiteEdgeMinimum

set_option autoImplicit false

variable {A B : Type} [DecidableEq A] [DecidableEq B]

def leftDegree (a : A) : List (A × B) → Nat
  | [] => 0
  | e::es => (if e.1 = a then 1 else 0) + leftDegree a es

def rightDegree (b : B) : List (A × B) → Nat
  | [] => 0
  | e::es => (if e.2 = b then 1 else 0) + rightDegree b es

omit [DecidableEq B] in
private theorem three_not_even (e f g : A × B)
    (h : ∀ a, leftDegree a [e,f,g] % 2 = 0) : False := by
  have he := h e.1
  have hf := h f.1
  have hg := h g.1
  by_cases hef : f.1 = e.1
  · by_cases heg : g.1 = e.1
    · simp [leftDegree, hef, heg] at he
    · simp [leftDegree, hef, Ne.symm heg] at hg
  · by_cases heg : g.1 = e.1
    · simp [leftDegree, heg, Ne.symm hef] at hf
    · simp [leftDegree, hef, heg] at he

theorem minimum_four (edges : List (A × B)) (hn : edges.Nodup) (hne : edges ≠ [])
    (hl : ∀ a, leftDegree a edges % 2 = 0) (hr : ∀ b, rightDegree b edges % 2 = 0) :
    4 ≤ edges.length := by
  cases edges with
  | nil => exact False.elim (hne rfl)
  | cons e es =>
    cases es with
    | nil => have h := hl e.1; simp [leftDegree] at h
    | cons f fs =>
      cases fs with
      | nil =>
        have hleft := hl e.1
        have hright := hr e.2
        have hf : f.1 = e.1 := by
          by_cases h : f.1 = e.1
          · exact h
          · simp [leftDegree, h] at hleft
        have hg : f.2 = e.2 := by
          by_cases h : f.2 = e.2
          · exact h
          · simp [rightDegree, h] at hright
        have heq : f = e := Prod.ext hf hg
        subst f
        simp at hn
      | cons g gs =>
        cases gs with
        | nil => exact False.elim (three_not_even e f g hl)
        | cons _ _ => simp only [List.length_cons]; omega

end YMGap.Continuum.EvenBipartiteEdgeMinimum

#print axioms YMGap.Continuum.EvenBipartiteEdgeMinimum.leftDegree
#print axioms YMGap.Continuum.EvenBipartiteEdgeMinimum.rightDegree
#print axioms YMGap.Continuum.EvenBipartiteEdgeMinimum.minimum_four
