/-
# Exact component mass and the no-isolates component bound

The existing finite component algorithm preserves every input occurrence:
the sum of component lengths is exactly the input length. If each vertex
has a distinct neighbor, every component has at least two vertices, with
an explicitly selected pair. Hence 2*(number of components) <= input length.
No enumeration of spanning forests or geometric weight estimate is assumed.
-/

import YMGap.Continuum.FiniteBoolGraphComponents

namespace YMGap.Continuum.FiniteBoolGraphComponentMass

set_option autoImplicit false

open YMGap.Continuum.FiniteBoolGraphComponents

def mass {A : Type} : List (List A) → Nat
  | [] => 0
  | c::cs => c.length+mass cs

theorem gather_keep_mass {A : Type} (adj : A → A → Bool) (x : A) :
    ∀ cs : List (List A),
    (gatherTouched adj x cs).length+mass (keepUntouched adj x cs)=mass cs+1
  | [] => rfl
  | c::cs => by
    have ih := gather_keep_mass adj x cs
    by_cases ht : touchesB adj x c=true <;>
      simp only [gatherTouched,keepUntouched,ht,Bool.false_eq_true,↓reduceIte,List.length_append,mass] <;> omega

theorem graph_mass {A : Type} (adj : A → A → Bool) : ∀ vertices : List A,
    mass (graphComponents adj vertices)=vertices.length
  | [] => rfl
  | x::xs => by
    change (gatherTouched adj x (graphComponents adj xs)).length+
      mass (keepUntouched adj x (graphComponents adj xs))=xs.length+1
    rw [gather_keep_mass,graph_mass adj xs]

theorem component_closed_under_edge {A : Type} [DecidableEq A]
    (adj : A → A → Bool) (hsym : SymmetricAdj adj) (vertices : List A)
    (component : List A) (hc : component ∈ graphComponents adj vertices)
    (x y : A) (hx : x ∈ component) (hy : y ∈ vertices) (he : adj x y=true) : y ∈ component := by
  obtain ⟨other,ho,hyother⟩ := (graphComponents_covers adj vertices y).mp hy
  by_cases hh : component=other
  · exact hh ▸ hyother
  · have hf := graphComponents_distinctSeparated adj hsym vertices component hc other ho hh x hx y hyother
    rw [he] at hf
    contradiction

def componentPair {A : Type} [DecidableEq A]
    (adj : A → A → Bool) (hsym : SymmetricAdj adj) (vertices : List A)
    (neighbor : ∀ x, x ∈ vertices → Σ' y : A, y ∈ vertices ∧ y ≠ x ∧ adj x y=true)
    (component : List A) (hc : component ∈ graphComponents adj vertices) :
    Σ' x : A, Σ' y : A, x ∈ component ∧ y ∈ component ∧ y ≠ x := by
  let root := graphComponents_allNonempty adj vertices component hc
  have hr := (graphComponents_covers adj vertices root.1).mpr ⟨component,hc,root.2⟩
  let next := neighbor root.1 hr
  exact ⟨root.1,next.1,root.2,
    component_closed_under_edge adj hsym vertices component hc root.1 next.1 root.2 next.2.1 next.2.2.2,
    next.2.2.1⟩

theorem component_minimum_two {A : Type} [DecidableEq A]
    (adj : A → A → Bool) (hsym : SymmetricAdj adj) (vertices : List A)
    (neighbor : ∀ x, x ∈ vertices → Σ' y : A, y ∈ vertices ∧ y ≠ x ∧ adj x y=true)
    (component : List A) (hc : component ∈ graphComponents adj vertices) : 2 ≤ component.length := by
  let pair := componentPair adj hsym vertices neighbor component hc
  have hx := pair.2.2.1
  have hy := pair.2.2.2.1
  have hne := pair.2.2.2.2
  cases component with
  | nil => exact False.elim (List.not_mem_nil hx)
  | cons a rest =>
    cases rest with
    | nil => exact False.elim (hne ((List.mem_singleton.mp hy).trans (List.mem_singleton.mp hx).symm))
    | cons b tail => simp only [List.length_cons]; omega

theorem twice_length_le_mass {A : Type} : ∀ cs : List (List A),
    (∀ c, c ∈ cs → 2 ≤ c.length) → 2*cs.length ≤ mass cs
  | [], _ => Nat.le_refl 0
  | c::cs, h => by
    have hc := h c List.mem_cons_self
    have ht := twice_length_le_mass cs (fun d hd => h d (List.mem_cons_of_mem c hd))
    simp only [List.length_cons,mass]
    omega

theorem twice_component_count_le {A : Type} [DecidableEq A]
    (adj : A → A → Bool) (hsym : SymmetricAdj adj) (vertices : List A)
    (neighbor : ∀ x, x ∈ vertices → Σ' y : A, y ∈ vertices ∧ y ≠ x ∧ adj x y=true) :
    2*(graphComponents adj vertices).length ≤ vertices.length := by
  have h := twice_length_le_mass (graphComponents adj vertices)
    (component_minimum_two adj hsym vertices neighbor)
  rw [graph_mass] at h
  exact h

end YMGap.Continuum.FiniteBoolGraphComponentMass

#print axioms YMGap.Continuum.FiniteBoolGraphComponentMass.mass
#print axioms YMGap.Continuum.FiniteBoolGraphComponentMass.gather_keep_mass
#print axioms YMGap.Continuum.FiniteBoolGraphComponentMass.graph_mass
#print axioms YMGap.Continuum.FiniteBoolGraphComponentMass.component_closed_under_edge
#print axioms YMGap.Continuum.FiniteBoolGraphComponentMass.componentPair
#print axioms YMGap.Continuum.FiniteBoolGraphComponentMass.component_minimum_two
#print axioms YMGap.Continuum.FiniteBoolGraphComponentMass.twice_length_le_mass
#print axioms YMGap.Continuum.FiniteBoolGraphComponentMass.twice_component_count_le
