/-
# Constructive loop erasure for finite Boolean walks

Warshall soundness returns a transitively nested walk whose syntax may repeat
vertices.  This module normalizes such a witness to cons form and erases loops
by decidable membership in the already constructed tail.  The resulting walk
has duplicate-free vertices and uses only edges of the original relation.
-/

import YMGap.Continuum.Z4CanonicalBipartitePath

namespace YMGap.Continuum.FiniteSimpleWalk

open YMGap.Continuum.Z4CanonicalBipartitePath

inductive CWalk {A : Type} (edge : A → A → Bool) : A → A → Type
  | single (vertex : A) : CWalk edge vertex vertex
  | cons {first middle last : A} :
      edge first middle = true →
        CWalk edge middle last → CWalk edge first last

namespace CWalk

variable {A : Type} {edge : A → A → Bool}

def vertices : {first last : A} → CWalk edge first last → List A
  | first, _, .single _ => [first]
  | first, _, .cons _ rest => first :: vertices rest

def append {first middle last : A} :
    CWalk edge first middle → CWalk edge middle last →
      CWalk edge first last
  | .single _, second => second
  | .cons hedge rest, second => .cons hedge (append rest second)

def ofDWalk {first last : A} :
    DWalk edge first last → CWalk edge first last
  | .refl _ => .single _
  | .edge hedge => .cons hedge (.single _)
  | .trans first second => append (ofDWalk first) (ofDWalk second)

def dropTo [DecidableEq A] : {first last : A} →
    (walk : CWalk edge first last) →
      (vertex : A) → vertex ∈ walk.vertices →
        CWalk edge vertex last
  | _, _, .single first, vertex, hvertex => by
      have heq : vertex = first := List.mem_singleton.mp hvertex
      subst vertex
      exact .single first
  | first, _, .cons hedge rest, vertex, hvertex => by
      by_cases heq : vertex = first
      · subst vertex
        exact .cons hedge rest
      · exact dropTo rest vertex
          ((List.mem_cons.mp hvertex).resolve_left heq)

theorem dropTo_nodup [DecidableEq A] :
    ∀ {first last : A} (walk : CWalk edge first last)
      (vertex : A) (hvertex : vertex ∈ walk.vertices),
      walk.vertices.Nodup →
        (dropTo walk vertex hvertex).vertices.Nodup
  | _, _, .single first, vertex, hvertex, _ => by
      have heq : vertex = first := List.mem_singleton.mp hvertex
      subst vertex
      simp [dropTo, vertices]
  | first, _, .cons hedge rest, vertex, hvertex, hnodup => by
      by_cases heq : vertex = first
      · subst vertex
        simpa [dropTo, vertices] using hnodup
      · have hrest : vertex ∈ rest.vertices :=
          (List.mem_cons.mp hvertex).resolve_left heq
        have htail := (List.nodup_cons.mp hnodup).2
        simpa [dropTo, heq] using
          dropTo_nodup rest vertex hrest htail

structure Simple (edge : A → A → Bool) (first last : A) : Type where
  walk : CWalk edge first last
  nodup : walk.vertices.Nodup

def eraseLoops [DecidableEq A] : {first last : A} →
    CWalk edge first last → Simple edge first last
  | _, _, .single first =>
      { walk := .single first
        nodup := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩ }
  | first, _, .cons hedge rest =>
      let tail := eraseLoops rest
      if hfirst : first ∈ tail.walk.vertices then
        { walk := dropTo tail.walk first hfirst
          nodup := dropTo_nodup tail.walk first hfirst tail.nodup }
      else
        { walk := .cons hedge tail.walk
          nodup := List.nodup_cons.mpr ⟨hfirst, tail.nodup⟩ }

theorem start_mem_vertices :
    ∀ {first last : A} (walk : CWalk edge first last),
      first ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ _ => List.mem_cons_self

theorem end_mem_vertices :
    ∀ {first last : A} (walk : CWalk edge first last),
      last ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (end_mem_vertices rest)

theorem all_vertices_of_start
    (property : A → Prop)
    (hedge : ∀ first second,
      edge first second = true → property first → property second) :
    ∀ {first last : A} (walk : CWalk edge first last),
      property first →
        ∀ vertex, vertex ∈ walk.vertices → property vertex
  | _, _, .single first, hfirst, vertex, hvertex => by
      rw [List.mem_singleton.mp hvertex]
      exact hfirst
  | _, _, .cons hstep rest, hfirst, vertex, hvertex => by
      rcases List.mem_cons.mp hvertex with heq | htail
      · rw [heq]
        exact hfirst
      · exact all_vertices_of_start property hedge rest
          (hedge _ _ hstep hfirst) vertex htail

end CWalk

def simpleWalkOfWarshall [DecidableEq A]
    (edge : A → A → Bool) (ambient : List A)
    (first last : A)
    (hreaches : warshall edge ambient first last = true) :
    CWalk.Simple edge first last :=
  CWalk.eraseLoops
    (CWalk.ofDWalk (warshallSound edge ambient first last hreaches))

/-! ## Duplicate-free weighted subset accounting over `Nat` -/

def listNatWeight (weight : A → Nat) : List A → Nat
  | [] => 0
  | item :: rest => weight item + listNatWeight weight rest

theorem listNatWeight_append (weight : A → Nat) :
    ∀ first second : List A,
      listNatWeight weight (first ++ second) =
        listNatWeight weight first + listNatWeight weight second
  | [], second => by
      change listNatWeight weight second = 0 + listNatWeight weight second
      omega
  | head :: rest, second => by
      change weight head + listNatWeight weight (rest ++ second) =
        (weight head + listNatWeight weight rest) +
          listNatWeight weight second
      rw [listNatWeight_append weight rest second]
      omega

theorem listNatWeight_map (map : A → B) (weight : B → Nat) :
    ∀ xs : List A,
      listNatWeight weight (xs.map map) =
        listNatWeight (fun item => weight (map item)) xs
  | [] => rfl
  | _ :: rest => by
      simp only [List.map, listNatWeight]
      rw [listNatWeight_map map weight rest]

theorem listNatWeight_erase_decompose [DecidableEq A]
    (weight : A → Nat) :
    ∀ (xs : List A) (item : A), item ∈ xs →
      listNatWeight weight xs =
        weight item + listNatWeight weight (xs.erase item)
  | [], _, hitem => by cases hitem
  | head :: tail, item, hitem => by
      by_cases heq : head = item
      · subst head
        rw [List.erase_cons_head]
        rfl
      · have htail : item ∈ tail :=
          (List.mem_cons.mp hitem).resolve_left
            (fun h => heq h.symm)
        rw [List.erase_cons_tail (a := item) (b := head)
          (by simpa [heq])]
        simp only [listNatWeight]
        rw [listNatWeight_erase_decompose weight tail item htail]
        omega

theorem mem_erase_of_mem_of_ne [DecidableEq A]
    {first removed : A} (hne : first ≠ removed) :
    ∀ {xs : List A}, first ∈ xs → first ∈ xs.erase removed
  | [], hmem => by cases hmem
  | head :: tail, hmem => by
      by_cases heq : head = removed
      · subst head
        rw [List.erase_cons_head]
        exact (List.mem_cons.mp hmem).resolve_left hne
      · rw [List.erase_cons_tail (by simpa [heq])]
        rcases List.mem_cons.mp hmem with hhead | htail
        · exact List.mem_cons.mpr (Or.inl hhead)
        · exact List.mem_cons.mpr
            (Or.inr (mem_erase_of_mem_of_ne hne htail))

/-- A duplicate-free weighted source included in a target list has no larger
total weight.  The target need not be duplicate-free. -/
theorem listNatWeight_le_of_nodup_mem [DecidableEq A]
    (weight : A → Nat) :
    ∀ (source target : List A), source.Nodup →
      (∀ item, item ∈ source → item ∈ target) →
        listNatWeight weight source ≤ listNatWeight weight target
  | [], _, _, _ => Nat.zero_le _
  | head :: tail, target, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      have hhead : head ∈ target := hmem head List.mem_cons_self
      have htail : listNatWeight weight tail ≤
          listNatWeight weight (target.erase head) := by
        apply listNatWeight_le_of_nodup_mem weight tail
          (target.erase head) hparts.2
        intro item hitem
        exact mem_erase_of_mem_of_ne
          (fun heq => by
            subst item
            exact hparts.1 hitem)
          (hmem item (List.mem_cons_of_mem head hitem))
      simp only [listNatWeight]
      rw [listNatWeight_erase_decompose weight target head hhead]
      omega

end YMGap.Continuum.FiniteSimpleWalk

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteSimpleWalk.CWalk.eraseLoops
#print axioms YMGap.Continuum.FiniteSimpleWalk.CWalk.all_vertices_of_start
#print axioms YMGap.Continuum.FiniteSimpleWalk.simpleWalkOfWarshall
#print axioms YMGap.Continuum.FiniteSimpleWalk.listNatWeight_le_of_nodup_mem
