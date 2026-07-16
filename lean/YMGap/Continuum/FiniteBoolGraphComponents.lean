/-
# Constructive connected components of a finite Boolean graph

This module supplies the finite combinatorial engine needed by the corrected
Z4 surface gas.  Vertices are processed once.  A newly processed vertex merges
every existing component that it touches and leaves all untouched components
alone.  Thus a vertex that bridges several previously separate pieces performs
the union operation required by genuine connected components.

The construction is list-recursive and constructive.  It records internal
chains in `Type`, not merely propositional reachability, and proves coverage,
internal connectivity, pairwise separation, pairwise disjointness, and
duplicate-freedom for duplicate-free input lists.
-/

import YMGap.Continuum.Z4LinkSeparatedFamilyFactorization

namespace YMGap.Continuum.FiniteBoolGraphComponents

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-! ## 1. Graph predicates and Type-level internal chains -/

def SymmetricAdj {α : Type} (adj : α → α → Bool) : Prop :=
  ∀ a b, adj a b = adj b a

def SupportsSeparated {α : Type} (adj : α → α → Bool)
    (left right : List α) : Prop :=
  ∀ a, a ∈ left → ∀ b, b ∈ right → adj a b = false

def SupportsDisjoint {α : Type} (left right : List α) : Prop :=
  ∀ a, a ∈ left → a ∉ right

inductive ChainIn {α : Type} (adj : α → α → Bool) (support : List α) :
    α → α → Type
  | refl (a : α) : ChainIn adj support a a
  | step {a b c : α}
      (hab : adj a b = true) (hb : b ∈ support)
      (rest : ChainIn adj support b c) : ChainIn adj support a c

namespace ChainIn

def trans {α : Type} {adj : α → α → Bool} {support : List α} :
    {a b c : α} → ChainIn adj support a b → ChainIn adj support b c →
      ChainIn adj support a c
  | _, _, _, ChainIn.refl _, right => right
  | _, _, _, ChainIn.step hab hb rest, right =>
      ChainIn.step hab hb (trans rest right)

def mono {α : Type} {adj : α → α → Bool}
    {small large : List α}
    (hsub : ∀ x, x ∈ small → x ∈ large) :
    {a b : α} → ChainIn adj small a b → ChainIn adj large a b
  | _, _, ChainIn.refl a => ChainIn.refl a
  | _, _, ChainIn.step hab hb rest =>
      ChainIn.step hab (hsub _ hb) (mono hsub rest)

end ChainIn

def InternallyConnected {α : Type} (adj : α → α → Bool)
    (support : List α) : Type :=
  ∀ a b, a ∈ support → b ∈ support → ChainIn adj support a b

def AllConnected {α : Type} (adj : α → α → Bool)
    (components : List (List α)) : Type :=
  ∀ component, component ∈ components → InternallyConnected adj component

def AllNonempty {α : Type} (components : List (List α)) : Type :=
  ∀ component, component ∈ components → Σ' point : α, point ∈ component

def DistinctSeparated {α : Type} (adj : α → α → Bool)
    (components : List (List α)) : Prop :=
  ∀ left, left ∈ components → ∀ right, right ∈ components →
    left ≠ right → SupportsSeparated adj left right

def DistinctDisjoint {α : Type} (components : List (List α)) : Prop :=
  ∀ left, left ∈ components → ∀ right, right ∈ components →
    left ≠ right → SupportsDisjoint left right

def Covers {α : Type} (vertices : List α)
    (components : List (List α)) : Prop :=
  ∀ vertex, vertex ∈ vertices ↔
    ∃ component, component ∈ components ∧ vertex ∈ component

/-! ## 2. Touching, gathering, and retaining -/

def touchesB {α : Type} (adj : α → α → Bool) (vertex : α) :
    List α → Bool
  | [] => false
  | head :: tail => adj vertex head || touchesB adj vertex tail

def touchWitness {α : Type} (adj : α → α → Bool) (vertex : α) :
    ∀ support : List α, touchesB adj vertex support = true →
      Σ' point : α, (point ∈ support) ×' (adj vertex point = true)
  | [], h => by cases h
  | head :: tail, h => by
      cases hhead : adj vertex head with
      | false =>
          have htail : touchesB adj vertex tail = true := by
            simpa [touchesB, hhead] using h
          obtain ⟨point, hmem, hadj⟩ :=
            touchWitness adj vertex tail htail
          exact ⟨point, List.mem_cons_of_mem head hmem, hadj⟩
      | true =>
          exact ⟨head, List.mem_cons_self, hhead⟩

theorem adj_false_of_touchesB_false {α : Type}
    (adj : α → α → Bool) (vertex : α) :
    ∀ {support : List α}, touchesB adj vertex support = false →
      ∀ point, point ∈ support → adj vertex point = false
  | [], _, point, hmem => absurd hmem List.not_mem_nil
  | head :: tail, htouch, point, hmem => by
      have hhead : adj vertex head = false := by
        cases hh : adj vertex head <;> simp [touchesB, hh] at htouch ⊢
      rcases List.mem_cons.mp hmem with rfl | htailmem
      · exact hhead
      · apply adj_false_of_touchesB_false adj vertex
        · simpa [touchesB, hhead] using htouch
        · exact htailmem

def gatherTouched {α : Type} (adj : α → α → Bool) (vertex : α) :
    List (List α) → List α
  | [] => [vertex]
  | component :: rest =>
      if touchesB adj vertex component = true then
        component ++ gatherTouched adj vertex rest
      else
        gatherTouched adj vertex rest

def keepUntouched {α : Type} (adj : α → α → Bool) (vertex : α) :
    List (List α) → List (List α)
  | [] => []
  | component :: rest =>
      if touchesB adj vertex component = true then
        keepUntouched adj vertex rest
      else
        component :: keepUntouched adj vertex rest

def insertComponent {α : Type} (adj : α → α → Bool) (vertex : α)
    (components : List (List α)) : List (List α) :=
  gatherTouched adj vertex components :: keepUntouched adj vertex components

theorem vertex_mem_gatherTouched {α : Type} (adj : α → α → Bool)
    (vertex : α) : ∀ components,
    vertex ∈ gatherTouched adj vertex components
  | [] => List.mem_cons_self
  | component :: rest => by
      by_cases htouch : touchesB adj vertex component = true
      · simp only [gatherTouched, htouch, if_true]
        exact List.mem_append_right _ (vertex_mem_gatherTouched adj vertex rest)
      · simp only [gatherTouched, htouch, if_false]
        exact vertex_mem_gatherTouched adj vertex rest

theorem mem_gatherTouched_of_touched {α : Type}
    (adj : α → α → Bool) (vertex : α) :
    ∀ {components : List (List α)} {component : List α},
      component ∈ components → touchesB adj vertex component = true →
      ∀ {point}, point ∈ component →
        point ∈ gatherTouched adj vertex components
  | [], _, hmem, _, _, _ => absurd hmem List.not_mem_nil
  | head :: rest, component, hmem, htouch, point, hpoint => by
      rcases List.mem_cons.mp hmem with hhead | hrest
      · subst component
        simp only [gatherTouched, htouch, if_true]
        exact List.mem_append_left _ hpoint
      · by_cases hheadTouch : touchesB adj vertex head = true
        · simp only [gatherTouched, hheadTouch, if_true]
          exact List.mem_append_right _
            (mem_gatherTouched_of_touched adj vertex hrest htouch hpoint)
        · simp only [gatherTouched, hheadTouch, if_false]
          exact mem_gatherTouched_of_touched adj vertex hrest htouch hpoint

theorem mem_keepUntouched_of_untouched {α : Type}
    (adj : α → α → Bool) (vertex : α) :
    ∀ {components : List (List α)} {component : List α},
      component ∈ components → touchesB adj vertex component = false →
      component ∈ keepUntouched adj vertex components
  | [], _, hmem, _ => absurd hmem List.not_mem_nil
  | head :: rest, component, hmem, htouch => by
      rcases List.mem_cons.mp hmem with hhead | hrest
      · subst component
        simp only [keepUntouched, htouch, Bool.false_eq_true, if_false]
        exact List.mem_cons_self
      · by_cases hheadTouch : touchesB adj vertex head = true
        · simp only [keepUntouched, hheadTouch, if_true]
          exact mem_keepUntouched_of_untouched adj vertex hrest htouch
        · simp only [keepUntouched, hheadTouch, if_false]
          exact List.mem_cons_of_mem head
            (mem_keepUntouched_of_untouched adj vertex hrest htouch)

theorem mem_keepUntouched_original {α : Type}
    (adj : α → α → Bool) (vertex : α) :
    ∀ {components : List (List α)} {component : List α},
      component ∈ keepUntouched adj vertex components →
      component ∈ components
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: rest, component, hmem => by
      by_cases hheadTouch : touchesB adj vertex head = true
      · simp only [keepUntouched, hheadTouch, if_true] at hmem
        exact List.mem_cons_of_mem head
          (mem_keepUntouched_original adj vertex hmem)
      · simp only [keepUntouched, hheadTouch, if_false] at hmem
        rcases List.mem_cons.mp hmem with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem head
            (mem_keepUntouched_original adj vertex h)

theorem touchesB_false_of_mem_keepUntouched {α : Type}
    (adj : α → α → Bool) (vertex : α) :
    ∀ {components : List (List α)} {component : List α},
      component ∈ keepUntouched adj vertex components →
      touchesB adj vertex component = false
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: rest, component, hmem => by
      by_cases hheadTouch : touchesB adj vertex head = true
      · simp only [keepUntouched, hheadTouch, if_true] at hmem
        exact touchesB_false_of_mem_keepUntouched adj vertex hmem
      · simp only [keepUntouched, hheadTouch, if_false] at hmem
        rcases List.mem_cons.mp hmem with h | h
        · subst component
          cases hb : touchesB adj vertex head
          · rfl
          · exact absurd hb hheadTouch
        · exact touchesB_false_of_mem_keepUntouched adj vertex h

def decodeGatherMember {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex point : α) :
    ∀ (components : List (List α)),
      point ∈ gatherTouched adj vertex components →
      (point = vertex) ⊕'
        (Σ' component : List α,
          (component ∈ components) ×'
            (touchesB adj vertex component = true) ×'
              (point ∈ component))
  | [], hmem => PSum.inl (List.mem_singleton.mp hmem)
  | head :: rest, hmem => by
      by_cases htouch : touchesB adj vertex head = true
      · simp only [gatherTouched, htouch, if_true] at hmem
        by_cases hpoint : point ∈ head
        · exact PSum.inr ⟨head, List.mem_cons_self, htouch, hpoint⟩
        · have hrest : point ∈ gatherTouched adj vertex rest := by
            exact (List.mem_append.mp hmem).resolve_left hpoint
          match decodeGatherMember adj vertex point rest hrest with
          | PSum.inl heq => exact PSum.inl heq
          | PSum.inr ⟨component, hc, ht, hp⟩ =>
              exact PSum.inr
                ⟨component, List.mem_cons_of_mem head hc, ht, hp⟩
      · simp only [gatherTouched, htouch, if_false] at hmem
        match decodeGatherMember adj vertex point rest hmem with
        | PSum.inl heq => exact PSum.inl heq
        | PSum.inr ⟨component, hc, ht, hp⟩ =>
            exact PSum.inr
              ⟨component, List.mem_cons_of_mem head hc, ht, hp⟩

/-! ## 3. Connectivity of the merged component -/

def chainFromGatherHub {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (components : List (List α))
    (hall : AllConnected adj components) :
    ∀ point, point ∈ gatherTouched adj vertex components →
      ChainIn adj (gatherTouched adj vertex components) vertex point := by
  intro point hpoint
  match decodeGatherMember adj vertex point components hpoint with
  | PSum.inl heq =>
      rw [heq]
      exact ChainIn.refl vertex
  | PSum.inr ⟨component, hcomponent, htouch, hmem⟩ =>
      let witness := touchWitness adj vertex component htouch
      exact ChainIn.step witness.2.2
        (mem_gatherTouched_of_touched adj vertex hcomponent htouch
          witness.2.1)
        (ChainIn.mono
          (fun x hx => mem_gatherTouched_of_touched adj vertex
            hcomponent htouch hx)
          (hall component hcomponent witness.1 point witness.2.1 hmem))

def chainToGatherHub {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (components : List (List α))
    (hsym : SymmetricAdj adj)
    (hall : AllConnected adj components) :
    ∀ point, point ∈ gatherTouched adj vertex components →
      ChainIn adj (gatherTouched adj vertex components) point vertex := by
  intro point hpoint
  match decodeGatherMember adj vertex point components hpoint with
  | PSum.inl heq =>
      rw [heq]
      exact ChainIn.refl vertex
  | PSum.inr ⟨component, hcomponent, htouch, hmem⟩ =>
      let witness := touchWitness adj vertex component htouch
      have htoWitness :
          ChainIn adj (gatherTouched adj vertex components)
            point witness.1 :=
        ChainIn.mono
          (fun x hx => mem_gatherTouched_of_touched adj vertex
            hcomponent htouch hx)
          (hall component hcomponent point witness.1 hmem witness.2.1)
      have hback : adj witness.1 vertex = true := by
        rw [hsym witness.1 vertex]
        exact witness.2.2
      exact ChainIn.trans htoWitness
        (ChainIn.step hback (vertex_mem_gatherTouched adj vertex components)
          (ChainIn.refl vertex))

def gatherTouched_connected {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (components : List (List α))
    (hsym : SymmetricAdj adj)
    (hall : AllConnected adj components) :
    InternallyConnected adj (gatherTouched adj vertex components) :=
  fun left right hleft hright =>
    ChainIn.trans
      (chainToGatherHub adj vertex components hsym hall left hleft)
      (chainFromGatherHub adj vertex components hall right hright)

def insertComponent_allConnected {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (components : List (List α))
    (hsym : SymmetricAdj adj)
    (hall : AllConnected adj components) :
    AllConnected adj (insertComponent adj vertex components) := by
  intro component hcomponent
  by_cases heq : component = gatherTouched adj vertex components
  · rw [heq]
    exact gatherTouched_connected adj vertex components hsym hall
  · have hkeep : component ∈ keepUntouched adj vertex components := by
      unfold insertComponent at hcomponent
      rcases List.mem_cons.mp hcomponent with h | h
      · exact absurd h heq
      · exact h
    exact hall component
      (mem_keepUntouched_original adj vertex hkeep)

def insertComponent_allNonempty {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (components : List (List α))
    (hall : AllNonempty components) :
    AllNonempty (insertComponent adj vertex components) := by
  intro component hcomponent
  by_cases heq : component = gatherTouched adj vertex components
  · rw [heq]
    exact ⟨vertex, vertex_mem_gatherTouched adj vertex components⟩
  · have hkeep : component ∈ keepUntouched adj vertex components := by
      unfold insertComponent at hcomponent
      rcases List.mem_cons.mp hcomponent with h | h
      · exact absurd h heq
      · exact h
    exact hall component
      (mem_keepUntouched_original adj vertex hkeep)

/-! ## 4. Coverage, separation, disjointness, and duplicate freedom -/

theorem insertComponent_covers {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (vertices : List α) (components : List (List α))
    (hcover : Covers vertices components) :
    Covers (vertex :: vertices) (insertComponent adj vertex components) := by
  intro point
  constructor
  · intro hpoint
    rcases List.mem_cons.mp hpoint with heq | htail
    · subst point
      exact ⟨gatherTouched adj vertex components, List.mem_cons_self,
        vertex_mem_gatherTouched adj vertex components⟩
    · rcases (hcover point).1 htail with ⟨component, hc, hp⟩
      cases ht : touchesB adj vertex component with
      | false =>
          exact ⟨component,
            List.mem_cons_of_mem _
              (mem_keepUntouched_of_untouched adj vertex hc ht), hp⟩
      | true =>
          exact ⟨gatherTouched adj vertex components, List.mem_cons_self,
            mem_gatherTouched_of_touched adj vertex hc ht hp⟩
  · rintro ⟨component, hcomponent, hpoint⟩
    unfold insertComponent at hcomponent
    rcases List.mem_cons.mp hcomponent with hgather | hkeep
    · subst component
      match decodeGatherMember adj vertex point components hpoint with
      | PSum.inl heq => exact heq ▸ List.mem_cons_self
      | PSum.inr ⟨old, hold, _, hp⟩ =>
          exact List.mem_cons_of_mem vertex
            ((hcover point).2 ⟨old, hold, hp⟩)
    · have hold := mem_keepUntouched_original adj vertex hkeep
      exact List.mem_cons_of_mem vertex
        ((hcover point).2 ⟨component, hold, hpoint⟩)

theorem supportsSeparated_symm {α : Type} {adj : α → α → Bool}
    (hsym : SymmetricAdj adj) {left right : List α}
    (hsep : SupportsSeparated adj left right) :
    SupportsSeparated adj right left := by
  intro b hb a ha
  rw [hsym b a]
  exact hsep a ha b hb

theorem gatherTouched_separated_from_keep {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (components : List (List α))
    (hold : DistinctSeparated adj components) :
    ∀ {untouched}, untouched ∈ keepUntouched adj vertex components →
      SupportsSeparated adj (gatherTouched adj vertex components) untouched := by
  intro untouched huntouched point hpoint other hother
  have hfalse := touchesB_false_of_mem_keepUntouched
    adj vertex huntouched
  match decodeGatherMember adj vertex point components hpoint with
  | PSum.inl heq =>
      rw [heq]
      exact adj_false_of_touchesB_false adj vertex hfalse other hother
  | PSum.inr ⟨touched, htouched, htouch, hp⟩ =>
      have huntouchedOld := mem_keepUntouched_original adj vertex huntouched
      have hne : touched ≠ untouched := by
        intro heq
        subst untouched
        rw [htouch] at hfalse
        cases hfalse
      exact hold touched htouched untouched huntouchedOld hne point hp
        other hother

theorem insertComponent_distinctSeparated {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (components : List (List α))
    (hsym : SymmetricAdj adj)
    (hold : DistinctSeparated adj components) :
    DistinctSeparated adj (insertComponent adj vertex components) := by
  intro left hleft right hright hne
  by_cases hleftGather : left = gatherTouched adj vertex components
  · subst left
    have hrightKeep : right ∈ keepUntouched adj vertex components := by
      unfold insertComponent at hright
      rcases List.mem_cons.mp hright with h | h
      · exact absurd h.symm hne
      · exact h
    exact gatherTouched_separated_from_keep adj vertex components hold
      hrightKeep
  · have hleftKeep : left ∈ keepUntouched adj vertex components := by
      unfold insertComponent at hleft
      rcases List.mem_cons.mp hleft with h | h
      · exact absurd h hleftGather
      · exact h
    by_cases hrightGather : right = gatherTouched adj vertex components
    · subst right
      exact supportsSeparated_symm hsym
        (gatherTouched_separated_from_keep adj vertex components hold
          hleftKeep)
    · have hrightKeep : right ∈ keepUntouched adj vertex components := by
        unfold insertComponent at hright
        rcases List.mem_cons.mp hright with h | h
        · exact absurd h hrightGather
        · exact h
      exact hold left
        (mem_keepUntouched_original adj vertex hleftKeep)
        right (mem_keepUntouched_original adj vertex hrightKeep) hne

theorem supportsDisjoint_symm {α : Type} {left right : List α}
    (hdisjoint : SupportsDisjoint left right) :
    SupportsDisjoint right left := by
  intro point hright hleft
  exact hdisjoint point hleft hright

theorem gatherTouched_disjoint_from_keep {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (components : List (List α))
    (hold : DistinctDisjoint components)
    (hvertex : ∀ component, component ∈ components → vertex ∉ component) :
    ∀ {untouched}, untouched ∈ keepUntouched adj vertex components →
      SupportsDisjoint (gatherTouched adj vertex components) untouched := by
  intro untouched huntouched point hpoint
  match decodeGatherMember adj vertex point components hpoint with
  | PSum.inl heq =>
      rw [heq]
      exact hvertex untouched
        (mem_keepUntouched_original adj vertex huntouched)
  | PSum.inr ⟨touched, htouched, htouch, hp⟩ =>
      have huntouchedOld := mem_keepUntouched_original adj vertex huntouched
      have hfalse := touchesB_false_of_mem_keepUntouched
        adj vertex huntouched
      have hne : touched ≠ untouched := by
        intro heq
        subst untouched
        rw [htouch] at hfalse
        cases hfalse
      exact hold touched htouched untouched huntouchedOld hne point hp

theorem insertComponent_distinctDisjoint {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (components : List (List α))
    (hold : DistinctDisjoint components)
    (hvertex : ∀ component, component ∈ components → vertex ∉ component) :
    DistinctDisjoint (insertComponent adj vertex components) := by
  intro left hleft right hright hne
  by_cases hleftGather : left = gatherTouched adj vertex components
  · subst left
    have hrightKeep : right ∈ keepUntouched adj vertex components := by
      unfold insertComponent at hright
      rcases List.mem_cons.mp hright with h | h
      · exact absurd h.symm hne
      · exact h
    exact gatherTouched_disjoint_from_keep adj vertex components hold
      hvertex hrightKeep
  · have hleftKeep : left ∈ keepUntouched adj vertex components := by
      unfold insertComponent at hleft
      rcases List.mem_cons.mp hleft with h | h
      · exact absurd h hleftGather
      · exact h
    by_cases hrightGather : right = gatherTouched adj vertex components
    · subst right
      exact supportsDisjoint_symm
        (gatherTouched_disjoint_from_keep adj vertex components hold
          hvertex hleftKeep)
    · have hrightKeep : right ∈ keepUntouched adj vertex components := by
        unfold insertComponent at hright
        rcases List.mem_cons.mp hright with h | h
        · exact absurd h hrightGather
        · exact h
      exact hold left
        (mem_keepUntouched_original adj vertex hleftKeep)
        right (mem_keepUntouched_original adj vertex hrightKeep) hne

theorem keepUntouched_nodup {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α) :
    ∀ {components : List (List α)}, components.Nodup →
      (keepUntouched adj vertex components).Nodup
  | [], _ => List.nodup_nil
  | head :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases htouch : touchesB adj vertex head = true
      · simp only [keepUntouched, htouch, if_true]
        exact keepUntouched_nodup adj vertex hparts.2
      · simp only [keepUntouched, htouch, if_false]
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          exact hparts.1 (mem_keepUntouched_original adj vertex hmem)
        · exact keepUntouched_nodup adj vertex hparts.2

theorem insertComponent_nodup {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertex : α)
    (components : List (List α))
    (hnodup : components.Nodup)
    (hvertex : ∀ component, component ∈ components → vertex ∉ component) :
    (insertComponent adj vertex components).Nodup := by
  unfold insertComponent
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    have hold := mem_keepUntouched_original adj vertex hmem
    have hnot := hvertex _ hold
    exact hnot (vertex_mem_gatherTouched adj vertex components)
  · exact keepUntouched_nodup adj vertex hnodup

/-! ## 5. The component construction and its global invariants -/

def graphComponents {α : Type} (adj : α → α → Bool) :
    List α → List (List α)
  | [] => []
  | vertex :: rest =>
      insertComponent adj vertex (graphComponents adj rest)

theorem graphComponents_covers {α : Type} [DecidableEq α]
    (adj : α → α → Bool) : ∀ vertices,
    Covers vertices (graphComponents adj vertices)
  | [] => by
      intro vertex
      constructor
      · intro h
        exact absurd h List.not_mem_nil
      · rintro ⟨component, h, _⟩
        exact absurd h List.not_mem_nil
  | vertex :: rest =>
      insertComponent_covers adj vertex rest (graphComponents adj rest)
        (graphComponents_covers adj rest)

def graphComponents_allConnected {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (hsym : SymmetricAdj adj) :
    ∀ vertices, AllConnected adj (graphComponents adj vertices)
  | [] => fun component hmem => absurd hmem List.not_mem_nil
  | vertex :: rest =>
      insertComponent_allConnected adj vertex (graphComponents adj rest)
        hsym (graphComponents_allConnected adj hsym rest)

def graphComponents_allNonempty {α : Type} [DecidableEq α]
    (adj : α → α → Bool) :
    ∀ vertices, AllNonempty (graphComponents adj vertices)
  | [] => fun component hmem => absurd hmem List.not_mem_nil
  | vertex :: rest =>
      insertComponent_allNonempty adj vertex (graphComponents adj rest)
        (graphComponents_allNonempty adj rest)

theorem graphComponents_distinctSeparated {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (hsym : SymmetricAdj adj) :
    ∀ vertices, DistinctSeparated adj (graphComponents adj vertices)
  | [] => by
      intro left hleft
      exact absurd hleft List.not_mem_nil
  | vertex :: rest =>
      insertComponent_distinctSeparated adj vertex (graphComponents adj rest)
        hsym (graphComponents_distinctSeparated adj hsym rest)

theorem graphComponents_distinctDisjoint {α : Type} [DecidableEq α]
    (adj : α → α → Bool) : ∀ {vertices : List α}, vertices.Nodup →
    DistinctDisjoint (graphComponents adj vertices)
  | [], _ => by
      intro left hleft
      exact absurd hleft List.not_mem_nil
  | vertex :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      have hrestDisjoint := graphComponents_distinctDisjoint adj hparts.2
      have hvertex : ∀ component,
          component ∈ graphComponents adj rest → vertex ∉ component := by
        intro component hcomponent hmem
        exact hparts.1
          ((graphComponents_covers adj rest vertex).2
            ⟨component, hcomponent, hmem⟩)
      exact insertComponent_distinctDisjoint adj vertex
        (graphComponents adj rest) hrestDisjoint hvertex

theorem graphComponents_nodup {α : Type} [DecidableEq α]
    (adj : α → α → Bool) : ∀ {vertices : List α}, vertices.Nodup →
    (graphComponents adj vertices).Nodup
  | [], _ => List.nodup_nil
  | vertex :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      have hrestNodup := graphComponents_nodup adj hparts.2
      have hvertex : ∀ component,
          component ∈ graphComponents adj rest → vertex ∉ component := by
        intro component hcomponent hmem
        exact hparts.1
          ((graphComponents_covers adj rest vertex).2
            ⟨component, hcomponent, hmem⟩)
      exact insertComponent_nodup adj vertex (graphComponents adj rest)
        hrestNodup hvertex

end YMGap.Continuum.FiniteBoolGraphComponents

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteBoolGraphComponents.graphComponents_covers
#print axioms YMGap.Continuum.FiniteBoolGraphComponents.graphComponents_allConnected
#print axioms YMGap.Continuum.FiniteBoolGraphComponents.graphComponents_allNonempty
#print axioms YMGap.Continuum.FiniteBoolGraphComponents.graphComponents_distinctSeparated
#print axioms YMGap.Continuum.FiniteBoolGraphComponents.graphComponents_distinctDisjoint
#print axioms YMGap.Continuum.FiniteBoolGraphComponents.graphComponents_nodup
