/-
# Canonical rooted component of a finite Boolean graph

The finite component compiler already constructs all connected components of
a symmetric Boolean graph.  This module selects, without choice, the unique
component containing a supplied root and proves the properties needed for a
superselection sector: it contains the root, lies in the finite carrier, is
internally connected, and has no edge to its complement.

The selector is executable list recursion.  `eraseDups` makes the returned
carrier literally duplicate-free without changing its support.
-/

import YMGap.Continuum.FiniteBoolGraphComponents

namespace YMGap.Continuum.FiniteBoolGraphRootComponent

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.FiniteBoolGraphComponents

/-! ## 1. Choice-free selection of the first component containing a root -/

def firstContaining {α : Type} [DecidableEq α] (root : α) :
    List (List α) → List α
  | [] => []
  | component :: rest =>
      if root ∈ component then component else firstContaining root rest

theorem root_mem_firstContaining {α : Type} [DecidableEq α]
    (root : α) : ∀ {components : List (List α)},
    (∃ component, component ∈ components ∧ root ∈ component) →
      root ∈ firstContaining root components
  | [], hexists => by
      rcases hexists with ⟨component, hcomponent, _⟩
      exact False.elim (List.not_mem_nil hcomponent)
  | head :: tail, hexists => by
      by_cases hhead : root ∈ head
      · simp [firstContaining, hhead]
      · simp only [firstContaining, hhead, if_false]
        apply root_mem_firstContaining root
        rcases hexists with ⟨component, hcomponent, hroot⟩
        rcases List.mem_cons.mp hcomponent with heq | htail
        · subst component
          exact False.elim (hhead hroot)
        · exact ⟨component, htail, hroot⟩

theorem firstContaining_mem {α : Type} [DecidableEq α]
    (root : α) : ∀ {components : List (List α)},
    (∃ component, component ∈ components ∧ root ∈ component) →
      firstContaining root components ∈ components
  | [], hexists => by
      rcases hexists with ⟨component, hcomponent, _⟩
      exact False.elim (List.not_mem_nil hcomponent)
  | head :: tail, hexists => by
      by_cases hhead : root ∈ head
      · simp [firstContaining, hhead]
      · simp only [firstContaining, hhead, if_false]
        apply List.mem_cons_of_mem head
        apply firstContaining_mem root
        rcases hexists with ⟨component, hcomponent, hroot⟩
        rcases List.mem_cons.mp hcomponent with heq | htail
        · subst component
          exact False.elim (hhead hroot)
        · exact ⟨component, htail, hroot⟩

/-! ## 2. The canonical rooted support -/

def rootComponent {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertices : List α) (root : α) : List α :=
  (firstContaining root (graphComponents adj vertices)).eraseDups

private theorem filtered_eraseDups_nodup {α : Type}
    [BEq α] [LawfulBEq α] (items : List α) :
    ∀ predicate : α → Bool, (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr
          ⟨?_, ih (fun item => (!(item == head)) && predicate item)⟩
        intro hmem
        have hmem' : head ∈ tail.filter
            (fun item => (!(item == head)) && predicate item) :=
          List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hmem').2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih predicate

private theorem filter_true_local {α : Type} :
    ∀ items : List α, items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail =>
      congrArg (List.cons head) (filter_true_local tail)

private theorem eraseDups_nodup_local {α : Type}
    [BEq α] [LawfulBEq α] (items : List α) : items.eraseDups.Nodup := by
  have h := filtered_eraseDups_nodup items (fun _ => true)
  rw [filter_true_local] at h
  exact h

theorem rootComponent_nodup {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (vertices : List α) (root : α) :
    (rootComponent adj vertices root).Nodup :=
  eraseDups_nodup_local _

private theorem root_component_exists {α : Type} [DecidableEq α]
    (adj : α → α → Bool) {vertices : List α} {root : α}
    (hroot : root ∈ vertices) :
    ∃ component, component ∈ graphComponents adj vertices ∧
      root ∈ component :=
  (graphComponents_covers adj vertices root).1 hroot

theorem root_mem_rootComponent {α : Type} [DecidableEq α]
    (adj : α → α → Bool) {vertices : List α} {root : α}
    (hroot : root ∈ vertices) :
    root ∈ rootComponent adj vertices root := by
  apply List.mem_eraseDups.mpr
  exact root_mem_firstContaining root
    (root_component_exists adj hroot)

theorem rootComponent_subset {α : Type} [DecidableEq α]
    (adj : α → α → Bool) {vertices : List α} {root point : α}
    (hroot : root ∈ vertices)
    (hpoint : point ∈ rootComponent adj vertices root) :
    point ∈ vertices := by
  have hselected :
      firstContaining root (graphComponents adj vertices) ∈
        graphComponents adj vertices :=
    firstContaining_mem root (root_component_exists adj hroot)
  apply (graphComponents_covers adj vertices point).2
  exact ⟨firstContaining root (graphComponents adj vertices), hselected,
    List.mem_eraseDups.mp hpoint⟩

def rootComponent_connected {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (hsym : SymmetricAdj adj)
    {vertices : List α} {root : α} (hroot : root ∈ vertices) :
    InternallyConnected adj (rootComponent adj vertices root) := by
  intro left right hleft hright
  let selected := firstContaining root (graphComponents adj vertices)
  have hselected : selected ∈ graphComponents adj vertices :=
    firstContaining_mem root (root_component_exists adj hroot)
  have hchain : ChainIn adj selected left right :=
    graphComponents_allConnected adj hsym vertices
      selected hselected left right
      (List.mem_eraseDups.mp hleft) (List.mem_eraseDups.mp hright)
  exact ChainIn.mono
    (fun point hpoint => List.mem_eraseDups.mpr hpoint) hchain

/-! ## 3. Exact separation from the complement -/

theorem rootComponent_adj_false_of_not_mem
    {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (hsym : SymmetricAdj adj)
    {vertices : List α} {root source target : α}
    (hroot : root ∈ vertices)
    (hsource : source ∈ rootComponent adj vertices root)
    (htarget : target ∈ vertices)
    (houtside : target ∉ rootComponent adj vertices root) :
    adj source target = false := by
  let selected := firstContaining root (graphComponents adj vertices)
  have hselected : selected ∈ graphComponents adj vertices :=
    firstContaining_mem root (root_component_exists adj hroot)
  obtain ⟨targetComponent, htargetComponent, htargetIn⟩ :=
    (graphComponents_covers adj vertices target).1 htarget
  have hne : selected ≠ targetComponent := by
    intro heq
    apply houtside
    apply List.mem_eraseDups.mpr
    change target ∈ selected
    rw [heq]
    exact htargetIn
  exact graphComponents_distinctSeparated adj hsym vertices
    selected hselected targetComponent htargetComponent hne
    source (List.mem_eraseDups.mp hsource) target htargetIn

theorem rootComponent_closed_under_edge
    {α : Type} [DecidableEq α]
    (adj : α → α → Bool) (hsym : SymmetricAdj adj)
    {vertices : List α} {root source target : α}
    (hroot : root ∈ vertices)
    (hsource : source ∈ rootComponent adj vertices root)
    (htarget : target ∈ vertices)
    (hedge : adj source target = true) :
    target ∈ rootComponent adj vertices root := by
  by_cases hmem : target ∈ rootComponent adj vertices root
  · exact hmem
  · have hfalse := rootComponent_adj_false_of_not_mem
      adj hsym hroot hsource htarget hmem
    rw [hedge] at hfalse
    cases hfalse

end YMGap.Continuum.FiniteBoolGraphRootComponent

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.FiniteBoolGraphRootComponent.root_mem_rootComponent
#print axioms
  YMGap.Continuum.FiniteBoolGraphRootComponent.rootComponent_connected
#print axioms
  YMGap.Continuum.FiniteBoolGraphRootComponent.rootComponent_adj_false_of_not_mem
#print axioms
  YMGap.Continuum.FiniteBoolGraphRootComponent.rootComponent_closed_under_edge
