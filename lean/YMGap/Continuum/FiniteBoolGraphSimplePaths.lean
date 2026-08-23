/-
# Constructive loop erasure for finite Boolean graph paths

The connected-component compiler supplies explicit `ChainIn` walks, but its
transitive construction may revisit vertices.  This module normalizes such a
walk to cons form, erases loops by decidable membership tests, and bounds the
resulting simple walk by the length of its finite support.

The edge relation is augmented with a Boolean certificate that every target
lies in the support.  Consequently loop erasure retains both actual graph
edges and support membership.  All constructions are data-valued; no
shortest-path choice or excluded-middle search over propositions is used.
-/

import YMGap.Continuum.FiniteBoolGraphComponents

namespace YMGap.Continuum.FiniteBoolGraphSimplePaths

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Continuum.FiniteBoolGraphComponents

/-! ## 1. Cons-form walks and support-aware normalization -/

inductive Walk {State : Type} (edge : State → State → Bool) :
    State → State → Type
  | single (state : State) : Walk edge state state
  | cons {first next last : State} :
      edge first next = true → Walk edge next last → Walk edge first last

namespace Walk

variable {State : Type} {edge : State → State → Bool}

def vertices : {first last : State} → Walk edge first last → List State
  | first, _, .single _ => [first]
  | first, _, .cons _ rest => first :: vertices rest

def start : {first last : State} → Walk edge first last → State
  | first, _, _ => first

@[simp] theorem start_eq {first last : State}
    (path : Walk edge first last) : path.start = first := by
  cases path <;> rfl

def edgeLength : {first last : State} → Walk edge first last → Nat
  | _, _, .single _ => 0
  | _, _, .cons _ rest => edgeLength rest + 1

/-- The literal directed edges of a cons-form walk. -/
def directedEdges : {first last : State} →
    Walk edge first last → List (State × State)
  | _, _, .single _ => []
  | first, _, .cons (next := next) _ rest =>
      (first, next) :: directedEdges rest

/-- The source of every directed edge occurs among the walk vertices. -/
theorem directedEdges_source_mem_vertices :
    ∀ {first last : State} (path : Walk edge first last)
      (traversed : State × State),
      traversed ∈ path.directedEdges → traversed.1 ∈ path.vertices
  | _, _, .single _, traversed, htraversed => by
      cases htraversed
  | first, _, .cons (next := next) hedge rest, traversed, htraversed => by
      rcases List.mem_cons.mp htraversed with hhead | htail
      · rw [hhead]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem first
          (directedEdges_source_mem_vertices rest traversed htail)

/-- A vertex-simple walk cannot repeat a directed edge. -/
theorem directedEdges_nodup_of_vertices_nodup :
    ∀ {first last : State} (path : Walk edge first last),
      path.vertices.Nodup → path.directedEdges.Nodup
  | _, _, .single _, _ => List.nodup_nil
  | first, _, .cons (next := next) hedge rest, hvertices => by
      have hparts := List.nodup_cons.mp hvertices
      apply List.nodup_cons.mpr
      constructor
      · intro hhead
        exact hparts.1
          (directedEdges_source_mem_vertices rest (first, next) hhead)
      · exact directedEdges_nodup_of_vertices_nodup rest hparts.2

def append {first middle last : State} :
    Walk edge first middle → Walk edge middle last → Walk edge first last
  | .single _, right => right
  | .cons hedge rest, right => .cons hedge (append rest right)

def dropTo [DecidableEq State] :
    {first last : State} → (path : Walk edge first last) →
      (target : State) → target ∈ vertices path → Walk edge target last
  | _, _, .single first, target, htarget => by
      have heq : target = first := List.mem_singleton.mp htarget
      subst target
      exact .single first
  | first, _, .cons hedge rest, target, htarget => by
      by_cases heq : target = first
      · subst target
        exact .cons hedge rest
      · have hrest : target ∈ vertices rest :=
          (List.mem_cons.mp htarget).resolve_left heq
        exact dropTo rest target hrest

set_option linter.unusedVariables false in
theorem dropTo_nodup [DecidableEq State] :
    ∀ {first last : State} (path : Walk edge first last)
      (target : State) (htarget : target ∈ vertices path)
      (hnodup : (vertices path).Nodup),
      (vertices (dropTo path target htarget)).Nodup
  | _, _, .single first, target, htarget, _hnodup => by
      have heq : target = first := List.mem_singleton.mp htarget
      subst target
      simp [dropTo, vertices]
  | first, _, .cons hedge rest, target, htarget, hnodup => by
      by_cases heq : target = first
      · subst target
        simpa [dropTo, vertices] using hnodup
      · have hrest : target ∈ vertices rest :=
          (List.mem_cons.mp htarget).resolve_left heq
        have htail : (vertices rest).Nodup :=
          (List.nodup_cons.mp hnodup).2
        simpa [dropTo, heq] using
          dropTo_nodup rest target hrest htail

structure Simple (edge : State → State → Bool)
    (first last : State) : Type where
  walk : Walk edge first last
  nodup : walk.vertices.Nodup

def eraseLoops [DecidableEq State] :
    {first last : State} → Walk edge first last → Simple edge first last
  | _, _, .single first =>
      { walk := .single first
        nodup :=
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩ }
  | first, _, .cons hedge rest =>
      let tail := eraseLoops rest
      if hfirst : first ∈ tail.walk.vertices then
        { walk := tail.walk.dropTo first hfirst
          nodup := dropTo_nodup tail.walk first hfirst tail.nodup }
      else
        { walk := .cons hedge tail.walk
          nodup := List.nodup_cons.mpr ⟨hfirst, tail.nodup⟩ }

theorem all_vertices_of_start
    (Property : State → Prop)
    (hedge : ∀ first next,
      edge first next = true → Property first → Property next) :
    ∀ {first last : State} (path : Walk edge first last),
      Property first → ∀ state, state ∈ path.vertices → Property state
  | _, _, .single first, hfirst, state, hstate => by
      rw [List.mem_singleton.mp hstate]
      exact hfirst
  | _, _, .cons hedgeNow rest, hfirst, state, hstate => by
      rcases List.mem_cons.mp hstate with heq | hrest
      · rw [heq]
        exact hfirst
      · exact all_vertices_of_start Property hedge rest
          (hedge _ _ hedgeNow hfirst) state hrest

theorem edgeLength_add_one_eq_vertices_length :
    ∀ {first last : State} (path : Walk edge first last),
      path.edgeLength + 1 = path.vertices.length
  | _, _, .single _ => rfl
  | _, _, .cons _ rest => by
      have ih := edgeLength_add_one_eq_vertices_length rest
      simp only [edgeLength, vertices, List.length_cons]
      omega

theorem edgeLength_le_vertices_length
    {first last : State} (path : Walk edge first last) :
    path.edgeLength ≤ path.vertices.length := by
  have h := edgeLength_add_one_eq_vertices_length path
  omega

end Walk

def supportedEdge {State : Type} [DecidableEq State]
    (adjacent : State → State → Bool) (support : List State)
    (first next : State) : Bool :=
  adjacent first next && decide (next ∈ support)

namespace Walk

def ofChainIn {State : Type} [DecidableEq State]
    (adjacent : State → State → Bool) (support : List State) :
    {first last : State} → ChainIn adjacent support first last →
      Walk (supportedEdge adjacent support) first last
  | _, _, ChainIn.refl first => .single first
  | _, _, ChainIn.step hedge hnext rest =>
      .cons
        ((Bool.and_eq_true _ _).mpr
          ⟨hedge, by simpa using hnext⟩)
        (ofChainIn adjacent support rest)

end Walk

/-! ## 2. Constructive finite-pigeonhole bound -/

namespace FiniteListBound

variable {State : Type} [DecidableEq State]

def removeFirst (state : State) : List State → List State
  | [] => []
  | first :: rest =>
      if first = state then rest else first :: removeFirst state rest

theorem removeFirst_length (state : State) :
    ∀ states : List State, state ∈ states →
      (removeFirst state states).length + 1 = states.length
  | [], hstate => absurd hstate List.not_mem_nil
  | first :: rest, hstate => by
      by_cases heq : first = state
      · simp [removeFirst, heq]
      · simp only [removeFirst, heq, ↓reduceIte, List.length_cons]
        have hrest : state ∈ rest :=
          (List.mem_cons.mp hstate).resolve_left (fun h => heq h.symm)
        have ih := removeFirst_length state rest hrest
        omega

theorem mem_removeFirst (state : State) :
    ∀ (states : List State) (other : State),
      other ∈ states → other ≠ state →
        other ∈ removeFirst state states
  | [], other, hother, _ => absurd hother List.not_mem_nil
  | first :: rest, other, hother, hne => by
      by_cases heq : first = state
      · rw [removeFirst, if_pos heq]
        rcases List.mem_cons.mp hother with hfirst | hrest
        · exact absurd (hfirst.trans heq) hne
        · exact hrest
      · rw [removeFirst, if_neg heq]
        rcases List.mem_cons.mp hother with hfirst | hrest
        · rw [hfirst]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _
            (mem_removeFirst state rest other hrest hne)

theorem nodup_subset_length_le :
    ∀ (states support : List State), states.Nodup →
      (∀ state, state ∈ states → state ∈ support) →
      states.length ≤ support.length
  | [], support, _, _ => Nat.zero_le _
  | first :: rest, support, hnodup, hsubset => by
      have hfirst : first ∈ support := hsubset first List.mem_cons_self
      have hparts := List.nodup_cons.mp hnodup
      have htail : ∀ state, state ∈ rest →
          state ∈ removeFirst first support := by
        intro state hstate
        have hne : state ≠ first := fun heq => hparts.1 (heq ▸ hstate)
        exact mem_removeFirst first support state
          (hsubset state (List.mem_cons_of_mem first hstate)) hne
      have ih := nodup_subset_length_le rest
        (removeFirst first support) hparts.2 htail
      have hlength := removeFirst_length first support hfirst
      show rest.length + 1 ≤ support.length
      omega

end FiniteListBound

/-! ## 3. A simple support-bounded walk extracted from any internal chain -/

structure SupportBoundedSimpleWalk {State : Type} [DecidableEq State]
    (adjacent : State → State → Bool) (support : List State)
    (first last : State) : Type where
  walk : Walk (supportedEdge adjacent support) first last
  nodup : walk.vertices.Nodup
  vertices_subset : ∀ state, state ∈ walk.vertices → state ∈ support
  vertices_length_le : walk.vertices.length ≤ support.length
  edgeLength_le : walk.edgeLength ≤ support.length

def supportBoundedSimpleWalkOfChainIn
    {State : Type} [DecidableEq State]
    (adjacent : State → State → Bool) (support : List State)
    {first last : State} (hfirst : first ∈ support)
    (path : ChainIn adjacent support first last) :
    SupportBoundedSimpleWalk adjacent support first last := by
  let normalized := Walk.ofChainIn adjacent support path
  let simple := Walk.eraseLoops normalized
  have hpropagate : ∀ source target,
      supportedEdge adjacent support source target = true →
      source ∈ support → target ∈ support := by
    intro source target hedge _hsource
    exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hedge).2
  have hsubset : ∀ state, state ∈ simple.walk.vertices →
      state ∈ support :=
    Walk.all_vertices_of_start (fun state => state ∈ support)
      hpropagate simple.walk hfirst
  have hvertices := FiniteListBound.nodup_subset_length_le
    simple.walk.vertices support simple.nodup hsubset
  have hedgeLength := Nat.le_trans
    (Walk.edgeLength_le_vertices_length simple.walk) hvertices
  exact
    { walk := simple.walk
      nodup := simple.nodup
      vertices_subset := hsubset
      vertices_length_le := hvertices
      edgeLength_le := hedgeLength }

end YMGap.Continuum.FiniteBoolGraphSimplePaths

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.FiniteBoolGraphSimplePaths.Walk.dropTo_nodup
#print axioms
  YMGap.Continuum.FiniteBoolGraphSimplePaths.Walk.edgeLength_add_one_eq_vertices_length
#print axioms
  YMGap.Continuum.FiniteBoolGraphSimplePaths.Walk.directedEdges_nodup_of_vertices_nodup
#print axioms
  YMGap.Continuum.FiniteBoolGraphSimplePaths.FiniteListBound.nodup_subset_length_le
#print axioms
  YMGap.Continuum.FiniteBoolGraphSimplePaths.supportBoundedSimpleWalkOfChainIn
