/-
# The canonical reverse occurrence path has a unique forward seed

The unique artificial-root neighbor theorem is transported through root
stripping, walk reversal, and constructive loop erasure.  It yields the exact
endpoint property needed by the exceptional source decoder: every forward
seed on the extracted simple path is its terminal seed.
-/

import YMGap.Continuum.XiExceptionalWarshallRootNeighbor

namespace YMGap.Continuum.XiExceptionalWarshallSeedEndpoint

open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalWarshallRootNeighbor

theorem leftWalkToIndex_mem_lift
    (seed : Nat → Bool) (edge : Nat → Nat → Bool) :
    ∀ {i j : Nat}
      (walk : CWalk (occurrenceReachEdge seed edge)
        (SwitchVertex.left i) (SwitchVertex.left j))
      (k : Nat),
      k ∈ (leftWalkToIndex seed edge walk).vertices →
        SwitchVertex.left k ∈ walk.vertices
  | i, _, .single _, k, hk => by
      simp only [leftWalkToIndex, CWalk.vertices] at hk
      have hk' := List.mem_singleton.mp hk
      subst k
      exact List.mem_cons_self
  | _, _, @CWalk.cons _ _ _ (.left next) _ hedge rest, k, hk => by
      change edge _ next = true at hedge
      simp only [leftWalkToIndex, CWalk.vertices] at hk
      rcases List.mem_cons.mp hk with hk | hk
      · rw [hk]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _
          (leftWalkToIndex_mem_lift seed edge rest k hk)

theorem stripOccurrenceRoot_neighbor_unique
    (seed : Nat → Bool) (edge : Nat → Nat → Bool) {finish : Nat}
    (walk : CWalk (occurrenceReachEdge seed edge)
      SwitchVertex.root (SwitchVertex.left finish))
    (hunique : ∀ a b,
      SwitchVertex.left a ∈ walk.vertices →
      SwitchVertex.left b ∈ walk.vertices →
      seed a = true → seed b = true → a = b) :
    let stripped := stripOccurrenceRoot seed edge walk
    ∀ a b, a ∈ stripped.walk.vertices → b ∈ stripped.walk.vertices →
      seed a = true → seed b = true → a = b := by
  cases walk with
  | @cons _ next _ hedge rest =>
      cases next with
      | root => simp [occurrenceReachEdge] at hedge
      | right i => simp [occurrenceReachEdge] at hedge
      | left i =>
          dsimp only [stripOccurrenceRoot]
          intro a b ha hb hsa hsb
          apply hunique a b
          · exact List.mem_cons_of_mem _
              (leftWalkToIndex_mem_lift seed edge rest a ha)
          · exact List.mem_cons_of_mem _
              (leftWalkToIndex_mem_lift seed edge rest b hb)
          · exact hsa
          · exact hsb

theorem CWalk.mem_dropTo_original
    {α : Type} [DecidableEq α] {edge : α → α → Bool} :
    ∀ {x y : α} (walk : CWalk edge x y)
      (a : α) (ha : a ∈ walk.vertices) (k : α),
      k ∈ (walk.dropTo a ha).vertices → k ∈ walk.vertices
  | _, _, .single _, a, ha, k, hk => by
      have hax := List.mem_singleton.mp ha
      subst a
      exact hk
  | x, _, .cons hedge rest, a, ha, k, hk => by
      by_cases hax : a = x
      · subst a
        simpa only [CWalk.dropTo, CWalk.vertices] using hk
      · have har : a ∈ rest.vertices :=
          (List.mem_cons.mp ha).resolve_left hax
        exact List.mem_cons_of_mem _
          (CWalk.mem_dropTo_original rest a har k (by
            simpa [CWalk.dropTo, hax] using hk))

theorem CWalk.mem_reverse_original
    {α : Type} {edge : α → α → Bool}
    (hsymm : ∀ a b, edge a b = true → edge b a = true) :
    ∀ {x y : α} (walk : CWalk edge x y) (k : α),
      k ∈ (walk.reverse hsymm).vertices → k ∈ walk.vertices
  | _, _, .single _, k, hk => hk
  | x, _, .cons hedge rest, k, hk => by
      rcases CWalk.mem_append_elim _ _ k hk with hk | hk
      · exact List.mem_cons_of_mem _
          (CWalk.mem_reverse_original hsymm rest k hk)
      · simp [CWalk.vertices] at hk
        rcases hk with hk | hk
        · subst k
          exact List.mem_cons_of_mem _ (CWalk.start_mem_vertices rest)
        · subst k
          exact List.mem_cons_self

theorem CWalk.mem_eraseLoops_original
    {α : Type} [DecidableEq α] {edge : α → α → Bool} :
    ∀ {x y : α} (walk : CWalk edge x y) (k : α),
      k ∈ (CWalk.eraseLoops walk).walk.vertices → k ∈ walk.vertices
  | _, _, .single _, k, hk => hk
  | x, _, .cons hedge rest, k, hk => by
      let tail := CWalk.eraseLoops rest
      by_cases hx : x ∈ tail.walk.vertices
      · have hdrop : k ∈ (tail.walk.dropTo x hx).vertices := by
          simpa [CWalk.eraseLoops, tail, hx] using hk
        have htail : k ∈ tail.walk.vertices :=
          CWalk.mem_dropTo_original tail.walk x hx k hdrop
        exact List.mem_cons_of_mem _
          (CWalk.mem_eraseLoops_original rest k htail)
      · have hcons : k ∈ (CWalk.cons hedge tail.walk).vertices := by
          simpa [CWalk.eraseLoops, tail, hx] using hk
        rcases List.mem_cons.mp hcons with hk | hk
        · exact List.mem_cons.mpr (Or.inl hk)
        · exact List.mem_cons_of_mem _
            (CWalk.mem_eraseLoops_original rest k hk)

theorem occurrenceUniverse_tail_root_not_mem (N : Nat) :
    SwitchVertex.root ∉ (List.range N).map SwitchVertex.left := by
  intro h
  obtain ⟨i, hi, hir⟩ := List.mem_map.mp h
  cases hir

theorem reverseOccurrencePath_seed_unique
    (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) (marked : Nat)
    (hreach : forwardComponent N inc left right bad marked = true) :
    let path := reverseOccurrencePathOfReach N inc left right bad marked hreach
    ∀ i, i ∈ path.walk.vertices →
      forwardSeed N left right bad i = true → i = path.seed := by
  let seed := forwardSeed N left right bad
  let edge := disagreementEdge N inc left right
  let reachEdge := occurrenceReachEdge seed edge
  let tailU := (List.range N).map SwitchVertex.left
  have htail : warshall reachEdge tailU SwitchVertex.root
      (SwitchVertex.left marked) = true := by
    change warshall reachEdge (SwitchVertex.root :: tailU)
      SwitchVertex.root (SwitchVertex.left marked) = true at hreach
    unfold warshall at hreach
    have hr := warshall_refl reachEdge tailU SwitchVertex.root
    simpa [hr] using hreach
  let rootWalk : CWalk reachEdge SwitchVertex.root
      (SwitchVertex.left marked) :=
    canonicalWarshallWalk reachEdge tailU SwitchVertex.root
      (SwitchVertex.left marked) htail
  have hfull : CWalk.ofDWalk
      (warshallSound reachEdge (occurrenceUniverse N)
        SwitchVertex.root (SwitchVertex.left marked) hreach) = rootWalk := by
    change canonicalWarshallWalk reachEdge
        (SwitchVertex.root :: tailU) SwitchVertex.root
          (SwitchVertex.left marked) hreach = rootWalk
    exact canonicalWarshallWalk_direct reachEdge SwitchVertex.root tailU
      SwitchVertex.root (SwitchVertex.left marked) hreach htail
  have hrawUnique : ∀ a b,
      SwitchVertex.left a ∈ rootWalk.vertices →
      SwitchVertex.left b ∈ rootWalk.vertices →
      seed a = true → seed b = true → a = b := by
    intro a b ha hb hsa hsb
    apply SwitchVertex.left.inj
    exact canonicalWarshallWalk_root_neighbor_unique
      reachEdge SwitchVertex.root rfl tailU
      (occurrenceUniverse_tail_root_not_mem N)
      (SwitchVertex.left marked) (by intro h; cases h)
      htail (SwitchVertex.left a) (SwitchVertex.left b)
      ha hb hsa hsb
  let stripped := stripOccurrenceRoot seed edge rootWalk
  have hstripped : ∀ a b,
      a ∈ stripped.walk.vertices → b ∈ stripped.walk.vertices →
      seed a = true → seed b = true → a = b :=
    stripOccurrenceRoot_neighbor_unique seed edge rootWalk hrawUnique
  let backward := CWalk.reverse (fun i j h => by
      change disagreementEdge N inc left right j i = true
      rw [disagreementEdge_symm N inc left right j i]
      exact h) stripped.walk
  let simple := CWalk.eraseLoops backward
  have hsimple : ∀ i, i ∈ simple.walk.vertices →
      seed i = true → i = stripped.start := by
    intro i hi hsi
    have hiback : i ∈ backward.vertices :=
      CWalk.mem_eraseLoops_original backward i hi
    have hiforward : i ∈ stripped.walk.vertices :=
      CWalk.mem_reverse_original _ stripped.walk i hiback
    exact hstripped i stripped.start hiforward
      (CWalk.start_mem_vertices stripped.walk) hsi stripped.seed_true
  dsimp only [reverseOccurrencePathOfReach]
  rw [hfull]
  intro i hi hsi
  exact hsimple i hi hsi

#print axioms leftWalkToIndex_mem_lift
#print axioms stripOccurrenceRoot_neighbor_unique
#print axioms CWalk.mem_reverse_original
#print axioms CWalk.mem_eraseLoops_original
#print axioms reverseOccurrencePath_seed_unique

end YMGap.Continuum.XiExceptionalWarshallSeedEndpoint
