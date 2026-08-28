/-
# Exact finite fibers indexed by realized key representatives

A deterministic finite pushforward is naturally indexed by a duplicate-free
list of target keys.  In applications, however, a target key may be only an
encoding: the estimate on its fiber still needs an actual source
representative in order to recover concrete dependent target data.

This module selects the last occurring representative of every realized key.
The selected representatives remain members of the source list, their key
list is duplicate-free, and their keys cover every source.  Consequently the
sum of the exact fibers indexed by those representatives is exactly the total
source weight.

Constructive contract: structural recursion on finite lists, decidable key
equality, and the exact deterministic-pushforward theorem.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.FiniteKeyRepresentativePartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One actual representative of every realized key -/

/-- Retain the last source representative of each realized key. -/
def keyRepresentatives {Source Key : Type} [DecidableEq Key]
    (code : Source -> Key) : List Source -> List Source
  | [] => []
  | source :: sources =>
      let representatives := keyRepresentatives code sources
      if code source ∈ representatives.map code then
        representatives
      else
        source :: representatives

/-- Every selected key representative is an actual member of the source
list. -/
theorem keyRepresentatives_mem_source
    {Source Key : Type} [DecidableEq Key]
    (code : Source -> Key) : forall sources representative,
      representative ∈ keyRepresentatives code sources ->
        representative ∈ sources
  | [], representative, hmem => absurd hmem List.not_mem_nil
  | source :: sources, representative, hmem => by
      let representatives := keyRepresentatives code sources
      change representative ∈
        (if code source ∈ representatives.map code then
          representatives else source :: representatives) at hmem
      split at hmem
      next hpresent =>
        exact List.mem_cons_of_mem source
          (keyRepresentatives_mem_source code sources representative hmem)
      next habsent =>
        rcases List.mem_cons.mp hmem with heq | htail
        · exact heq ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem source
            (keyRepresentatives_mem_source code sources representative htail)

/-- Every source key is represented by one selected actual source. -/
theorem keyRepresentatives_cover
    {Source Key : Type} [DecidableEq Key]
    (code : Source -> Key) : forall sources source,
      source ∈ sources ->
        code source ∈ (keyRepresentatives code sources).map code
  | [], source, hmem => absurd hmem List.not_mem_nil
  | head :: tail, source, hmem => by
      let representatives := keyRepresentatives code tail
      change code source ∈
        (if code head ∈ representatives.map code then
          representatives else head :: representatives).map code
      split
      next hpresent =>
        rcases List.mem_cons.mp hmem with heq | htail
        · subst source
          exact hpresent
        · exact keyRepresentatives_cover code tail source htail
      next habsent =>
        simp only [List.map_cons, List.mem_cons]
        rcases List.mem_cons.mp hmem with heq | htail
        · exact Or.inl (congrArg code heq)
        · exact Or.inr (keyRepresentatives_cover code tail source htail)

/-- The selected representatives have pairwise distinct keys. -/
theorem keyRepresentatives_keys_nodup
    {Source Key : Type} [DecidableEq Key]
    (code : Source -> Key) : forall sources,
      ((keyRepresentatives code sources).map code).Nodup
  | [] => List.nodup_nil
  | source :: sources => by
      let representatives := keyRepresentatives code sources
      change
        ((if code source ∈ representatives.map code then
          representatives else source :: representatives).map code).Nodup
      split
      next hpresent => exact keyRepresentatives_keys_nodup code sources
      next habsent =>
        simp only [List.map_cons]
        exact List.nodup_cons.mpr
          ⟨habsent, keyRepresentatives_keys_nodup code sources⟩

/-! ## 2. Exact representative-indexed fiber partition -/

/-- The concrete source list lying over the key of one selected
representative. -/
def representativeFiber {Source Key : Type} [DecidableEq Key]
    (sources : List Source) (code : Source -> Key)
    (representative : Source) : List Source :=
  sources.filter fun source => decide (code representative = code source)

/-- Fiber summation through the generic deterministic pushforward is exactly
summation over the concrete representative fiber. -/
theorem fiberWeight_eq_representativeFiber
    {Source Key : Type} [DecidableEq Key]
    (sources : List Source) (weight : Source -> Q')
    (code : Source -> Key) (representative : Source) :
    fiberWeight sources weight code (code representative) =
      listQSum weight (representativeFiber sources code representative) :=
  rfl

private theorem listQSum_map_local {A B : Type}
    (value : B -> Q') (map : A -> B) : forall items : List A,
    listQSum value (items.map map) =
      listQSum (fun item => value (map item)) items
  | [] => rfl
  | head :: tail =>
      congrArg (fun rest => value (map head) + rest)
        (listQSum_map_local value map tail)

/-- **Exact realized-key partition.**  The representative fibers recover the
complete source weight, without enumerating unrealized keys or losing the
actual dependent target data carried by a representative. -/
theorem keyRepresentativeFibers_weight_total
    {Source Key : Type} [DecidableEq Key]
    (sources : List Source) (weight : Source -> Q')
    (code : Source -> Key) :
    listQSum
        (fun representative =>
          listQSum weight
            (representativeFiber sources code representative))
        (keyRepresentatives code sources) ≈
      listQSum weight sources := by
  let representatives := keyRepresentatives code sources
  have htotal := fiberWeight_total sources weight code
    (representatives.map code)
    (keyRepresentatives_keys_nodup code sources)
    (fun source hsource =>
      keyRepresentatives_cover code sources source hsource)
  rw [listQSum_map_local] at htotal
  simpa only [representativeFiber, fiberWeight] using htotal

#print axioms keyRepresentatives
#print axioms keyRepresentatives_mem_source
#print axioms keyRepresentatives_cover
#print axioms keyRepresentatives_keys_nodup
#print axioms representativeFiber
#print axioms fiberWeight_eq_representativeFiber
#print axioms keyRepresentativeFibers_weight_total

end YMGap.Continuum.FiniteKeyRepresentativePartition
