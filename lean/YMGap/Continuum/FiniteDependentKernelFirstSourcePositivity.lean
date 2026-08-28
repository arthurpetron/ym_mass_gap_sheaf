/-
# Positivity retained by canonical first-source thinning

The first-source selector was introduced to obtain column capacity without an
injective decoder.  Its positivity mechanism is equally concrete: if any
listed source has a listed channel reaching a target, the selector returns a
listed source which itself has such a channel.  If every listed channel has
positive weight, that selected channel survives thinning with its original
positive weight.

This module proves that finite-search fact and the small positive-sum lemma
needed to lift one surviving term to a row or source total.  It imposes no
probabilistic or Yang--Mills assumptions.

Constructive contract: Boolean list search, dependent finite carriers, and
exact `Q'` order only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.FiniteDependentKernelFirstSourceThinning

namespace YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. Search soundness and completeness -/

theorem sourceReachesTargetB_true_of_mem_realize
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source -> Type)
    (choices : (source : Source) -> List (Choice source))
    (realize : (source : Source) -> Choice source -> Target)
    (source : Source) (target : Target) (choice : Choice source)
    (hchoice : choice ∈ choices source)
    (hrealize : target = realize source choice) :
    sourceReachesTargetB Choice choices realize source target = true := by
  unfold sourceReachesTargetB
  exact List.any_eq_true.mpr
    ⟨choice, hchoice, decide_eq_true hrealize⟩

theorem sourceReachesTargetB_choice_of_true
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source -> Type)
    (choices : (source : Source) -> List (Choice source))
    (realize : (source : Source) -> Choice source -> Target)
    (source : Source) (target : Target)
    (hreach : sourceReachesTargetB
      Choice choices realize source target = true) :
    ∃ choice : Choice source,
      choice ∈ choices source ∧ target = realize source choice := by
  unfold sourceReachesTargetB at hreach
  obtain ⟨choice, hchoice, heq⟩ := List.any_eq_true.mp hreach
  exact ⟨choice, hchoice, of_decide_eq_true heq⟩

theorem firstSourceForTarget_some_of_reachable
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source -> Type)
    (choices : (source : Source) -> List (Choice source))
    (realize : (source : Source) -> Choice source -> Target)
    (target : Target) : forall (sources : List Source) (source : Source),
    source ∈ sources ->
    sourceReachesTargetB Choice choices realize source target = true ->
    ∃ selected,
      firstSourceForTarget Choice choices realize target sources =
        some selected
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, source, hmem, hreach => by
      unfold firstSourceForTarget
      cases hhead : sourceReachesTargetB
          Choice choices realize head target with
      | true =>
          simp only [↓reduceIte]
          exact ⟨head, rfl⟩
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rcases List.mem_cons.mp hmem with hsource | htail
          · subst source
            rw [hhead] at hreach
            contradiction
          · exact firstSourceForTarget_some_of_reachable
              Choice choices realize target tail source htail hreach

theorem firstSourceForTarget_reaches_of_eq_some
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source -> Type)
    (choices : (source : Source) -> List (Choice source))
    (realize : (source : Source) -> Choice source -> Target)
    (target : Target) : forall {sources : List Source} {source : Source},
    firstSourceForTarget Choice choices realize target sources = some source ->
      sourceReachesTargetB Choice choices realize source target = true
  | [], _, hfirst => by cases hfirst
  | head :: tail, source, hfirst => by
      unfold firstSourceForTarget at hfirst
      cases hhead : sourceReachesTargetB
          Choice choices realize head target with
      | false =>
          simp only [hhead, Bool.false_eq_true, ↓reduceIte] at hfirst
          exact firstSourceForTarget_reaches_of_eq_some
            Choice choices realize target hfirst
      | true =>
          simp only [hhead, ↓reduceIte] at hfirst
          have heq : head = source := Option.some.inj hfirst
          exact heq ▸ hhead

/-- If one listed channel reaches a target, first-source search returns a
listed source together with a listed channel reaching that same target. -/
theorem firstSourceForTarget_some_choice_of_reachable
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source -> Type)
    (choices : (source : Source) -> List (Choice source))
    (realize : (source : Source) -> Choice source -> Target)
    (sources : List Source) (seed : Source) (target : Target)
    (hseed : seed ∈ sources)
    (hreach : sourceReachesTargetB
      Choice choices realize seed target = true) :
    ∃ selected,
      firstSourceForTarget Choice choices realize target sources =
          some selected ∧
      ∃ choice : Choice selected,
        choice ∈ choices selected ∧ target = realize selected choice := by
  obtain ⟨selected, hfirst⟩ :=
    firstSourceForTarget_some_of_reachable
      Choice choices realize target sources seed hseed hreach
  have hselectedReach := firstSourceForTarget_reaches_of_eq_some
    Choice choices realize target hfirst
  obtain ⟨choice, hchoice, hrealize⟩ :=
    sourceReachesTargetB_choice_of_true
      Choice choices realize selected target hselectedReach
  exact ⟨selected, hfirst, choice, hchoice, hrealize⟩

/-! ## 2. A selected positive channel gives positive retained mass -/

theorem firstSourceThinnedWeight_pos_of_selected
    {Source Target : Type} [DecidableEq Source] [DecidableEq Target]
    (sources : List Source)
    (Choice : Source -> Type)
    (choices : (source : Source) -> List (Choice source))
    (localWeight : (source : Source) -> Choice source -> Q')
    (realize : (source : Source) -> Choice source -> Target)
    (source : Source) (choice : Choice source) (target : Target)
    (hfirst : firstSourceForTarget Choice choices realize target sources =
      some source)
    (hrealize : target = realize source choice)
    (hpos : (0 : Q') < localWeight source choice) :
    (0 : Q') < firstSourceThinnedWeight
      sources Choice choices localWeight realize source choice := by
  unfold firstSourceThinnedWeight
  have hselected : firstSourceForTarget Choice choices realize
      (realize source choice) sources = some source := by
    rw [← hrealize]
    exact hfirst
  rw [if_pos hselected]
  exact hpos

theorem listQSum_pos_of_mem
    {A : Type} (value : A -> Q')
    (hnonnegative : forall item, (0 : Q') ≤ value item) :
    forall (items : List A) {item : A},
      item ∈ items -> (0 : Q') < value item ->
        (0 : Q') < listQSum value items
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem, hpos => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.pos_of_lt_of_le hpos
          (Q'.add_le_self_of_nonneg
            (value head) (listQSum value tail)
            (listQSum_nonnegative_on value tail
              (fun tailItem _ => hnonnegative tailItem)))
      · have ih := listQSum_pos_of_mem value hnonnegative tail htail hpos
        have hle : listQSum value tail ≤
            value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head)
          rwa [Q'.zero_add'] at h
        exact Q'.pos_of_lt_of_le ih hle

end YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity

#print axioms YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity.sourceReachesTargetB_true_of_mem_realize
#print axioms YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity.sourceReachesTargetB_choice_of_true
#print axioms YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity.firstSourceForTarget_some_choice_of_reachable
#print axioms YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity.firstSourceThinnedWeight_pos_of_selected
#print axioms YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity.listQSum_pos_of_mem
