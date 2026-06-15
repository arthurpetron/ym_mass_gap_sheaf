/-
Plan 2 of the categorical lift: the **codynamic transfer as a category with
closure transport**.

`Codynamic.lean` exhibits the SU(2) σ̂-budget closure and a synthetic EKF
sensor-fusion closure as two instances of one abstract
`InductiveBoundWitnessSystem`, sharing the proof `terminal_invariant_bound`.
Per `docs/category-theory-lift-assessment.md` this is the clearest reuse case
(≥2 genuine instances).  This module lifts "both are instances" to a genuine
categorical statement: the systems form a **category** `CodynCat` whose
morphisms are budget-domination refinements, along which **closure transports**
— the categorical form of "the worst case dominates, so all easier systems
close."  This is precisely the structure behind "SU(2) is the worst case ⇒ all
simple groups close" (`RG/UniformBudget.lean`).

# What this module delivers

  * `BudgetObj` — a budget datum (degradation, initial bound, budget,
    summability), the object stripped of a specific gap so morphisms can
    transport closure.
  * `ClosureWitness` — `Σ'`-typed (Type-level, AGENTS.md Rule 8): a strictly
    positive gap with `budget + gap ≤ initial_bound`.
  * `BudgetHom` — a morphism `S ⟶ S'`: `S` is *easier* than `S'`
    (`S.budget ≤ S'.budget`, `S'.initial_bound ≤ S.initial_bound`).
    Propositional, so `CodynCat` is thin and its laws are `rfl`.
  * `CodynCat : Cat` — the category of budget data.
  * `transportClosure` — **the load-bearing theorem**: a morphism `S ⟶ S'`
    transports a closure witness of the harder `S'` to one of the easier `S`
    (with the same gap).  This is the universal-property payoff the assessment
    requires: prove closure once for the worst case, get it for all easier
    objects for free.
  * `budgetFunctor : Functor CodynCat QPosetCat` — the budget is functorial
    (monotone) into the poset of `Q'`.
  * `su2Obj`, `ekfObj`, `su2_to_ekf` — the existing SU(2) and EKF instances as
    `BudgetObj`s and an explicit morphism between them, realizing the shared
    interface as transport (not coincidence): EKF's closure transports to SU(2).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Categorical.Core
import YMGap.Codynamic

namespace YMGap.Categorical

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SigmaHatLimit
open YMGap.Codynamic

/-! ## Budget objects and closure witnesses -/

/-- A **budget datum**: the per-step degradation, initial bound, a uniform
budget on the partial sums, and the summability proof.  The object of
`CodynCat` — stripped of a specific gap so morphisms can transport closure. -/
structure BudgetObj where
  /-- Per-step degradation sequence. -/
  degradation : QSeq
  /-- Initial bound. -/
  initial_bound : Q'
  /-- Uniform upper bound on the partial sums of `degradation`. -/
  budget : Q'
  /-- The partial sums are bounded by `budget`. -/
  budget_summable : ∀ N, finSum degradation N ≤ budget

/-- A **closure witness** for a budget datum: a strictly positive gap `g` with
`budget + g ≤ initial_bound` (`Σ'`-typed, Type-level data per Rule 8).  From it,
`Codynamic.terminal_invariant_bound` gives the uniform terminal-invariant lower
bound `∀ N, finSum degradation N + g ≤ initial_bound`. -/
def ClosureWitness (S : BudgetObj) : Type :=
  Σ' g : Q', (0 : Q') < g ∧ S.budget + g ≤ S.initial_bound

/-- A closure witness yields the uniform terminal-invariant bound at every
truncation (the bridge to `Codynamic`'s abstract theorem). -/
theorem ClosureWitness.terminal {S : BudgetObj} (w : ClosureWitness S) :
    ∀ N, finSum S.degradation N + w.1 ≤ S.initial_bound :=
  sigma_hat_uniform_positive_lower_bound
    S.degradation S.budget S.initial_bound w.1
    S.budget_summable w.2.2

/-! ## Morphisms: budget-domination refinements -/

/-- A **morphism** `S ⟶ S'`: `S` is *easier* than `S'` — it degrades no more
(`S.budget ≤ S'.budget`) and has at least as much room
(`S'.initial_bound ≤ S.initial_bound`).  Both fields are propositional, so
`CodynCat` is a thin category. -/
structure BudgetHom (S S' : BudgetObj) : Prop where
  /-- `S` degrades no more than `S'`. -/
  budget_le : S.budget ≤ S'.budget
  /-- `S` has at least as much room as `S'`. -/
  init_ge : S'.initial_bound ≤ S.initial_bound

/-- Identity morphism (reflexivity of `≤`). -/
def BudgetHom.id (S : BudgetObj) : BudgetHom S S where
  budget_le := Q'.le_refl' _
  init_ge := Q'.le_refl' _

/-- Composition (transitivity of `≤`). -/
def BudgetHom.comp {S S' S'' : BudgetObj}
    (f : BudgetHom S S') (g : BudgetHom S' S'') : BudgetHom S S'' where
  budget_le := Q'.le_trans' _ _ _ f.budget_le g.budget_le
  init_ge := Q'.le_trans' _ _ _ g.init_ge f.init_ge

/-- **`CodynCat`** — the category of budget data.  Thin (`BudgetHom` is a
`Prop`), so the category laws are `rfl` by proof-irrelevance. -/
def CodynCat : Cat where
  Obj := BudgetObj
  Hom := fun S S' => PLift (BudgetHom S S')
  id := fun S => PLift.up (BudgetHom.id S)
  comp := fun f g => PLift.up (BudgetHom.comp f.down g.down)
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-! ## The load-bearing theorem: closure transports along morphisms -/

/-- **Closure transports along morphisms.**  A morphism `S ⟶ S'` (with `S`
easier than `S'`) transports a closure witness of the *harder* `S'` to one of
the *easier* `S`, with the SAME gap:

    budget_S + g ≤ budget_{S'} + g ≤ initial_{S'} ≤ initial_S.

This is the universal-property payoff: prove closure once for the worst case
(largest budget / least room), get it for every easier object for free — the
categorical form of "SU(2) is the worst case ⇒ all simple groups close." -/
def transportClosure {S S' : BudgetObj}
    (h : BudgetHom S S') (w : ClosureWitness S') : ClosureWitness S :=
  ⟨w.1, w.2.1, by
    -- S.budget + g ≤ S'.budget + g ≤ S'.initial ≤ S.initial
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right S.budget S'.budget w.1 h.budget_le) ?_
    exact Q'.le_trans' _ _ _ w.2.2 h.init_ge⟩

/-! ## The budget functor `CodynCat → (Q', ≤)` -/

/-- The thin category of rationals under `≤` (`Hom x y = PLift (x ≤ y)`). -/
def QPosetCat : Cat where
  Obj := Q'
  Hom := fun x y => PLift (x ≤ y)
  id := fun x => PLift.up (Q'.le_refl' x)
  comp := fun f g => PLift.up (Q'.le_trans' _ _ _ f.down g.down)
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-- **The budget is functorial.**  `S ↦ S.budget` is a (monotone) functor
`CodynCat → QPosetCat`: a morphism `S ⟶ S'` carries `S.budget ≤ S'.budget`.
Functoriality is automatic (`QPosetCat` is thin). -/
def budgetFunctor : Functor CodynCat QPosetCat where
  obj := fun S => S.budget
  map := fun f => PLift.up f.down.budget_le
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-! ## The SU(2) and EKF instances as objects, and a transport morphism -/

/-- A full `InductiveBoundWitnessSystem` forgets to a `BudgetObj`. -/
def forget (s : InductiveBoundWitnessSystem) : BudgetObj where
  degradation := s.degradation
  initial_bound := s.initial_bound
  budget := s.budget
  budget_summable := s.budget_summable

/-- Its closure witness, from the system's own gap. -/
def forgetClosure (s : InductiveBoundWitnessSystem) : ClosureWitness (forget s) :=
  ⟨s.gap, s.gap_positive, s.gap_fits⟩

/-- The SU(2) σ̂-budget closure as a `CodynCat` object. -/
def su2Obj : BudgetObj := forget SU2_YM_Instance.su2_ym_system

/-- The EKF sensor-fusion closure as a `CodynCat` object. -/
def ekfObj : BudgetObj := forget EKF_Instance.ekf_system

/-- **An explicit morphism `su2Obj ⟶ ekfObj`.**  SU(2) is *easier* than EKF:
its budget `9/10000` is below EKF's `5/100`, and both have initial bound `1`.
So `su2Obj` refines into `ekfObj` in `CodynCat`. -/
def su2_to_ekf : BudgetHom su2Obj ekfObj where
  budget_le := by decide
  init_ge := by decide

/-- **The shared interface as transport, not coincidence.**  EKF's closure
witness transports along `su2_to_ekf` to a closure witness for SU(2) — the
SU(2) σ̂-budget closure is *derived* from the EKF closure through the categorical
morphism (with EKF's gap `95/100`), exhibiting that the two instances are
related by a `CodynCat` morphism, not merely parallel. -/
def su2_closure_via_ekf : ClosureWitness su2Obj :=
  transportClosure su2_to_ekf (forgetClosure EKF_Instance.ekf_system)

end YMGap.Categorical

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Categorical.ClosureWitness.terminal
#print axioms YMGap.Categorical.CodynCat
#print axioms YMGap.Categorical.transportClosure
#print axioms YMGap.Categorical.budgetFunctor
#print axioms YMGap.Categorical.su2_to_ekf
#print axioms YMGap.Categorical.su2_closure_via_ekf
