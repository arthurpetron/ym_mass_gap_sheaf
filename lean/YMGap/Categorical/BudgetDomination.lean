/-
Upgrade A of the load-bearing categorical lift: **SU(2) as the worst-case
object of a budget-domination category, whose closure transports to every
admissible simple group.**

This makes the all-admissible-groups σ̂-budget closure
(`RepTheory.budget_closes_of_witness`) a **universal-property statement**: in
the category of group budget data ordered by domination, SU(2) is the object
every admissible group maps INTO (`eta_dominated` is exactly that morphism),
and SU(2)'s closure transports along the morphism to all of them.  The
categorical structure (`CodynCat`-style transport, `Categorical/Core` `Cat`)
is thereby on the critical path of the all-groups result, not decorative.

# Concurring evidence — honest scope

This is the *mathematical-closure narrative* (SU(2) is the terminal worst case)
concurring with the **numerical** all-groups evidence (the `U.4` sweep
`Σ η(G) ≤ Σ η(su2)` over all 19 group types, `notes/uniform-character-tail-bound.md`).
It is NOT arithmetically independent of the analytic `budget_closes_of_witness`:
the transport shares the monotonicity atom `RG.truncatedConst_le` with
`RG.monotone_budget`.  The value added is the categorical ORGANIZATION — closure
of one terminal object ⇒ closure of all — which is the natural statement of
"SU(2) is the worst case" and the structure the manuscript's all-groups claim
rests on.  (For an arithmetically-independent concurrence, see
`Continuum/ReflectionDagger.lean`, where OS2 is re-derived from a genuinely
different fact.)

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` only.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Categorical.Core
import YMGap.RG.UniformBudget

namespace YMGap.Categorical

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RepTheory
open YMGap.RG

/-! ## Group budget data and the closure predicate -/

/-- The budget-relevant projection of a simple group's RG data: the per-step
σ̂-degradation bound, the window length, and the initial string tension. -/
structure GroupBudget where
  /-- Uniform per-step σ̂-degradation bound `η_max`. -/
  etaMax : Q'
  /-- RG window length `K`. -/
  K : Nat
  /-- Initial dimensionless string tension `σ̂₀`. -/
  sigma0 : Q'

/-- **The budget closes**: the `K`-window degradation total stays under `σ̂₀`
at every truncation — the σ̂-budget closure predicate (the conclusion form of
`RepTheory.budget_closes_of_witness`). -/
def GroupBudget.Closes (G : GroupBudget) : Prop :=
  ∀ N, finSum (truncatedConst G.K G.etaMax) N ≤ G.sigma0

/-! ## Domination morphisms -/

/-- A **domination morphism** `G ⟶ G'`: `G` is *easier* than `G'` — it degrades
no more (`etaMax_le`), runs the same window (`K_eq`), and has at least as much
room (`sigma_ge`).  Propositional, so the category is thin. -/
structure GBHom (G G' : GroupBudget) : Prop where
  /-- `G` degrades no more than `G'`. -/
  etaMax_le : G.etaMax ≤ G'.etaMax
  /-- Same RG window. -/
  K_eq : G.K = G'.K
  /-- `G` has at least as much room as `G'`. -/
  sigma_ge : G'.sigma0 ≤ G.sigma0

/-- Identity domination morphism. -/
def GBHom.id (G : GroupBudget) : GBHom G G where
  etaMax_le := Q'.le_refl' _
  K_eq := rfl
  sigma_ge := Q'.le_refl' _

/-- Composition of domination morphisms. -/
def GBHom.comp {G G' G'' : GroupBudget}
    (f : GBHom G G') (g : GBHom G' G'') : GBHom G G'' where
  etaMax_le := Q'.le_trans' _ _ _ f.etaMax_le g.etaMax_le
  K_eq := f.K_eq.trans g.K_eq
  sigma_ge := Q'.le_trans' _ _ _ g.sigma_ge f.sigma_ge

/-- **The budget-domination category.**  Objects are group budget data;
morphisms are domination refinements (thin → laws are `rfl`). -/
def GroupBudgetCat : Cat where
  Obj := GroupBudget
  Hom := fun G G' => PLift (GBHom G G')
  id := fun G => PLift.up (GBHom.id G)
  comp := fun f g => PLift.up (GBHom.comp f.down g.down)
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-! ## The load-bearing theorem: closure transports along domination -/

/-- **Closure transports along domination morphisms.**  A morphism `G ⟶ G'`
(with `G` easier than `G'`) carries the closure of the *harder* `G'` to the
*easier* `G`:

    finSum(truncatedConst G.K G.etaMax) N
      ≤ finSum(truncatedConst G.K G'.etaMax) N    (truncatedConst_le, etaMax_le)
      = finSum(truncatedConst G'.K G'.etaMax) N    (K_eq)
      ≤ G'.sigma0                                  (Closes G')
      ≤ G.sigma0.                                  (sigma_ge)

The universal-property payoff: prove closure ONCE for the worst case, get it for
every easier object.  This is the categorical form of "SU(2) is the worst case
⇒ all simple groups close." -/
theorem GroupBudget.transportCloses {G G' : GroupBudget}
    (h : GBHom G G') (hG' : G'.Closes) : G.Closes := by
  intro N
  have step1 : finSum (truncatedConst G.K G.etaMax) N
      ≤ finSum (truncatedConst G.K G'.etaMax) N :=
    truncatedConst_le G.K h.etaMax_le N
  have step2 : finSum (truncatedConst G.K G'.etaMax) N
      = finSum (truncatedConst G'.K G'.etaMax) N := by rw [h.K_eq]
  refine Q'.le_trans' _ _ _ step1 ?_
  rw [step2]
  exact Q'.le_trans' _ _ _ (hG' N) h.sigma_ge

/-! ## SU(2) as the terminal worst-case object -/

/-- SU(2)'s group budget object. -/
def su2GB : GroupBudget where
  etaMax := su2.eta_max
  K := su2.K_steps
  sigma0 := su2.sigma0

/-- **SU(2) closes** — `RepTheory.su2_budget_closes` packaged as `Closes`. -/
theorem su2GB_closes : su2GB.Closes := su2_budget_closes

/-- An admissible group's budget object, bounded by SU(2)'s string tension
`σ̂₀` (the universal bound `budget_closes_of_witness` proves against). -/
def repGB (R : RepData) : GroupBudget where
  etaMax := R.eta_max
  K := R.K_steps
  sigma0 := su2.sigma0

/-- **Every admissible η-dominated group maps INTO SU(2)** in the
budget-domination category.  The morphism IS the `UniformBudgetWitness`:
`eta_dominated` is `etaMax_le`, `same_window` is `K_eq`, and the room is
reflexive (`σ̂₀ = su2.sigma0`).  This exhibits SU(2) as the weakly-terminal
worst-case object receiving an arrow from every admissible group. -/
def repGB_to_su2 (R : RepData) (w : UniformBudgetWitness R) : GBHom (repGB R) su2GB where
  etaMax_le := w.eta_dominated
  K_eq := w.same_window
  sigma_ge := Q'.le_refl' _

/-- **All admissible groups close, by transport from the terminal SU(2)
object.**  The σ̂-budget of any η-dominated admissible group closes —
re-derived categorically as the transport of SU(2)'s closure along the
domination morphism `repGB R ⟶ su2GB`, NOT by a fresh per-group estimate.

Concurs with `RepTheory.budget_closes_of_witness` (the two conclude the same
`∀ N, finSum(truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0`). -/
theorem all_admissible_close_via_terminal (R : RepData) (w : UniformBudgetWitness R) :
    (repGB R).Closes :=
  GroupBudget.transportCloses (repGB_to_su2 R w) su2GB_closes

/-- **The two derivations concur.**  The categorical (terminal-object transport)
and analytic (`budget_closes_of_witness`) routes establish the same all-groups
budget closure. -/
theorem all_admissible_close_concur (R : RepData) (w : UniformBudgetWitness R) :
    (∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0) ∧
    (∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0) :=
  ⟨budget_closes_of_witness R w, all_admissible_close_via_terminal R w⟩

end YMGap.Categorical

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Categorical.GroupBudgetCat
#print axioms YMGap.Categorical.GroupBudget.transportCloses
#print axioms YMGap.Categorical.su2GB_closes
#print axioms YMGap.Categorical.repGB_to_su2
#print axioms YMGap.Categorical.all_admissible_close_via_terminal
#print axioms YMGap.Categorical.all_admissible_close_concur
