/-
The block-spin step: refined type and proof obligations.
Milestone 2.3.

Mirrors `formal/block-spin-morphism.tex` Definitions 4.1 (Θ_k),
5.1 (budget functions), 5.2 (StepTypeWithBudget), 6.1 (obligation).

Constructive contract (`lean/AGENTS.md`):

  - The refined step type and the obligation type are exposed as
    `def`s returning Lean `Type`s.  No term inhabiting them is
    constructed here — that is the joint job of Milestones 3.1–3.4.
  - The placeholder inhabitant `step_obligation_witness` is a
    sorry'd `def` of type `StepObligation`, logged in
    `SORRY_LEDGER.md` as `[P2.3]`.  Constructively phrased
    (Σ-typed); never to be closed classically.
  - Witness-bearing scalars (σ̂, ρ, K, η, ε, Δ) inhabit an abstract
    value type `V` with `[LT V] [Zero V] [LE V] [Min V] [Add V]
    [Sub V]`.  Per Rule 3, no Mathlib `ℝ`, no Lean-core `Rat`.
  - The 2-cell Θ_k is a separate `structure` per work_plan 2.3's
    open-question recommendation, not a field on InductiveState.

Scope: per-step only.  No conjunct of the refined type
quantifies over `k` or sums over scales.  Global budget closure
(Σ_k η < σ̂_0, Σ_k Δ_∩ < ∞, inf_k σ̂_k > 0) is Phase 3 / Milestone
3.4 and is NOT stated anywhere in this file.
-/

import YMGap.RG.InductiveState

namespace YMGap.RG

open YMGap.Sheaf
open InductiveState

/-! ## The 2-cell Θ_k as a separate typed object

Mirrors `formal/block-spin-morphism.tex` Definition 4.1.  A
Θ_k-witness bundles (σ_in, η_k, σ_out, decrease proof) for the
dimensional-rescaling 2-cell of `docs/outline.md` §10.4.

Separate from `BlockSpinStep` per work_plan 2.3's open-question
recommendation: ``a separate object for clarity.'' -/

/-- The 2-cell Θ_k: a σ̂-transport witness bundling input and
output renormalized string tensions with the per-step degradation
budget η_k and a proof of the decrease inequality. -/
structure TwoCellTheta (V : Type) [LE V] [Sub V] where
  /-- Input renormalized string tension `σ̂_k`. -/
  sigma_in  : V
  /-- Per-step degradation budget `η_k = η(b, g_k)`. -/
  eta_k     : V
  /-- Output renormalized string tension `σ̂_{k+1}`. -/
  sigma_out : V
  /-- The decrease inequality `σ_in - η_k ≤ σ_out`. -/
  decrease  : sigma_in - eta_k ≤ sigma_out

namespace TwoCellTheta

variable {V : Type} [LE V] [Sub V]

/-- Build a `TwoCellTheta` from the four pieces of data. -/
@[inline] def mk' (sigma_in eta_k sigma_out : V)
    (h : sigma_in - eta_k ≤ sigma_out) : TwoCellTheta V :=
  ⟨sigma_in, eta_k, sigma_out, h⟩

end TwoCellTheta

/-! ## The refined block-spin step type with budget

Mirrors `formal/block-spin-morphism.tex` Definition 5.2.  Carries
the four per-step conditions S1–S4 as type-level constraints,
abstract over the budget functions (ε_sf, ε_lf, Δ_∩, η).

Each S_i is a single inequality at one scale-k input / scale-(k+1)
output.  No conjunct mentions Σ_k or "for all k".  Output positivity
of σ̂_{k+1} is structurally provided by the codomain demanding
`Valid s_next` (via V1); S4 is just the decrease inequality.

The conjuncts in the Σ'-return are, in order:
  - `Valid s_next`         — V1 ∧ V2 ∧ V3 at scale k+1
  - `s_next.k = s_k.k + 1` — scale increment
  - S1: ρ_sf budget
  - S2: ρ_lf budget
  - S3: K_∩ budget
  - S4: σ̂ budget (= Θ_k decrease inequality)
-/

/-- The type of a block-spin step at block scale `b` and budget
functions `(eps_sf, eps_lf, delta_cap, eta)`.  A term inhabiting
this type takes a `Valid` input state to a `Valid` output state
with all four per-step degradation conditions S1–S4 satisfied.

This is the refined type the bare 2.2 `StepType` evolves into for
Milestone 2.3.  2.3 states the type; 3.1–3.4 jointly produce a
term. -/
def StepTypeWithBudget
    (V : Type) [LT V] [Zero V] [LE V] [Min V] [Add V] [Sub V]
    (P : V → V → Prop) (PolyAtlas : Type)
    (b : V)
    (eps_sf eps_lf delta_cap eta : V → V → V) : Type :=
  (s_k : InductiveState V P PolyAtlas) → Valid s_k →
    Σ' (s_next : InductiveState V P PolyAtlas),
      Valid s_next ∧
      s_next.k = s_k.k + 1 ∧
      -- S1: small-field ρ-budget
      (s_k.c_sf.rho - eps_sf b s_k.g ≤ s_next.c_sf.rho) ∧
      -- S2: large-field ρ-budget
      (s_k.c_lf.rho - eps_lf b s_k.g ≤ s_next.c_lf.rho) ∧
      -- S3: overlap K-budget
      (s_next.c_cap.K ≤ s_k.c_cap.K + delta_cap b s_k.g) ∧
      -- S4: string-tension budget (= Θ_k decrease)
      (s_k.sigmaHat - eta b s_k.g ≤ s_next.sigmaHat)

/-! ## The obligation: what 3.x must produce -/

/-- The 2.3 obligation, as a Σ'-typed statement.

A term of this type exhibits, for some choice of budget functions,
a step inhabiting `StepTypeWithBudget`.  Discharging this
obligation for the SU(2) pilot is the joint content of:

  * Milestone 3.1 — supplies `eps_sf` and the sf-cert pushforward;
  * Milestone 3.2 — supplies `eps_lf` and the lf-cert pushforward;
  * Milestone 3.3 — supplies `delta_cap` and the buffer pushforward,
    inheriting the 2.1 `domGlue_preserves_KP` sorry through V2-cap
    and the Conjecture 7.4 tightness obligation through V3-K;
  * Milestone 3.4 — supplies `eta` and proves the σ̂-transport S4
    (= Θ_k); also responsible for the Phase-3 global budget
    closure `Σ_k η < σ̂_0`, which is OUT OF SCOPE here.

The obligation is parametrized by `b` (block scale, fixed
program-level by outline §6.1). -/
def StepObligation
    (V : Type) [LT V] [Zero V] [LE V] [Min V] [Add V] [Sub V]
    (P : V → V → Prop) (PolyAtlas : Type)
    (b : V) : Type :=
  Σ' (eps_sf eps_lf delta_cap eta : V → V → V),
    StepTypeWithBudget V P PolyAtlas b eps_sf eps_lf delta_cap eta

/-- The unwritten 2.3 obligation, placeholder for Milestones 3.1–3.4.

`sorry`'d on purpose; logged in `lean/SORRY_LEDGER.md` as `[P2.3]`.
Per AGENTS.md Rule 6, this `sorry` must not be closed classically;
closure requires a constructive term against concrete budget
functions from 3.1–3.4.

`#print axioms` will report `depends on axioms: [sorryAx]` here —
the explicit signal of an unclosed constructive obligation, not a
silent classical lapse. -/
def step_obligation_witness
    (V : Type) [LT V] [Zero V] [LE V] [Min V] [Add V] [Sub V]
    (P : V → V → Prop) (PolyAtlas : Type)
    (b : V) : StepObligation V P PolyAtlas b := by
  -- SORRY[P2.3]: block-spin step inhabitation, owed by 3.1-3.4
  sorry

/-! ## Helper: extracting the 2-cell from an S4 proof -/

/-- Given an `S4` proof from a step's output, package it as a
`TwoCellTheta`.  This is the bridge between the inline S4 inequality
inside `StepTypeWithBudget` and the separate-typed-object form. -/
def extractTwoCell
    {V : Type} [LT V] [Zero V] [LE V] [Min V] [Add V] [Sub V]
    {P : V → V → Prop} {PolyAtlas : Type}
    {b : V} {eta : V → V → V}
    (s_k s_next : InductiveState V P PolyAtlas)
    (h_S4 : s_k.sigmaHat - eta b s_k.g ≤ s_next.sigmaHat) :
    TwoCellTheta V :=
  TwoCellTheta.mk' s_k.sigmaHat (eta b s_k.g) s_next.sigmaHat h_S4

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms TwoCellTheta
#print axioms TwoCellTheta.mk'
#print axioms StepTypeWithBudget
#print axioms StepObligation
#print axioms step_obligation_witness
#print axioms extractTwoCell

end YMGap.RG
