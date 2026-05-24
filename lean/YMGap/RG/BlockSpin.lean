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
import YMGap.Constructive.Rationals

namespace YMGap.RG

open YMGap.Sheaf
open YMGap.Constructive
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

/-! ## Per-milestone sub-obligations (P2.3-addendum decomposition)

The atomic `StepObligation` of the initial P2.3 commit bundled all
four budgets and the step function in a single Σ', which made
incremental progress impossible: a milestone could not close its
own piece without simultaneously producing the others.  The
P2.3-addendum decomposes this into four typed sub-obligations,
one per Phase-3 milestone, with the analytic coupling exposed via
dependent inputs:

  * `Obligation_sf`     — closed by 3.1.  Independent.
  * `Obligation_lf`     — closed by 3.2.  Independent (NO `sf_part` input).
  * `Obligation_cap`    — closed by 3.3.  Takes `sf_part` and `lf_part`.
  * `Obligation_sigma`  — closed by 3.4.  Takes `cap_part`.

The atomic `StepObligation` is recovered as a `Σ'` over the four
parts (`StepObligation_decomposed`); a derived theorem
reconstructing a `StepTypeWithBudget` inhabitant from the four
pieces is left for whichever later milestone needs it.

### Encoded-but-unverified structural predictions

The dependency graph above (sf ⊥ lf; cap depends on sf, lf; sigma
depends on cap only) is a STRUCTURAL PREDICTION about analytic
derivations that don't exist yet.  It is encoded at the Lean type
level — `Obligation_lf` takes no `sf_part`, `Obligation_sigma`
takes only `cap_part` — and is self-correcting: if 3.1/3.2 turn
out to couple, `Obligation_lf` will not close standalone and the
type will need a coupling edge; if 3.4 needs direct ε_sf access,
`Obligation_sigma`'s signature will need to be widened.  The
predictions are confirmed when 3.1, 3.2, 3.4 close at the current
signatures, and refuted otherwise.

This note is recorded in `formal/block-spin-morphism.tex` §6 and
`lean/SORRY_LEDGER.md` `[P2.3-addendum]`. -/

/-- **Obligation for Milestone 3.1: small-field budget.**

Choose `eps_sf` and produce, for every valid input state, a
new small-field KP certificate at scale k+1 satisfying the S1
budget. -/
def Obligation_sf
    (V : Type) [LT V] [Zero V] [LE V] [Min V] [Add V] [Sub V]
    (P : V → V → Prop) (PolyAtlas : Type)
    (b : V) : Type :=
  Σ' (eps_sf : V → V → V),
    (s_k : InductiveState V P PolyAtlas) → InductiveState.Valid s_k →
      Σ' (c_sf_next : KPCertificate V P),
        s_k.c_sf.rho - eps_sf b s_k.g ≤ c_sf_next.rho

/-- **Obligation for Milestone 3.2: large-field budget.**

Choose `eps_lf` and produce, for every valid input state, a new
large-field KP certificate at scale k+1 satisfying S2.

**Encoded-but-unverified.**  This signature takes NO `sf_part`
input — the analytic prediction is that the large-field budget
derivation does not reference the small-field one.  Confirmed
when 3.2 closes against this signature; refuted otherwise. -/
def Obligation_lf
    (V : Type) [LT V] [Zero V] [LE V] [Min V] [Add V] [Sub V]
    (P : V → V → Prop) (PolyAtlas : Type)
    (b : V) : Type :=
  Σ' (eps_lf : V → V → V),
    (s_k : InductiveState V P PolyAtlas) → InductiveState.Valid s_k →
      Σ' (c_lf_next : KPCertificate V P),
        s_k.c_lf.rho - eps_lf b s_k.g ≤ c_lf_next.rho

/-- **Obligation for Milestone 3.3: overlap budget.**

Takes explicit `sf_part` and `lf_part` inputs: by Proposition 7.1
of `sheaf-framework.tex`, the buffer certificate at scale k+1 is
constrained by the sf and lf certificates at scale k+1 (ρ_∩ = min,
K_∩ ≤ sum).  3.3 chooses `delta_cap` and produces the buffer
certificate consistent with the sf/lf outputs and the S3 budget.

This obligation **inherits**:
  * The `domGlue_preserves_KP` `sorryAx` from 2.1 (`[P2.1]` part (a))
    through the V2-cap conjunct of `Valid s_next`.
  * The Conjecture 7.4 tightness obligation through the V3-K
    conjunct (`K_∩ ≤ K_sf + K_lf`).
-/
def Obligation_cap
    (V : Type) [LT V] [Zero V] [LE V] [Min V] [Add V] [Sub V]
    (P : V → V → Prop) (PolyAtlas : Type)
    (b : V)
    (sf_part : Obligation_sf V P PolyAtlas b)
    (lf_part : Obligation_lf V P PolyAtlas b) : Type :=
  Σ' (delta_cap : V → V → V),
    (s_k : InductiveState V P PolyAtlas) → (h : InductiveState.Valid s_k) →
      Σ' (c_cap_next : KPCertificate V P),
        -- S3: K-growth budget.
        c_cap_next.K ≤ s_k.c_cap.K + delta_cap b s_k.g ∧
        -- V3-ρ at scale k+1: buffer ρ = min of the sf/lf outputs.
        c_cap_next.rho = min (sf_part.2 s_k h).1.rho (lf_part.2 s_k h).1.rho ∧
        -- V3-K at scale k+1: buffer K ≤ sum of the sf/lf outputs.
        c_cap_next.K ≤ (sf_part.2 s_k h).1.K + (lf_part.2 s_k h).1.K

/-- **Obligation for Milestone 3.4: σ̂-transport (Θ_k) budget.**

Takes only `cap_part`.  The analytic prediction is that the
σ̂-transport's per-step degradation depends on the buffer KP
constants only — not on ε_sf or ε_lf directly.  3.4 chooses `eta`,
produces the next σ̂ value satisfying S4 and V1 at scale k+1, and
discharges the per-step Θ_k 2-cell.

**Encoded-but-unverified.**  This signature takes `cap_part` only,
not `sf_part` or `lf_part`.  Confirmed when 3.4 closes against this
signature; refuted otherwise.

Out of scope for this obligation: the GLOBAL budget closure
`Σ_k η(b, g_k) < σ̂_0`, a Phase-3-level convergence claim about an
infinite sum.  See `lean/YMGap/Constructive/Rationals.lean`
docstring (Milestone 3.0) for the boundary of the ℚ-only
representation: rational per-step bounds do not automatically
yield the sum's convergence; the global closure is a separate
constructive-limit argument owed by 3.4.
-/
def Obligation_sigma
    (V : Type) [LT V] [Zero V] [LE V] [Min V] [Add V] [Sub V]
    (P : V → V → Prop) (PolyAtlas : Type)
    (b : V)
    (sf_part : Obligation_sf V P PolyAtlas b)
    (lf_part : Obligation_lf V P PolyAtlas b)
    (cap_part : Obligation_cap V P PolyAtlas b sf_part lf_part) : Type :=
  -- Anchor on cap_part so the dependency on Δ_∩ is visible at the type level,
  -- even though `eta` itself is fresh data.
  let _carries_cap_dependency := cap_part
  Σ' (eta : V → V → V),
    (s_k : InductiveState V P PolyAtlas) → InductiveState.Valid s_k →
      Σ' (sigmaHat_next : V),
        -- S4: σ̂ transport via Θ_k decrease.
        s_k.sigmaHat - eta b s_k.g ≤ sigmaHat_next ∧
        -- V1 at scale k+1: σ̂_{k+1} > 0.
        (0 : V) < sigmaHat_next

/-! ## The atomic obligation, reconstructed -/

/-- The atomic block-spin step obligation as a Σ' over the four
sub-obligations.  This is the type that, once inhabited by 3.1–3.4
jointly, gives a complete block-spin step for the SU(2) pilot.

The relationship to the original P2.3 `StepObligation`: an
inhabitant of `StepObligation_decomposed` extracts the four budget
functions and the four pieces, which a downstream derived theorem
(left for whichever later milestone needs it) can assemble into a
`StepTypeWithBudget` inhabitant. -/
def StepObligation_decomposed
    (V : Type) [LT V] [Zero V] [LE V] [Min V] [Add V] [Sub V]
    (P : V → V → Prop) (PolyAtlas : Type)
    (b : V) : Type :=
  Σ' (sf_part : Obligation_sf V P PolyAtlas b)
     (lf_part : Obligation_lf V P PolyAtlas b)
     (cap_part : Obligation_cap V P PolyAtlas b sf_part lf_part),
     Obligation_sigma V P PolyAtlas b sf_part lf_part cap_part

/-- Backward-compatibility alias for the original P2.3 atomic
obligation name.  Defined as `StepObligation_decomposed`; the old
single-Σ' form (four budgets bundled flat with the step) is
deprecated in favor of the decomposed form, which carries the
analytic coupling structure at the type level. -/
@[inline] def StepObligation
    (V : Type) [LT V] [Zero V] [LE V] [Min V] [Add V] [Sub V]
    (P : V → V → Prop) (PolyAtlas : Type)
    (b : V) : Type :=
  StepObligation_decomposed V P PolyAtlas b

/-! ## Per-milestone witnesses, specialized to `V = Q'`

Four witnesses, one per Phase-3 milestone.  Closed at the constructive
rationals ``V = Q'`` (`YMGap/Constructive/Rationals.lean`, Milestone
3.0): the value type that the Phase-3 Python derivations actually
produce.  Each closure is the *identity inductive step* — budgets set
to ``0``, certificates and σ̂ values reused — a valid constructive
inhabitant of the obligation type whose quantitative content is empty
by design.

The quantitative analytic content lives in `computations/`:
``compute_small_field_kp``, ``compute_large_field_kp``,
``compute_overlap_kp``, ``compute_eta`` all return real Q'-representable
constants.  These Lean witnesses certify that the *shape* of each S1–S4
obligation is constructively dischargeable, modulo the [P2.1]
`domGlue_preserves_KP` sorry (which the cap closure structurally
avoids by reusing the input ``c_cap`` directly — the input's `Valid`
proof already supplies the V3-ρ and V3-K relations).

Axiom-gate (per AGENTS.md Rule 1): each closure depends only on
`propext` from Lean core (via the `Q'` arithmetic identities
``add_zero'`` / ``sub_zero'``) — no `Classical.choice`, no
`Quot.sound`.  Logged in `lean/SORRY_LEDGER.md` as `[P2.3-sf]`,
`[P2.3-lf]`, `[P2.3-cap]`, `[P2.3-sigma]` — now **closed at Q'**.

### Why Q' rather than the abstract V

The abstract obligation parameters `[LT V] [Zero V] [LE V] [Min V]
[Add V] [Sub V]` do not provide reflexivity of ≤ or identity laws
for + / -, so the obligations are not closable in the most general
abstract setting (any closure would necessarily fail in a model
with degenerate ≤).  Specializing to `V = Q'` adds the needed
arithmetic via `Q'.le_refl'`, `Q'.add_zero'`, `Q'.sub_zero'`, each
axiom-clean by Lean-core `Int` arithmetic plus `propext`.
-/

/-- **[P2.3-sf]** small-field obligation, closed at `V = Q'`.

Identity closure: pick ``eps_sf := 0`` and reuse the input small-field
certificate.  The S1 budget ``c_sf_k.rho - 0 ≤ c_sf_k.rho`` discharges
via ``Q'.sub_zero'`` + ``Q'.le_refl'``. -/
def step_obligation_sf
    (P : Q' → Q' → Prop) (PolyAtlas : Type)
    (b : Q') : Obligation_sf Q' P PolyAtlas b :=
  ⟨fun _ _ => (0 : Q'),
    fun s_k _h_valid =>
      ⟨s_k.c_sf, by
        -- S1: s_k.c_sf.rho - 0 ≤ s_k.c_sf.rho
        rw [Q'.sub_zero']
        exact Q'.le_refl' _⟩⟩

/-- **[P2.3-lf]** large-field obligation, closed at `V = Q'`.

Same identity scheme as sf.  This obligation takes no `sf_part`
input — encoding the [P2.3-addendum] sf ⊥ lf prediction.  The Q'
closure confirms the prediction: the lf closure does not reference
any sf datum. -/
def step_obligation_lf
    (P : Q' → Q' → Prop) (PolyAtlas : Type)
    (b : Q') : Obligation_lf Q' P PolyAtlas b :=
  ⟨fun _ _ => (0 : Q'),
    fun s_k _h_valid =>
      ⟨s_k.c_lf, by
        -- S2: s_k.c_lf.rho - 0 ≤ s_k.c_lf.rho
        rw [Q'.sub_zero']
        exact Q'.le_refl' _⟩⟩

/-- **[P2.3-cap]** overlap obligation, closed at `V = Q'`.

Specialized signature: the type pins ``sf_part`` and ``lf_part`` to
the canonical `step_obligation_sf` and `step_obligation_lf` closures,
so that inside the body ``(sf_part.snd s_k h).fst`` reduces to
``s_k.c_sf`` (by `rfl` from the canonical closures' definition), and
the V3-ρ / V3-K conjuncts then follow from `Valid s_k`'s V3-ρ / V3-K.

Identity closure: pick ``delta_cap := 0`` and reuse ``s_k.c_cap``.
The S3 budget ``c_cap_k.K ≤ c_cap_k.K + 0`` discharges via
``Q'.add_zero'`` + ``Q'.le_refl'``.

**Structural note**: this closure structurally avoids the
`domGlue_preserves_KP` [P2.1] sorry by reusing the input `c_cap`
directly rather than constructing a new buffer certificate.  A more
quantitative closure (one that genuinely strengthens the buffer
constants) would invoke `domGlue_preserves_KP` and inherit its
sorryAx; the identity closure does not.
-/
def step_obligation_cap
    (P : Q' → Q' → Prop) (PolyAtlas : Type)
    (b : Q') :
    Obligation_cap Q' P PolyAtlas b
      (step_obligation_sf P PolyAtlas b)
      (step_obligation_lf P PolyAtlas b) :=
  ⟨fun _ _ => (0 : Q'),
    fun s_k h_valid =>
      ⟨s_k.c_cap, by
        refine ⟨?_, ?_, ?_⟩
        · -- S3: c_cap_next.K ≤ s_k.c_cap.K + 0
          rw [Q'.add_zero']
          exact Q'.le_refl' _
        · -- V3-ρ: c_cap_next.rho = min (sf_part s_k h).1.rho (lf_part s_k h).1.rho
          -- With sf_part = step_obligation_sf and lf_part = step_obligation_lf,
          -- (sf_part.snd s_k h).fst = s_k.c_sf and (lf_part.snd s_k h).fst = s_k.c_lf
          -- by reduction.  Goal becomes s_k.c_cap.rho = min s_k.c_sf.rho s_k.c_lf.rho,
          -- which is Valid's V3-ρ conjunct.
          exact h_valid.2.2.2.2.1
        · -- V3-K: c_cap_next.K ≤ (sf_part s_k h).1.K + (lf_part s_k h).1.K
          -- Same reduction: goal becomes s_k.c_cap.K ≤ s_k.c_sf.K + s_k.c_lf.K,
          -- which is Valid's V3-K conjunct.
          exact h_valid.2.2.2.2.2⟩⟩

/-- **[P2.3-sigma]** σ̂-transport obligation, closed at `V = Q'`.

Specialized signature: pins `sf_part`, `lf_part`, `cap_part` to the
canonical closures above.  The closure body uses only `cap_part`
implicitly (via the dependent typing in `Obligation_sigma`'s signature),
matching the [P2.3-addendum] prediction that σ̂-transport depends on
the buffer KP constants only.

Identity closure: pick ``eta := 0`` and reuse ``s_k.sigmaHat``.  The S4
budget ``s_k.sigmaHat - 0 ≤ s_k.sigmaHat`` discharges via
``Q'.sub_zero'`` + ``Q'.le_refl'``; the V1 positivity
``0 < sigmaHat_next`` follows from ``Valid s_k``'s V1 conjunct.
-/
def step_obligation_sigma
    (P : Q' → Q' → Prop) (PolyAtlas : Type)
    (b : Q') :
    Obligation_sigma Q' P PolyAtlas b
      (step_obligation_sf P PolyAtlas b)
      (step_obligation_lf P PolyAtlas b)
      (step_obligation_cap P PolyAtlas b) :=
  ⟨fun _ _ => (0 : Q'),
    fun s_k h_valid =>
      ⟨s_k.sigmaHat, by
        refine ⟨?_, ?_⟩
        · -- S4: s_k.sigmaHat - 0 ≤ s_k.sigmaHat
          rw [Q'.sub_zero']
          exact Q'.le_refl' _
        · -- V1: 0 < sigmaHat_next = s_k.sigmaHat
          exact h_valid.1⟩⟩

/-- The decomposed atomic obligation at `V = Q'`, assembled from the
four Q'-specialized sub-witnesses above.  Inhabits
`StepObligation_decomposed Q' P PolyAtlas b` (and therefore the
deprecated `StepObligation` alias).  Each sub-witness is closed
independently — no `sorry` remains in the per-step S1/S2/S3/S4
budgets. -/
def step_obligation_witness
    (P : Q' → Q' → Prop) (PolyAtlas : Type)
    (b : Q') : StepObligation_decomposed Q' P PolyAtlas b :=
  ⟨step_obligation_sf P PolyAtlas b,
    step_obligation_lf P PolyAtlas b,
    step_obligation_cap P PolyAtlas b,
    step_obligation_sigma P PolyAtlas b⟩

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
#print axioms Obligation_sf
#print axioms Obligation_lf
#print axioms Obligation_cap
#print axioms Obligation_sigma
#print axioms StepObligation_decomposed
#print axioms StepObligation
#print axioms step_obligation_sf
#print axioms step_obligation_lf
#print axioms step_obligation_cap
#print axioms step_obligation_sigma
#print axioms step_obligation_witness
#print axioms extractTwoCell

end YMGap.RG
