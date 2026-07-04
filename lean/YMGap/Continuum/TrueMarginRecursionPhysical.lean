/-
Track B / R2 — THE **TRUE DIMENSIONLESS MARGIN** recursion and its adequacy for
the shared spacing-uniform floor.

# What this module is about — and the honesty of it

The existing `TrueMarginRecursion` (`UniformCouplingFromAF.lean`) is, by its own
§4/§5 flags, a **multiplicative-only survival surrogate**: its `physGap` is the
survival product `∏(1−δ_ren)`, NOT the true margin `m_lat(a_k)/a_k`.  Every
inhabited floor surrogate in the codebase (`DefectGapRecursion.recursion`, the
`ContinuumClosureProgram` recursion, `tunedCRealFloor`) is likewise purely
multiplicative: it carries a per-step defect `δ_k` but NO additive erosion term.

The load-bearing structural fact this module states honestly is that the **true**
dimensionless margin

    margin k  =  m_lat(a_k) / a_k          (`Q'.divPos`, `a_k > 0`)

obeys an **ADDITIVE-erosion** step law

    margin (k+1)  ≥  (1 − δ_k) · margin k  −  ε_k .

For an additive recursion, summability of the budget `∑(δ_k + ε_k)` ALONE does
NOT force a positive limit; positivity holds only under an extra
**anchor-dominates-budget** condition (`margin 0` beats the accumulated `ε`).
Hence the positive continuum limit must be carried as DATA, not derived — and the
un-sourced additive `ε_k` + anchor-dominates-budget inequality is the real, strictly
sharper, open residual behind the multiplicative surrogate.

# What is stated / proved here (axiom-clean; Rule 8 Type-level data)

  * `TrueMarginRecursionPhysical` — the honest named residual (a `Type`, DELIBERATELY
    UNINHABITED here): the definitional `margin_def` via `Q'.divPos`, the ADDITIVE
    `step` law, a `GradedTowerSummable`-style `budget_modulus`
    (`tailSum … ≤ C·pot 2 N`, never a bare `Summable`), and the positive continuum
    limit carried as Type-level witness data (`floorWitness`, `floorWitness_pos`,
    `floorWitness_le`, `lowerBound`) — the anchor-dominates-budget conclusion.

  * `le_of_leEv_ofQ'` — the one trivial glue lemma (pure `Q'`, no analysis):
    `leEv (ofQ' a) (ofQ' b) → a ≤ b`, collapsing the eventual order on two rational
    embeddings to the plain rational order.

  * `uniformSpacingFloor_of_trueMarginPhysical` — THE ADEQUACY LEMMA (the gate a
    downstream milestone consumes): a `TrueMarginRecursionPhysical` genuinely
    supplies the shared `QFloor` on its `margin`, feeding the canonical
    `UniformSpacingFloor` interface unchanged.

  * `delta_isPositive` — the derived accessor exhibiting the carried limit witness
    as a `CReal.IsPositive Δ`, honoring the "positive continuum limit" narrative.

The analytic discharge (inhabiting `step` for the non-abelian multi-link 4D
block-spin margin AND proving anchor-dominates-budget) is out of scope; the
structure is NOT inhabited here.
-/
import YMGap.Continuum.UnifiedContinuumFloor
import YMGap.Continuum.SummableInverseSquare
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.CRealComplete
import YMGap.Continuum.RCDistBridge

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.UnifiedContinuumFloor

/-! ## 1. The trivial rational-collapse glue lemma

`leEv (ofQ' a) (ofQ' b)` is, since `(ofQ' q).approx n = q` for all `n`, precisely
`∀ ε > 0, ∃ N, ∀ n ≥ N, a ≤ b + ε`.  Instantiating at any single `n` gives
`∀ ε > 0, a ≤ b + ε`, whence the plain rational order `a ≤ b` by the Archimedean
upper bound `Q'.le_of_forall_pos_add`.  Zero analytic content. -/

/-- **Rational-collapse glue.**  The eventual order on two rational embeddings
collapses to the plain `Q'` order: `leEv (ofQ' a) (ofQ' b) ⟹ a ≤ b`. -/
theorem le_of_leEv_ofQ' {a b : Q'}
    (h : CReal.leEv (CReal.ofQ' a) (CReal.ofQ' b)) : a ≤ b := by
  refine Q'.le_of_forall_pos_add (fun ε hε => ?_)
  obtain ⟨N, hN⟩ := h ε hε
  have hb := hN N (Nat.le_refl N)
  -- (ofQ' a).approx N = a, (ofQ' b).approx N = b  (both `rfl`/simp)
  simpa using hb

/-! ## 2. The honest named residual — the TRUE margin recursion

`TrueMarginRecursionPhysical` is a `Type` (Rule 8) and is DELIBERATELY UNINHABITED
here (the physical `step` / anchor-dominates-budget instance for the non-abelian 4D
block-spin margin is the open input).  It is NOT `True` and NOT a multiplicative
surrogate: the `margin_def`, the ADDITIVE `step`, the summability `budget_modulus`,
and the carried positive limit are all genuine content. -/

/-- **THE TRUE DIMENSIONLESS-MARGIN RECURSION (honest named residual, `Type`).**

The margin `margin k = m_lat(a_k)/a_k` (`margin_def`, via `Q'.divPos`) obeys the
ADDITIVE-erosion step `margin (k+1) ≥ (1−δ_k)·margin k − ε_k` (`step`), with a
`GradedTowerSummable`-shaped tail modulus for the `(δ+ε)` budget (`budget_modulus`,
NOT a bare `Summable`), and the positive continuum limit carried as Type-level
witness DATA (`floorWitness`, `floorWitness_pos`, `floorWitness_le`, `lowerBound`) —
the anchor-dominates-budget conclusion the additive law cannot derive from
summability alone.  UNINHABITED here. -/
structure TrueMarginRecursionPhysical : Type where
  /-- The lattice mass `m_lat(a_k)` at spacing `a_k`. -/
  massLat : Nat → Q'
  /-- The lattice spacing `a_k`. -/
  spacing : Nat → Q'
  /-- The spacing is strictly positive at every step. -/
  spacing_pos : ∀ k, (0 : Q') < spacing k
  /-- The dimensionless margin `m_lat(a_k)/a_k` — NOT a survival product. -/
  margin : Nat → Q'
  /-- The margin is definitionally the physical ratio `m_lat(a_k)/a_k`. -/
  margin_def : ∀ k, margin k = Q'.divPos (massLat k) (spacing k) (spacing_pos k)
  /-- Per-step multiplicative defect `δ_k`. -/
  δ : Nat → Q'
  /-- Per-step ADDITIVE erosion `ε_k` (absent in every multiplicative surrogate). -/
  ε : Nat → Q'
  /-- The defect is nonnegative. -/
  δ_nonneg : ∀ k, (0 : Q') ≤ δ k
  /-- The defect does not exceed `1`. -/
  δ_le_one : ∀ k, δ k ≤ (1 : Q')
  /-- The erosion is nonnegative. -/
  ε_nonneg : ∀ k, (0 : Q') ≤ ε k
  /-- **The ADDITIVE-erosion step law** — the whole point: the `−ε_k` term is what
  distinguishes the true margin from the multiplicative survival surrogate. -/
  step : ∀ k, ((1 : Q') - δ k) * margin k - ε k ≤ margin (k + 1)
  /-- The tail-modulus constant for the `(δ+ε)` budget. -/
  budgetTailConst : Q'
  /-- **Rule-8.3 explicit tail-rate witness** (mirrors `GradedTowerSummable`), NOT a
  bare `Summable`: every window of the `(δ+ε)` budget is `≤ C·pot 2 N`. -/
  budget_modulus : ∀ N M,
      tailSum (fun k => δ k + ε k) N M ≤ budgetTailConst * pot 2 (by decide) N
  /-- The positive continuum-limit margin (as a `CReal`). -/
  Δ : CReal
  /-- The positive rational witness beneath `Δ` (Type-level data, not Prop-∃). -/
  floorWitness : Q'
  /-- The witness is strictly positive (anchor-dominates-budget, carried as data). -/
  floorWitness_pos : (0 : Q') < floorWitness
  /-- The witness bounds `Δ` from below at the `CReal` level. -/
  floorWitness_le : CReal.ofQ' floorWitness ≤ Δ
  /-- `Δ` lies below the margin at EVERY step simultaneously (uniform `∀k`). -/
  lowerBound : ∀ k, CReal.leEv Δ (CReal.ofQ' (margin k))

/-! ## 3. The derived positivity accessor -/

/-- The carried limit `Δ` is `CReal`-positive, witnessed by `floorWitness`.  This
exhibits the Type-level data of `TrueMarginRecursionPhysical` as the usual
`CReal.IsPositive` narrative of a positive continuum-limit margin. -/
theorem delta_isPositive (T : TrueMarginRecursionPhysical) :
    CReal.IsPositive T.Δ :=
  ⟨T.floorWitness, T.floorWitness_pos, T.floorWitness_le⟩

/-! ## 4. THE ADEQUACY LEMMA — the gate the downstream milestone consumes

A `TrueMarginRecursionPhysical` genuinely supplies the shared `QFloor` on its
`margin`: `floorWitness` is a strictly-positive rational lying (via the chain
`leEv (ofQ' floorWitness) Δ  ∘  leEv Δ (ofQ' (margin k))` collapsed by
`le_of_leEv_ofQ'`) below `margin k` at EVERY scale `k` at once.  This is exactly
the canonical `UniformSpacingFloor` interface of `UnifiedContinuumFloor`, feeding
`unified_continuum_gap` and every wall consumer unchanged. -/

/-- **ADEQUACY.**  The true physical margin supplies the shared spacing-uniform
floor: `TrueMarginRecursionPhysical → QFloor margin`.  A `def` (the conclusion is
`Type`-level `UniformSpacingFloor` data, Rule 2: Σ not ∃). -/
def uniformSpacingFloor_of_trueMarginPhysical
    (T : TrueMarginRecursionPhysical) : QFloor T.margin where
  floor := T.floorWitness
  floor_pos := T.floorWitness_pos
  bound := fun k =>
    le_of_leEv_ofQ'
      (CReal.leEv_trans (CReal.leEv_of_le T.floorWitness_le) (T.lowerBound k))

end YMGap.Continuum
