/-
Track A / R2 — Round J of the fusion box log-concavity node: the DIAGONAL (3/4) MINOR
RESERVE atom of the central-autoconvolution log-concavity margin (`AutoconvReserveResidual`),
proved symbolically for all modes, together with an HONEST machine-checked CORRECTION of the
naive "summand-wise" route to the reserve.

# What this module adds (read first — load-bearing honesty)

Round I reduced Round H's `AutoconvBumpBounds` to the SINGLE open field
`AutoconvReserveResidual.reserve`,

    (1 + 31/225)·H0auto(s)·H0auto(s+2)  ≤  H0auto(s+1)²        (uniform in `N, s`),

with `256/225 = (16/15)²` the two-leg square of Round I's geometric constant.  A natural
attack expands the central-autoconvolution defect `H0auto(s+1)² − H0auto(s)·H0auto(s+2)` as
a Menon convolution defect and hopes to write it as a sum of MANIFESTLY nonnegative terms:
a DIAGONAL part (`p = q`) carrying the factor-4 Casimir reserve, plus an OFF-DIAGONAL part
paired as symmetrized `2×2` minors.  Round J supplies the diagonal atom in full and shows —
machine-checked — that the off-diagonal part is NOT sign-definite, so the naive summand
route does NOT close the reserve (the wall is genuine, not a bookkeeping gap).

ROUND-J DELIVERABLE 1 (the diagonal (3/4) minor reserve — PROVED, symbolic, all `s`).
  * `coeffW_diagReserve` — the diagonal reserve in additive form: for `0 ≤ w ≤ 1/2`,
        (3/4)·c_{s+1}²  +  c_s·c_{s+2}   ≤   c_{s+1}²,
    i.e. the diagonal minor `δ_s := c_{s+1}² − c_s·c_{s+2}` has strength `δ_s ≥ (3/4)·c_{s+1}²`.
    This is exactly `1 − 1/4` of the mode square, the (3/4)=(1−K⁻¹) Casimir reserve at `K=4`,
    read off `coeffW_superLogConcave` (`c_s·c_{s+2} ≤ (1/4)·c_{s+1}²`).  It is the diagonal
    (`p=q`) contribution the Menon autoconvolution defect identity would consume.
  * `coeffW_diagMinor_reserve` — the same fact in the `X + -Y` minor form
        (3/4)·c_{s+1}²  ≤  c_{s+1}²  +  −(c_s·c_{s+2}),
    the shape the defect identity pairs against the off-diagonal block.

ROUND-J DELIVERABLE 2 (the honest correction — the summand route provably does NOT close it).
  * `offMinor_wrong_direction` — a machine-checked refutation of the naive off-diagonal
    summand bound.  A summand-wise proof of the reserve would pair each off-diagonal Menon
    term `c_m·c_{n+2} + c_n·c_{m+2}` against `2·c_{m+1}·c_{n+1}` and hope both legs satisfy
    `c_·c_· ≤ c_{·+1}·c_{·+1}`.  At the true theta weight (`w = 1/2`, `(m,n) = (0,2)`) the
    second leg is
        c_2·c_2  ≤  c_3·c_1        — FALSE  (`c_2² = 9/65536 > 2/65536 = c_1·c_3`).
    For `n ≥ m+2` the pair `{c_n, c_{m+2}}` is LESS spread than `{c_{n+1}, c_{m+1}}`, so
    log-concavity makes it LARGER, not smaller.  Hence the symmetrized off-diagonal minor is
    NOT `≥ 0` in general, and the reserve is not a sum of manifestly nonnegative summands.
  * `symMinor`, `symMinor_can_be_negative` — the full symmetrized off-diagonal minor
    `T(m,n) = 2c_{m+1}c_{n+1} − c_m c_{n+2} − c_n c_{m+2}` and a decidable witness that it is
    `< 0` at `w = 1/2`, `(m,n) = (0,2)`.  This is the exact analogue of Round D's
    `bracket_can_be_negative` for the autoconvolution reserve.

# HONESTY — what is NOT closed

`AutoconvReserveResidual w` (Round I) remains NAMED-OPEN; Round J does NOT inhabit it, and
the A1 strand reindex remains a threaded hypothesis.  What Round J DOES prove is the diagonal
factor-`(3/4)` minor reserve (all `s`, symbolic `w ≤ 1/2`) and the machine-checked fact that
the off-diagonal block is genuinely indefinite — so the wall is real: the reserve requires
an AGGREGATE cancellation (the `QuadGershgorinClosure` / heat-kernel local-CLT content), not
a summand-wise nonnegativity.  This corrects the naive summand plan and sharpens the residual;
it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`coeffW_superLogConcave` lemmas, small
`Q'`-algebra congruences, and `decide` on closed concrete-rational facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only
(the `decide` refutations depend on NO axioms).  No `Classical.*`, no `native_decide`, no
`sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionCoreStepRoundI

namespace YMGap.Continuum.FusionCoreStepRoundJ

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundE
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionCoreStepRoundI

/-- The diagonal Casimir reserve constant `3/4 = 1 − 1/4` (the `(1 − K⁻¹)` minor strength
at `K = 4`). -/
abbrev qq34 : Q' := Q'.mkPos 3 4 (by decide)

/-! ## 0. A small `Q'` algebra helper -/

/-- **`le_add_neg_of_add_le`** — rearrange `a + Y ≤ X` into the minor (`X + -Y`) form
`a ≤ X + -Y`.  Add `-Y` to both sides and cancel `Y + -Y ≃ 0`. -/
theorem le_add_neg_of_add_le {a Y X : Q'} (h : a + Y ≤ X) : a ≤ X + -Y := by
  have hstep : (a + Y) + -Y ≤ X + -Y := Q'.add_le_add h (Q'.le_refl' (-Y))
  have e : ((a + Y) + -Y).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a Y (-Y)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (Y + -Y) 0 (Q'.add_neg_self_eqv Y)) ?_
    exact q_add_zero_eqv a
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv e) hstep

/-! ## 1. The diagonal (3/4) minor reserve -/

/-- **`coeffW_diagReserve` — the diagonal (3/4) minor reserve (additive form).**
For `0 ≤ w ≤ 1/2` and every mode `s`,

    (3/4)·(c_{s+1}·c_{s+1})  +  c_s·c_{s+2}   ≤   c_{s+1}·c_{s+1}.

Equivalently the diagonal minor `δ_s = c_{s+1}² − c_s·c_{s+2}` has reserve `δ_s ≥ (3/4)c_{s+1}²`.
PROOF.  `coeffW_superLogConcave` gives `c_s·c_{s+2} ≤ (1/4)·c_{s+1}²`; adding `(3/4)·c_{s+1}²`
to both sides and `(3/4 + 1/4) ≃ 1` closes it. -/
theorem coeffW_diagReserve {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (s : Nat) :
    qq34 * (coeffW w (s + 1) * coeffW w (s + 1)) + coeffW w s * coeffW w (s + 2)
      ≤ coeffW w (s + 1) * coeffW w (s + 1) := by
  -- `X := c_{s+1}²`, `Y := c_s·c_{s+2}`, with `Y ≤ (1/4)·X` from super-log-concavity.
  have h : coeffW w s * coeffW w (s + 2)
      ≤ quarter * (coeffW w (s + 1) * coeffW w (s + 1)) :=
    coeffW_superLogConcave hw0 hw12 s
  have hstep :
      qq34 * (coeffW w (s + 1) * coeffW w (s + 1)) + coeffW w s * coeffW w (s + 2)
        ≤ qq34 * (coeffW w (s + 1) * coeffW w (s + 1))
          + quarter * (coeffW w (s + 1) * coeffW w (s + 1)) :=
    Q'.add_le_add (Q'.le_refl' _) h
  -- `(3/4)·X + (1/4)·X ≃ X`
  have e : (qq34 * (coeffW w (s + 1) * coeffW w (s + 1))
        + quarter * (coeffW w (s + 1) * coeffW w (s + 1))).eqv
      (coeffW w (s + 1) * coeffW w (s + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv qq34 quarter (coeffW w (s + 1) * coeffW w (s + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (qq34 + quarter) 1 _ (by decide)) ?_
    exact Q'.one_mul_eqv _
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv e)

/-- **`coeffW_diagMinor_reserve` — the diagonal reserve in `X + -Y` minor form.**

    (3/4)·(c_{s+1}·c_{s+1})   ≤   (c_{s+1}·c_{s+1})  +  −(c_s·c_{s+2}).

The shape the Menon autoconvolution defect identity pairs against the off-diagonal block. -/
theorem coeffW_diagMinor_reserve {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (s : Nat) :
    qq34 * (coeffW w (s + 1) * coeffW w (s + 1))
      ≤ coeffW w (s + 1) * coeffW w (s + 1) + -(coeffW w s * coeffW w (s + 2)) :=
  le_add_neg_of_add_le (coeffW_diagReserve hw0 hw12 s)

/-! ## 2. The honest correction — the off-diagonal block is NOT sign-definite -/

/-- The full symmetrized off-diagonal Menon minor
`T(m,n) = 2·c_{m+1}·c_{n+1} − c_m·c_{n+2} − c_n·c_{m+2}` (in `X + -Y` form), the pairing a
naive summand-wise proof of the reserve would need `≥ 0`. -/
def symMinor (w : Q') (m n : Nat) : Q' :=
  (coeffW w (m + 1) * coeffW w (n + 1) + coeffW w (m + 1) * coeffW w (n + 1))
    + -(coeffW w m * coeffW w (n + 2) + coeffW w n * coeffW w (m + 2))

/-- **`offMinor_wrong_direction` — the naive off-diagonal leg is FALSE.**  A summand-wise
proof of the reserve pairs `c_n·c_{m+2}` against `c_{n+1}·c_{m+1}` and hopes for `≤`.  At the
true theta weight (`w = 1/2`, `(m,n) = (0,2)`) this leg reads `c_2·c_2 ≤ c_3·c_1`, which is
FALSE: `c_2² = 9/65536 > 2/65536 = c_1·c_3` (for `n ≥ m+2` the pair `{c_n, c_{m+2}}` is LESS
spread than `{c_{n+1}, c_{m+1}}`, so log-concavity makes it LARGER).  Machine-checked. -/
theorem offMinor_wrong_direction :
    ¬ (coeffW wH 2 * coeffW wH 2 ≤ coeffW wH 3 * coeffW wH 1) := by decide

/-- **`symMinor_can_be_negative` — the symmetrized off-diagonal minor is indefinite.**  At
`w = 1/2`, `(m,n) = (0,2)` the pairing `T(0,2) = 2·c_1·c_3 − c_0·c_4 − c_2·c_2` is `< 0`
(`= −1285/16777216`).  Hence the autoconvolution reserve is NOT a sum of manifestly
nonnegative summands: the off-diagonal block must be dominated by an AGGREGATE cancellation
(the `QuadGershgorinClosure` / heat-kernel local-CLT content), not summand-wise.  The exact
analogue of `bracket_can_be_negative` for the reserve.  Machine-checked (no axioms). -/
theorem symMinor_can_be_negative : ¬ ((0 : Q') ≤ symMinor wH 0 2) := by decide

/-! ## 3. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`; the `decide` refutations depend
on NO axioms):
  * `le_add_neg_of_add_le` — the `a + Y ≤ X ⟹ a ≤ X + -Y` rearrangement.
  * `coeffW_diagReserve`, `coeffW_diagMinor_reserve` — the diagonal factor-`(3/4)` minor
    reserve of the central-autoconvolution log-concavity margin, all `s`, symbolic `w ≤ 1/2`.
  * `offMinor_wrong_direction`, `symMinor_can_be_negative` — the machine-checked CORRECTION:
    the naive off-diagonal summand leg is false and the symmetrized off-diagonal minor is
    strictly negative, so the reserve is not a sum of nonnegative summands.

NAMED OPEN (carried from Round I, NOT inhabited here):
  * `AutoconvReserveResidual w` — the reserve `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.
    Round J supplies its diagonal reserve and shows the off-diagonal block is indefinite;
    what remains is the AGGREGATE cancellation of the indefinite off-diagonal block against
    the diagonal `(3/4)`-reserve, uniform in the `N`-truncation — the same
    `QuadGershgorinClosure` / heat-kernel local-CLT wall.
  * the A1 strand reindex `reindex` remains a threaded hypothesis.

HONEST VERDICT.  Round J PROVES the diagonal `(3/4)` Casimir minor reserve of the reserve
inequality and MACHINE-CHECKS that the off-diagonal Menon block is not sign-definite — so the
reserve genuinely needs aggregate cancellation, not summand-wise nonnegativity.  This
corrects the naive summand plan and sharpens the residual; it is NOT a 4D Yang–Mills mass
gap. -/

end YMGap.Continuum.FusionCoreStepRoundJ

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundJ.le_add_neg_of_add_le
#print axioms YMGap.Continuum.FusionCoreStepRoundJ.coeffW_diagReserve
#print axioms YMGap.Continuum.FusionCoreStepRoundJ.coeffW_diagMinor_reserve
#print axioms YMGap.Continuum.FusionCoreStepRoundJ.offMinor_wrong_direction
#print axioms YMGap.Continuum.FusionCoreStepRoundJ.symMinor_can_be_negative
