/-
Track B / local-CLT — the GENUINE decoupling of the Casimir-normalized shift second-difference
`XMeanSecondDiffLeOne` (`d2x ≤ 1`) into two universal-sign halves, correcting the module's own
recommended-but-circular split.

# What this module adds (read first — load-bearing honesty)

`MeanExpConvexProgress.XMeanSecondDiffLeOne w` is the sole open first-moment datum feeding the
fusion-box log-concavity chain, after the entire Casimir/geometry has been stripped to the exact
constant `+2` (`casimir_secondDiff_eq_two : Δ²C₄ = 2`).  Concretely `d2x ≤ 1 = ½·Δ²C₄` is TIGHT, so it
is genuinely a local-CLT / Tate–Zelditch estimate, not a covariance positivity.

With the exact machine-checked covariance decomposition `x_p = p(s−p) + (t−s)·p`,
    `d2x = d2A + 2·dB`,   `dB = ⟨p⟩_{s+2} − ⟨p⟩_{s+1}`,
    `d2A = ⟨x^{(s)}⟩_s − 2⟨x^{(s)}⟩_{s+1} + ⟨x^{(s)}⟩_{s+2}`.

## The route-correction (honesty finding)

The `MeanExpConvexProgress` header recommends the split
    `MeanShiftHalf (dB ≤ 1/2)`  +  "correctly-signed residual `d2A ≤ 1 − 2dB`".
But `d2A ≤ 1 − 2dB  ⟺  d2A + 2dB ≤ 1  ⟺  d2x ≤ 1` — **the named companion residual is literally the
target rewritten**, so that split decouples NOTHING.  `MeanShiftHalf` alone cannot close `d2x ≤ 1`
(that would need `d2A ≤ 0`, which is REFUTED: `d2A > 0` near `w = 1`, growing with `s`).

## The GENUINE decoupling (this module)

Regroup the SAME identity as
    `d2x = (d2x − dB) + dB`,
with BOTH halves genuinely `≤ 1/2` (universal sign):
  * `dB ≤ 1/2`         — `MeanExpConvexProgress.MeanShiftHalf` (the universal-sign mean-shift engine).
  * `d2x − dB ≤ 1/2`   — `MeanShiftComplementHalf` (this module; the complement half).
Their sum gives `d2x ≤ 1`.  This is a genuine decoupling (unlike the circular header split): each half
is a real, separately-provable `≤ 1/2` statement.  It does NOT soften the crux — both halves saturate
at the SAME even-`s`, `w → 0` two-point-tie corner (`½δ_m + ½δ_{m+1}`, `d2x → 1⁻`) — but it factors the
target through two universal-sign sub-obligations rather than one tight inequality.

# What this module proves (all axiom-clean, `[propext]` / `[propext, Quot.sound]`)

  * `two_mul_eqv` — the numeric doubling `ofNat 2 · x ≃ x + x` (the ONE non-AC identity used).
  * `xmsd_of_halves_core` — the pure-`Q'` combination lemma: the two cleared half-inequalities plus a
    single positive-factor cancellation yield the cleared target `d2x ≤ 1`.  All bridging identities
    are SUBTRACTION-FREE (closed by the reused `ring_qeqv`); the only cancellations are the numeric
    `+E/−E` (`le_of_add_le_add_right`) and the positive factor `2` (`Q'.le_of_mul_le_mul_left`).
  * `xmsd_of_msh_msch` — THE REDUCTION: `MeanShiftHalf w ∧ MeanShiftComplementHalf w`
    inhabits `XMeanSecondDiffLeOne w` (for `0 ≤ w`, using `acN_nonneg`).
  * `meanExpConvex_of_halves` — the composite: the two halves inhabit `FusionMarginMonotone.MeanExpConvex w`
    (chained through the existing `meanExpConvex_of_xmsd`).

# NAMED OPEN (Type-level structure, never `sorry`)

  * `MeanShiftComplementHalf w` — the complement half `d2x − dB ≤ 1/2`, cleared over
    `acN_{s+1,s}·acN_{s+1,s+1}·acN_{s+1,s+2}` in subtraction-free form.  Universal-sign (`→ 1/2` at the
    even-`s`, `w → 0` corner); NOT provably-empty and NOT the circular header companion.

# HONEST VERDICT

A route-correction + valid decoupling + reusable combination machinery, NOT a closure.  The circular
"`d2A ≤ 1 − 2dB`" companion is replaced by the genuinely-decoupled complement half `d2x − dB ≤ 1/2`;
together with `MeanShiftHalf` it inhabits `XMeanSecondDiffLeOne` and hence `MeanExpConvex`.  Both halves
still saturate at the even-`s` two-point tie, so the local-CLT crux is relocated, not removed.  The Clay
Yang–Mills mass gap remains OPEN (reduction mode).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic, the reused `ring_qeqv` cancellation-free ring closer (subtraction-free only —
every use here is subtraction-free), `two_mul_eqv` for the single numeric doubling, and the imported
`acN_nonneg` / `Q'.le_of_mul_le_mul_left` / `Q'.mul_le_mul_of_nonneg_left`.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.MeanExpConvexProgress
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.XMeanSecondDiffProgress

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.FusionMarginMonotone
open YMGap.Continuum.MeanExpConvexProgress

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The numeric doubling `ofNat 2 · x ≃ x + x`.

This is the ONE identity in the module that is NOT a pure associativity/commutativity ring fact
(`x + x` vs `2·x` is genuinely numeric), so it is isolated here and threaded as an explicit
hypothesis into the otherwise-AC combination core. -/

/-- `ofNat 2 · x ≃ x + x`. -/
theorem two_mul_eqv (x : Q') : (Q'.ofNat 2 * x).eqv (x + x) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (Q'.ofNat 2) (1 + 1) x (by decide)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 x) ?_
  exact Q'.add_eqv_congr' (Q'.one_mul_eqv x) (Q'.one_mul_eqv x)

/-! ## 1. The pure-`Q'` combination core.

The two cleared half-inequalities, added and cleared, give exactly TWICE the cleared target; a single
positive-factor cancellation recovers `d2x ≤ 1`.  All the polynomial bridges (`eL`, `eR1`, `eR3`) are
subtraction-free (closed by `ring_qeqv`); the sole numeric input is the doubling `hdbl` (for the one
term `As·(A1·A2)`, which two separate `≤ D` right-hand sides contribute additively). -/

/-- **`xmsd_of_halves_core`** — the cleared target `d2x ≤ 1`

    `Xs·(A1·A2) + X2·(As·A1)  ≤  As·(A1·A2) + 2·(X1·(As·A2))`

follows from:
  * `hMSH` — the mean-shift half `2·(P2·A1) ≤ A1·A2 + 2·(P1·A2)`  (`dB ≤ 1/2`, cleared over `A1·A2`);
  * `hMSC` — the complement half (cleared over `As·A1·A2`, subtraction-free `×2` form of `d2x − dB ≤ 1/2`);
  * `hAs` — `0 ≤ As` (to scale `hMSH` by `As`);
  * `hdbl` — the numeric doubling `As·(A1·A2) + As·(A1·A2) ≃ 2·(As·(A1·A2))`;
  * `htwo_pos` — `0 < two` (to cancel the leading factor).

Adding `As·hMSH` and `hMSC`, the `P`-terms cancel and the two `As·(A1·A2)` right-hand contributions
combine (via `hdbl`) into `two·(As·(A1·A2))`, leaving exactly `two·target`; `Q'.le_of_mul_le_mul_left`
strips the `two`. -/
theorem xmsd_of_halves_core
    (As A1 A2 Xs X1 X2 P1 P2 two : Q')
    (htwo_pos : (0 : Q') < two)
    (hAs : (0 : Q') ≤ As)
    (hdbl : (As * (A1 * A2) + As * (A1 * A2)) ≈ (two * (As * (A1 * A2))))
    (hMSH : two * (P2 * A1) ≤ A1 * A2 + two * (P1 * A2))
    (hMSC : two * (Xs * (A1 * A2)) + two * (X2 * (As * A1)) + two * (P1 * (As * A2))
              ≤ As * (A1 * A2) + two * (two * (X1 * (As * A2))) + two * (P2 * (As * A1))) :
    Xs * (A1 * A2) + X2 * (As * A1) ≤ As * (A1 * A2) + two * (X1 * (As * A2)) := by
  -- scale the mean-shift half by `As ≥ 0`
  have hMSH_As : As * (two * (P2 * A1)) ≤ As * (A1 * A2 + two * (P1 * A2)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ As hMSH hAs
  -- add the two halves
  have hsum := Q'.add_le_add hMSH_As hMSC
  -- LHS collapse: the added left sides ≃ `two·targetLHS + E` (pure AC)
  have eL :
      (As * (two * (P2 * A1))
        + (two * (Xs * (A1 * A2)) + two * (X2 * (As * A1)) + two * (P1 * (As * A2))))
      ≈ (two * (Xs * (A1 * A2) + X2 * (As * A1))
          + (two * (P1 * (As * A2)) + two * (P2 * (As * A1)))) := by ring_qeqv
  -- RHS collapse, step 1: the added right sides ≃ `(As·A1A2 + As·A1A2) + R` (pure AC)
  have eR1 :
      (As * (A1 * A2 + two * (P1 * A2))
        + (As * (A1 * A2) + two * (two * (X1 * (As * A2))) + two * (P2 * (As * A1))))
      ≈ ((As * (A1 * A2) + As * (A1 * A2))
          + (two * (two * (X1 * (As * A2))) + two * (P1 * (As * A2)) + two * (P2 * (As * A1)))) := by
    ring_qeqv
  -- RHS collapse, step 2: fold the doubled `As·A1A2` into `two·(As·A1A2)` (numeric, via `hdbl`)
  have eR2 :
      ((As * (A1 * A2) + As * (A1 * A2))
          + (two * (two * (X1 * (As * A2))) + two * (P1 * (As * A2)) + two * (P2 * (As * A1))))
      ≈ ((two * (As * (A1 * A2)))
          + (two * (two * (X1 * (As * A2))) + two * (P1 * (As * A2)) + two * (P2 * (As * A1)))) :=
    Q'.add_eqv_congr_right _ _ _ hdbl
  -- RHS collapse, step 3: ≃ `two·targetRHS + E` (pure AC)
  have eR3 :
      ((two * (As * (A1 * A2)))
          + (two * (two * (X1 * (As * A2))) + two * (P1 * (As * A2)) + two * (P2 * (As * A1))))
      ≈ (two * (As * (A1 * A2) + two * (X1 * (As * A2)))
          + (two * (P1 * (As * A2)) + two * (P2 * (As * A1)))) := by ring_qeqv
  have eR := Q'.eqv_trans _ _ _ eR1 (Q'.eqv_trans _ _ _ eR2 eR3)
  -- rewrite both ends of `hsum`
  have hstep :
      (two * (Xs * (A1 * A2) + X2 * (As * A1))
          + (two * (P1 * (As * A2)) + two * (P2 * (As * A1))))
      ≤ (two * (As * (A1 * A2) + two * (X1 * (As * A2)))
          + (two * (P1 * (As * A2)) + two * (P2 * (As * A1)))) :=
    le_of_eqvR (le_of_eqvL (Q'.eqv_symm eL) hsum) eR
  -- cancel the common `E`, then the positive factor `two`
  have hcancel :
      two * (Xs * (A1 * A2) + X2 * (As * A1))
        ≤ two * (As * (A1 * A2) + two * (X1 * (As * A2))) :=
    le_of_add_le_add_right hstep
  exact Q'.le_of_mul_le_mul_left hcancel htwo_pos

/-! ## 2. The complement half (named open Type-level residual). -/

/-- **`MeanShiftComplementHalf w`** — the complement half `d2x − dB ≤ 1/2`, cleared over
`acN_{s+1,s}·acN_{s+1,s+1}·acN_{s+1,s+2}` in subtraction-free `×2` form:

    2·⟨x⟩-numerator terms + 2·⟨p⟩_{s+1}-numerator
      ≤ acN_s·acN_{s+1}·acN_{s+2} + 4·⟨x⟩_{s+1}-numerator + 2·⟨p⟩_{s+2}-numerator.

Together with `MeanShiftHalf` (`dB ≤ 1/2`) it yields `d2x = (d2x − dB) + dB ≤ 1`, i.e.
`XMeanSecondDiffLeOne`.  This is the GENUINE decoupling — NOT the circular header companion
`d2A ≤ 1 − 2dB` (which is the target rewritten).  Universal-sign (`→ 1/2` at the even-`s`, `w → 0`
two-point tie), hence not provably-empty.  NAMED-OPEN (never `sorry`). -/
structure MeanShiftComplementHalf (w : Q') : Type where
  msch : ∀ s,
    Q'.ofNat 2 * (xmomN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2)))
        + Q'.ofNat 2 * (xmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1)))
        + Q'.ofNat 2 * (pmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
      ≤ acN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + Q'.ofNat 2 * (Q'.ofNat 2
            * (xmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2))))
        + Q'.ofNat 2 * (pmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1)))

/-! ## 3. The reduction: the two halves inhabit `XMeanSecondDiffLeOne`. -/

/-- **`xmsd_of_msh_msch` — THE REDUCTION.**  For `0 ≤ w`, a `MeanShiftHalf w` witness together with a
`MeanShiftComplementHalf w` witness inhabits `MeanExpConvexProgress.XMeanSecondDiffLeOne w`:
instantiate `xmsd_of_halves_core` per window with the two cleared halves, `acN_nonneg` for `0 ≤ acN`,
and `two_mul_eqv` for the numeric doubling.  This is the honest, non-circular decoupling of the tight
shift second-difference into two universal-sign `≤ 1/2` obligations. -/
def xmsd_of_msh_msch {w : Q'} (hw0 : (0 : Q') ≤ w)
    (M : MeanShiftHalf w) (C : MeanShiftComplementHalf w) : XMeanSecondDiffLeOne w where
  xmsd := fun s =>
    xmsd_of_halves_core
      (acN w (s + 1) s) (acN w (s + 1) (s + 1)) (acN w (s + 1) (s + 2))
      (xmomN w (s + 1) s) (xmomN w (s + 1) (s + 1)) (xmomN w (s + 1) (s + 2))
      (pmomN w (s + 1) (s + 1)) (pmomN w (s + 1) (s + 2))
      (Q'.ofNat 2)
      (by decide)
      (acN_nonneg hw0 (s + 1) s)
      (Q'.eqv_symm (two_mul_eqv (acN w (s + 1) s
        * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2)))))
      (M.msh s)
      (C.msch s)

/-- **`meanExpConvex_of_halves` — the composite reduction.**  The two universal-sign halves inhabit
`FusionMarginMonotone.MeanExpConvex w`, chaining `xmsd_of_msh_msch` through the existing
`meanExpConvex_of_xmsd`. -/
def meanExpConvex_of_halves {w : Q'} (hw0 : (0 : Q') ≤ w)
    (M : MeanShiftHalf w) (C : MeanShiftComplementHalf w) : MeanExpConvex w :=
  meanExpConvex_of_xmsd (xmsd_of_msh_msch hw0 M C)

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `two_mul_eqv` — the numeric doubling `ofNat 2 · x ≃ x + x`.
  * `xmsd_of_halves_core` — the pure-`Q'` combination `MSH ∧ MSC ⟹ d2x ≤ 1` (cleared).
  * `xmsd_of_msh_msch` — THE REDUCTION `MeanShiftHalf w ∧ MeanShiftComplementHalf w ⟹ XMeanSecondDiffLeOne w`.
  * `meanExpConvex_of_halves` — the composite `… ⟹ MeanExpConvex w`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `MeanShiftComplementHalf w` — the complement half `d2x − dB ≤ 1/2` (universal-sign, corner-tight).

ROUTE-CORRECTION (prose; see header): the header-recommended companion `d2A ≤ 1 − 2dB` is CIRCULAR
(literally `d2x ≤ 1` rewritten).  The genuine decoupling is `d2x = (d2x − dB) + dB` with BOTH halves
`≤ 1/2`; `MeanShiftComplementHalf` is the correctly-decoupled complement, not the circular residual.

HONEST VERDICT.  A route-correction + valid decoupling + reusable combination machinery, NOT a closure.
Both halves saturate at the even-`s`, `w → 0` two-point tie, so the local-CLT crux is relocated, not
removed.  The Clay Yang–Mills mass gap remains OPEN. -/

end YMGap.Continuum.XMeanSecondDiffProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.XMeanSecondDiffProgress.two_mul_eqv
#print axioms YMGap.Continuum.XMeanSecondDiffProgress.xmsd_of_halves_core
#print axioms YMGap.Continuum.XMeanSecondDiffProgress.xmsd_of_msh_msch
#print axioms YMGap.Continuum.XMeanSecondDiffProgress.meanExpConvex_of_halves
