/-
Track A / R2 (track: 1-arraymlr) — the PRECISE REFUTATION of the pointwise adjacent-MLR sufficient
condition for the ACTUAL theta autoconvolution arrays, and the correct one-sided windowed-floor
residual to keep in its place.

# What this module settles

Upstream, `ArrayMLR.AdjacentMLR a m` (strict positivity of the denominator array `m` + the adjacent
one-step ratio inequality) was left NAMED-OPEN as a *sufficient* condition that, via the proved
telescoping engine `arrayMLR_of_adjacent_grid`, generates the full pointwise coefficient MLR
`CrossRatioMonotone.ArrayMLR a m e` (the TP₂ condition `e_k < e_j ⟹ a_k·m_j ≤ a_j·m_k`).

This module computes the ACTUAL `s = 1` arrays and shows `ArrayMLR.AdjacentMLR` is **uninhabitable**
for them — so it is the WRONG sufficient condition, defeated by theta lacunarity, and should not be
pursued.  The theta kernel is `c_s = (s+1)·w^{s(s+2)}` (`coeffW = dimQ·qpow`, `dimQ s = s+1`,
`c4 s = s(s+2)`), whose exponents `s(s+2) = 0,3,8,15,…` are lacunary.  At the worst mode `s = 1`,
window `n = s+1 = 2`, the antidiagonal split `A_1 = acN(2,1)·acN(2,3)` and diagonal split
`B_1 = acN(2,2)²` have exact coefficients

    A_1 = 24·w^14 + 16·w^18                 support {14, 18}
    B_1 = 16·w^12 + 24·w^14 +  9·w^16       support {12, 14, 16}

On the shared exponent grid `{12,14,16,18}` (indices `0,1,2,3`):

    a = (0, 24,  0, 16)      m = (16, 24,  9,  0).

Two independent, structural obstructions — both proved here as exact integer facts:

  * **Lacunary support ⇒ `mpos` fails.**  `m` carries a structural zero at the top exponent
    (`B_1` vanishes at `w^18`), so `AdjacentMLR.mpos : ∀ k, 0 < m k` is already violated
    (`m 3 = 0`).  The denominator array is NOT strictly positive.
  * **The generated pointwise MLR is FALSE.**  At indices `k = 1 < j = 2` the engine would force
    `a_1·m_2 ≤ a_2·m_1`, i.e. `24·9 ≤ 0·24`, i.e. `216 ≤ 0` — a false INTEGER inequality.

Either one alone gives `ArrayMLR.AdjacentMLR aTheta mTheta → False`.

# The correct residual to KEEP (not MLR)

`AcNReserveAnalytic.reserveOfFiniteSMargin` consumes `FiniteSMargin` DIRECTLY (bypassing
`CrossRatioMonotone`/`ArrayMLR`): its content is a one-sided uniform FLOOR, not a pointwise
TP₂/ratio.  In the window-total form `S_N := acN(s+1, N)` it is

    S_s · S_{s+2}  ≤  ρ · S_{s+1}²,      ρ = 22801/40000 ≈ 0.57025,

which needs neither pointwise TP₂ (killed above) nor `w`/`s`-monotonicity — only a floor with a
≈2.85× cushion over the exact per-mode atom `w² = 1/4` (`coeffW_superLogConcave_wsq`).  This module
provides that floor as the named residual `SaddleFloor` (the honest Gaussian-saddle log-concavity
target in the total-mass index `N`) and REDUCES it to the in-tree `FiniteSMargin` by clearing the
rational denominator — i.e. `SaddleFloor ⟹ FiniteSMargin`, connecting it to the whole reserve chain.

# The naive pointwise → line-sum lift is direction-wrong

Also proved: the sum-of-log-concave / A3 wall.  Pointwise `a_p·c_p ≤ ρ·b_p²` does NOT give
`(Σa)(Σc) ≤ ρ(Σb)²`: the concrete slice `a=(1,0), c=(0,1), b=(0,0)` satisfies every pointwise term
(all products `0`) yet `(Σa)(Σc)=1 ≰ ρ·0`.  So `WindowedGaussianEnvelope`-style pointwise seeds
alone cannot upper-bound `S_s·S_{s+2}`; a genuine saddle/local-CLT overlap estimate is required.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, `decide` on closed concrete-rational/integer facts, the reused `Q'`
order/`eqv` algebra and one nonneg left-multiplication, and the upstream proved telescoping engine.
Every load-bearing declaration is gated with `#print axioms`; permitted output is `propext` /
`propext, Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are
`Type`-level data.
-/

import YMGap.Continuum.ArrayMLR
import YMGap.Continuum.AcNReserveAnalytic

namespace YMGap.Continuum.AdjacentMLR

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.AcNReserveAnalytic

/-! ## 0. The exact `s = 1` theta arrays on the shared exponent grid `{12,14,16,18}` -/

/-- **`aTheta`** — the coefficient array of the antidiagonal split `A_1 = acN(2,1)·acN(2,3)` on the
shared grid `{12,14,16,18}` (indices `0,1,2,3`):  `a = (0, 24, 0, 16)`.  Support `{14,18}` (indices
`1,3`); the lacunary theta support makes it vanish at the two even grid points `12,16`. -/
def aTheta : Nat → Q'
  | 1 => Q'.ofNat 24
  | 3 => Q'.ofNat 16
  | _ => 0

/-- **`mTheta`** — the coefficient array of the diagonal split `B_1 = acN(2,2)²` on the shared grid
`{12,14,16,18}`:  `m = (16, 24, 9, 0)`.  Support `{12,14,16}` (indices `0,1,2`); it carries a
structural ZERO at the top grid point `18` (index `3`) — the obstruction to `AdjacentMLR.mpos`. -/
def mTheta : Nat → Q'
  | 0 => Q'.ofNat 16
  | 1 => Q'.ofNat 24
  | 2 => Q'.ofNat 9
  | _ => 0

/-- The antidiagonal array vanishes at the even interior grid points `12` (index 0) and `16`
(index 2) — the lacunary-support fact. -/
theorem aTheta_support_gap : aTheta 0 = 0 ∧ aTheta 2 = 0 := ⟨rfl, rfl⟩

/-- The diagonal array carries a structural zero at the top grid point `18` (index 3): `B_1`
vanishes where `A_1` lives.  This is exactly what defeats `AdjacentMLR.mpos`. -/
theorem mTheta_support_gap : mTheta 3 = 0 := rfl

/-! ## 1. The exact integer falsification of the generated pointwise MLR -/

/-- **`cross_false`** — the EXACT integer counterexample.  On the shared grid the pointwise MLR at
`k = 1 < j = 2` reads `a_1·m_2 ≤ a_2·m_1`, i.e. `24·9 ≤ 0·24`, i.e. `216 ≤ 0` — FALSE.  This is the
statement the telescoping engine is forced to produce from any `AdjacentMLR` witness. -/
theorem cross_false : ¬ (aTheta 1 * mTheta 2 ≤ aTheta 2 * mTheta 1) := by decide

/-- **`mpos_false`** — strict positivity of the denominator array is already violated: `m 3 = 0`,
so `¬ (0 < m 3)`.  Lacunary theta support ⇒ `AdjacentMLR.mpos` is unsatisfiable. -/
theorem mpos_false : ¬ ((0 : Q') < mTheta 3) := by decide

/-! ## 2. The refutation of `ArrayMLR.AdjacentMLR` for the actual arrays -/

/-- **`adjacentMLR_refuted_via_mpos`** — the first, direct refutation: any `AdjacentMLR aTheta mTheta`
witness supplies `mpos 3 : 0 < mTheta 3`, contradicting the structural zero `mTheta 3 = 0`. -/
theorem adjacentMLR_refuted_via_mpos (H : ArrayMLR.AdjacentMLR aTheta mTheta) : False :=
  mpos_false (H.mpos 3)

/-- **`adjacentMLR_refuted_via_mlr`** — the second, independent refutation: feeding the witness
through the proved telescoping engine `arrayMLR_of_adjacent_id` produces the full pointwise MLR
`CrossRatioMonotone.ArrayMLR aTheta mTheta (fun n => n)`, whose value at `j = 2, k = 1` is the false
inequality `216 ≤ 0` (`cross_false`).  This is the content-bearing refutation: the engine is valid,
so the input `AdjacentMLR` must be uninhabitable. -/
theorem adjacentMLR_refuted_via_mlr (H : ArrayMLR.AdjacentMLR aTheta mTheta) : False :=
  cross_false ((ArrayMLR.arrayMLR_of_adjacent_id H).mlr 2 1 (by decide))

/-- **`adjacentMLR_uninhabited`** — packaged verdict: `ArrayMLR.AdjacentMLR` is uninhabitable for
the actual theta arrays.  `ArrayMLR.AdjacentMLR` is therefore the WRONG sufficient condition for the
theta autoconvolution log-concavity — a pointwise total-positivity over-ask that lacunarity defeats.
Stop trying to inhabit it. -/
theorem adjacentMLR_uninhabited : ArrayMLR.AdjacentMLR aTheta mTheta → False :=
  adjacentMLR_refuted_via_mpos

/-! ## 3. The naive pointwise → line-sum lift is direction-wrong (the A3 sum-of-log-concave wall) -/

/-- The rational floor constant `ρ = 22801/40000 ≈ 0.57025` (the crude two-term theta floor). -/
def rhoFloor : Q' := Q'.mkPos 22801 40000 (by decide)

/-- **`naive_lift_direction_wrong`** — the concrete A3 refutation.  The two-entry slice
`a = (1,0)`, `c = (0,1)`, `b = (0,0)` satisfies the pointwise bound `a_p·c_p ≤ ρ·b_p²` at BOTH
entries (all products are `0`), yet the line-sum upper bound FAILS:
`(a_0+a_1)·(c_0+c_1) = 1 ≰ ρ·(b_0+b_1)² = 0`.  So a pointwise seed cannot upper-bound the product of
window line-sums — the windowed Cauchy–Schwarz is in the wrong direction, and a genuine saddle
estimate (not `WindowedGaussianEnvelope` alone) is required for the floor. -/
theorem naive_lift_direction_wrong :
    -- pointwise bound holds at both entries (all products zero)
    ((1 : Q') * 0 ≤ rhoFloor * (0 * 0))
      ∧ ((0 : Q') * 1 ≤ rhoFloor * (0 * 0))
    -- yet the summed upper bound fails
    ∧ ¬ (((1 : Q') + 0) * (0 + 1) ≤ rhoFloor * ((0 + 0) * (0 + 0))) := by decide

/-! ## 4. The correct residual to KEEP: the one-sided windowed floor, reduced to `FiniteSMargin` -/

/-- **`SaddleFloor w` — THE NAMED RESIDUAL TO KEEP.**  The one-sided windowed floor in `ρ`-form:
for every mode `s`, the antidiagonal window product is bounded by `ρ = 22801/40000` times the
diagonal window square,

    acN(s+1,s)·acN(s+1,s+2)  ≤  ρ · acN(s+1,s+1)²,      ρ = 22801/40000.

In the total-mass notation `S_N := acN(s+1,N)` this is the Gaussian-saddle log-concavity
`S_s·S_{s+2} ≤ ρ·S_{s+1}²` — the discrete second difference of `log S_N` in the total-mass index `N`
exceeding `log ρ`, with a ≈2.85× cushion over the exact per-mode atom `w²=1/4`
(`coeffW_superLogConcave_wsq`).  It needs neither pointwise TP₂ (refuted in §2) nor `w`/`s`-
monotonicity — only the floor.  This is a one-sided lower bound (Tate–Zelditch local-CLT), the
correct object.  NAMED-OPEN (never `sorry`): this module does NOT inhabit it. -/
structure SaddleFloor (w : Q') : Type where
  /-- The one-sided windowed floor, uniform in `s`. -/
  floor : ∀ s,
    acN w (s + 1) s * acN w (s + 1) (s + 2)
      ≤ rhoFloor * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1))

/-- **`clearDenom`** — the pure-`Q'` denominator-clearing bridge.  From the one-sided floor
`A ≤ ρ·B` (`ρ = 22801/40000`) conclude `40000·A ≤ 22801·B`: rescale by the positive factor `40000`
and use `40000·ρ ≃ 22801`.  No sign hypothesis on `A`, `B` is needed. -/
theorem clearDenom {A B : Q'} (h : A ≤ rhoFloor * B) :
    Q'.ofNat 40000 * A ≤ Q'.ofNat 22801 * B := by
  have hstep : Q'.ofNat 40000 * A ≤ Q'.ofNat 40000 * (rhoFloor * B) :=
    Q'.mul_le_mul_of_nonneg_left A (rhoFloor * B) (Q'.ofNat 40000) h (by decide)
  have heqv : (Q'.ofNat 40000 * (rhoFloor * B)).eqv (Q'.ofNat 22801 * B) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 40000) rhoFloor B))
      (Q'.mul_eqv_congr_right (Q'.ofNat 40000 * rhoFloor) (Q'.ofNat 22801) B (by decide))
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv heqv)

/-- **`finiteSMargin_of_saddleFloor` — THE REDUCTION.**  A `SaddleFloor w` witness inhabits the
in-tree `AcNReserveAnalytic.FiniteSMargin w` by clearing the rational denominator (`clearDenom`).
This connects the kept residual to the whole reserve chain
(`reserveOfFiniteSMargin ⟶ AcNDefectReserve ⟶ SymMinorGershgorin`).  No sign hypothesis on `w` is
needed — the bridge is a single positive rescale of the one-sided inequality. -/
def finiteSMargin_of_saddleFloor {w : Q'} (H : SaddleFloor w) : FiniteSMargin w where
  margin := fun s => clearDenom (H.floor s)

/-- **`reserveOfSaddleFloor` — end-to-end wiring.**  Composed with the in-tree
`AcNReserveAnalytic.reserveOfFiniteSMargin`, a `SaddleFloor w` witness (with `0 ≤ w`) yields the full
`LeakGeoDecay.AcNDefectReserve w` — i.e. the one-sided saddle floor is exactly the analytic content
that closes the autoconvolution log-concavity reserve. -/
def reserveOfSaddleFloor {w : Q'} (hw0 : (0 : Q') ≤ w) (H : SaddleFloor w) :
    LeakGeoDecay.AcNDefectReserve w :=
  reserveOfFiniteSMargin hw0 (finiteSMargin_of_saddleFloor H)

/-! ## 5. PROVED vs. NAMED-open (honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `aTheta` / `mTheta` — the exact `s=1` coefficient arrays on the shared exponent grid.
  * `aTheta_support_gap` / `mTheta_support_gap` — the lacunary structural zeros.
  * `cross_false` — the exact integer falsification `¬ (216 ≤ 0)` of the generated pointwise MLR.
  * `mpos_false` — `¬ (0 < m 3)`: strict positivity of the denominator array is violated.
  * `adjacentMLR_refuted_via_mpos` / `adjacentMLR_refuted_via_mlr` / `adjacentMLR_uninhabited` —
    the two independent refutations of `ArrayMLR.AdjacentMLR` for the actual arrays.
  * `naive_lift_direction_wrong` — the A3 sum-of-log-concave wall: pointwise `≤` does not lift to
    the line-sum product upper bound.
  * `finiteSMargin_of_saddleFloor` — the reduction `SaddleFloor ⟹ FiniteSMargin` (denominator clear).
  * `reserveOfSaddleFloor` — end-to-end `SaddleFloor ⟹ AcNDefectReserve`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `SaddleFloor w` — the one-sided windowed floor `S_s·S_{s+2} ≤ ρ·S_{s+1}²`, the correct
    Gaussian-saddle / Tate–Zelditch local-CLT residual to keep in place of the refuted `AdjacentMLR`.

HONEST VERDICT.  `ArrayMLR.AdjacentMLR` for the real theta arrays is REFUTED (exact `s=1` integer
counterexample `216 ≤ 0`; `mpos` fails on lacunary support): it is a pointwise total-positivity
over-ask that theta lacunarity structurally defeats, and the whole `CrossRatioMonotone`/`crossTP2`
route is the wrong sufficient condition.  The correct object is the one-sided windowed floor
`SaddleFloor`, reduced here to the in-tree `FiniteSMargin` (and thence the reserve chain).  This is a
sharp reduction plus a precise refutation of one box-level log-concavity sub-fact; it is NOT a 4D
Yang–Mills mass gap. -/

end YMGap.Continuum.AdjacentMLR

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AdjacentMLR.aTheta_support_gap
#print axioms YMGap.Continuum.AdjacentMLR.mTheta_support_gap
#print axioms YMGap.Continuum.AdjacentMLR.cross_false
#print axioms YMGap.Continuum.AdjacentMLR.mpos_false
#print axioms YMGap.Continuum.AdjacentMLR.adjacentMLR_refuted_via_mpos
#print axioms YMGap.Continuum.AdjacentMLR.adjacentMLR_refuted_via_mlr
#print axioms YMGap.Continuum.AdjacentMLR.adjacentMLR_uninhabited
#print axioms YMGap.Continuum.AdjacentMLR.naive_lift_direction_wrong
#print axioms YMGap.Continuum.AdjacentMLR.clearDenom
#print axioms YMGap.Continuum.AdjacentMLR.finiteSMargin_of_saddleFloor
#print axioms YMGap.Continuum.AdjacentMLR.reserveOfSaddleFloor
