/-
Track B / local-CLT — the ADDITIVE-FOURIER-CIRCLE reframing of the open position-variance curvature
floor `Δ²_t ⟨D²⟩_t ≥ −2` (`MeanComplementClose.TwoPointTieSubleading`).

# Why this file exists (read first — load-bearing honesty)

EVERY per-term / local-combinatorial route to `Δ²⟨D²⟩ ≥ −2` is proven DEAD (Menon minor indefinite,
naive `(p,p+2)` summand `≤ 0`, line-sum log-concavity false from bare TP₂, Karlin inapplicable to a
TRUNCATED product).  What is needed is a GLOBAL aggregate-cancellation / Gaussian-decay estimate.  This
module relocates the residual to the higher-dimensional home where that estimate is standard: the
**additive Fourier circle**.

## The dictionary (exact; validated numerically to machine precision)

The project coefficient (`BondMovingStep.coeffW`) is the SU(2) heat-kernel character coefficient

    coeffW w s = (s+1)·w^{s(s+2)}          (`c₄ s = s(s+2) = (s+1)²−1`, `dimQ s = s+1`).

Form the **additive generating function** on the circle (NOT the SU(2) conjugacy circle — see the
correction below):

    f_w(θ) = Σ_{r≥0} coeffW(w,r) · e^{i r θ}          (a theta / Jacobi-derivative kernel, 0<w<1).

Because multiplication on the additive circle is `e^{ipθ}·e^{iqθ} = e^{i(p+q)θ}`, the FULL (untruncated)
autoconvolution is EXACTLY the t-th Fourier coefficient of the pointwise SQUARE:

    acN_full(w,t) := acN w (t+1) t = Σ_{p=0}^{t} coeffW(w,p)·coeffW(w,t−p)
                   = [ f_w² ]_t = (1/2π) ∫_{−π}^{π} f_w(θ)² e^{−i t θ} dθ .   (⋆)

The **antidiagonal square** `D_p = t − 2p` is a psi-shift: with the two-shift kernel

    Φ_t(ψ) := [ f_w(θ+ψ)·f_w(θ−ψ) ]_t = Σ_p coeffW(w,p)·coeffW(w,t−p)·e^{−i D_p ψ},

we get `acN_full = Φ_t(0)`, `⟨D⟩ = 0` (by the `p ↔ t−p` symmetry `Φ_t(−ψ)=Φ_t(ψ)`), and

    dmomN_full(w,t) := dmomN w (t+1) t = Σ_p D_p²·coeffW(w,p)·coeffW(w,t−p) = −Φ_t''(0),
    ⟨D²⟩_t = dmomN_full / acN_full = −(Φ_t''/Φ_t)(0) = −(log Φ_t)''(0) = κ₂(t),           (⋆⋆)

the **second cumulant** (variance) of the tilted measure `μ_t(p) ∝ coeffW(w,p)·coeffW(w,t−p)` on
`p ∈ {0,…,t}`.  Here `Φ_t(ψ)/Φ_t(0)` is literally the characteristic function `E_{μ_t}[e^{−iDψ}]`.
So `⟨D²⟩_t` is a CUMULANT-CURVATURE quantity, and `Δ²⟨D²⟩` its second difference in the degree `t`.

## The saddle / theta picture (why the truncation dissolves)

`μ_t(p) ∝ (p+1)(t−p+1)·w^{p²+(t−p)²+2t}`.  The `w`-exponent `p²+(t−p)² = t²/2 + 2(p−t/2)²` is a
DISCRETE GAUSSIAN of width `σ² = 1/(4|log w|)` centred at `p = t/2` (`D = 0`).  Hence
`⟨D²⟩_t = 4σ² → 1/|log w|` (a t-independent constant; pilot ratio → 1), and the ONLY t-dependence is the
integer-lattice PARITY of the centre:

  * `t` even : centre `t/2` is ON a lattice point ⇒ `D = 0` attainable ⇒ `⟨D²⟩_t → 0` as `w → 0`;
  * `t` odd  : centre `t/2` sits BETWEEN lattice points ⇒ `D = ±1` minimal ⇒ `⟨D²⟩_t → 1` (two-point tie).

The `−2` floor is EXACTLY this even/odd oscillation: at even `s`, `w → 0`,

    Δ²⟨D²⟩ = ⟨D²⟩_s + ⟨D²⟩_{s+2} − 2·⟨D²⟩_{s+1} → 0 + 0 − 2·1 = −2      (corner-tight, pilot: → −1.99999…).

In the circle form (⋆)–(⋆⋆) this is a STANDARD theta / discrete-Gaussian saddle statement (Poisson
summation / Jacobi; "theta q→1", Tate–Zelditch), whereas the truncated Clebsch–Gordan combinatorics
made every additive-convolution tool inapplicable.  The truncation is an artifact of the finite window
`n = s+1`, NOT of the object: the natural object `acN_full = [f_w²]_t` is truncation-FREE.

## TWO honest corrections to the naive "SU(2)-character / n-fold-power" framing

1. `acN` is a **2-fold** autoconvolution `Σ_p c_p·c_{t−p}` (the tensor SQUARE `g²`), NOT an `n`-fold
   power `g^n`.  The `n` in `acN w n t` is the TRUNCATION RANGE, not a fold count.  So the correct
   circle object is `f_w²`, a fixed pointwise square, and the "local CLT" is in the DEGREE `t`
   (parity of the discrete-Gaussian centre), not in a power `n → ∞`.

2. The convolution is **additive** (`p + (t−p) = t`), so the correct home is the additive Fourier
   circle `e^{irθ}`, NOT the SU(2) conjugacy circle with characters `χ_s`.  SU(2) fusion is truncated
   Clebsch–Gordan, `χ_p·χ_q = Σ_c N^c_{pq} χ_c`, whose `χ_t`-coefficient is `Σ_{p,q} c_p c_q N^t_{pq}
   ≠ Σ_p c_p c_{t−p}`.  Using `χ_s` would REINTRODUCE the very CG truncation we are escaping; the
   additive circle is what makes (⋆) EXACT.

Both (⋆) and (⋆⋆) are validated to machine precision (rel.err ≤ 1e-52 for (⋆); ≤ 4e-7 for the
finite-difference check of (⋆⋆)) against the project's combinatorial `acN`/`dmomN`.

# What this file provides (Type-level, named-open, NO `sorry`, NO fabricated proof)

The reframing splits `TwoPointTieSubleading` into TWO named residuals:

  * `SaddleVarianceFloor w`  (**R1**, the real content) — the `−2` floor on the FULL-range moments
    `acN w (t+1) t`, `dmomN w (t+1) t` (`= [f_w²]_t` by (⋆)).  This is the clean, well-posed theta /
    discrete-Gaussian saddle bound; it carries ALL the transcendental "global Gaussian-decay" content.
  * `WindowTailTransfer w` (**R2**, where the truncation reappears) — the per-window IMPLICATION that
    the WINDOWED floor (fixed `n = s+1`, the object `TwoPointTieSubleading` actually asks for) follows
    from the full-range floor.  The window drops the large-`D` boundary terms `p ∈ {s+1,s+2}`; the
    dropped tail is sign-definite and exponentially small at small `w` / large `s` (pilot: `1e-4` at
    `w=0.02,s=2` down to `1e-55` at `s=8`), and where it is O(0.1–0.3) at large `w` the floor has large
    positive slack — but it is NOT identically zero, so the transfer is a genuine (elementary,
    sign-counting) obligation, not free.

`circleFourier_twoPointTie` composes R1 and R2 into `TwoPointTieSubleading w` by pure modus ponens
(genuinely axiom-clean given the two fields; no `sorry`, no algebra faked).

# HONEST VERDICT (see the closing doc-section)

The additive Fourier circle IS the right home for the LEADING content: it makes the full-range floor a
clean, well-posed theta saddle bound (R1) and explains the `−2` corner exactly.  But the truncation
does NOT fully vanish for the EXACT windowed Lean object — it reappears as the sign-controlled boundary
tail R2.  So this is a genuine relocation of the transcendental core onto a STANDARD theta/local-CLT
saddle, reducing to ONE clean saddle residual (R1) PLUS one elementary truncation-transfer residual
(R2); it is a sharp reduction, not a closure.  The Clay Yang–Mills mass gap remains OPEN.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Only the composition `circleFourier_twoPointTie` is a theorem here, and it is pure modus ponens over the
two `Type`-level residual fields; its `#print axioms` is `[propext]` / `[propext, Quot.sound]` only (via
the reused `≤`/`Q'` machinery).  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
Both residuals are `Type`-level structures (Rule 6a named-hypothesis pattern), never `Prop := True` or a
`Unit` witness.  The Fourier-integral side of (⋆)/(⋆⋆) is DOCUMENTED (not asserted as a Lean field):
formalizing it uses the constructive Riemann-sum circle-integral substrate of the `Semicircle*` family
(`SemicircleIntegral.semiInt` and its Cauchy modulus `SemicircleCauchy`) and is a routine, NON-load-
bearing obligation — the load-bearing residual is the purely combinatorial R1.
-/

import YMGap.Continuum.MeanComplementClose

namespace YMGap.Continuum.CircleFourierPowerModel

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.MeanComplementCovariance
open YMGap.Continuum.MeanComplementClose

/-! ## 1. Full-range (truncation-free) moments = the Fourier-square coefficients.

`acNfull w t = acN w (t+1) t` sums the WHOLE antidiagonal `p ∈ {0,…,t}`, so by the additive
Fourier-power identity (⋆) it equals `[f_w²]_t` exactly (no window).  Likewise `dmomNfull w t
= dmomN w (t+1) t = −Φ_t''(0)` by (⋆⋆).  These are the objects on which the theta saddle bound is
clean. -/

/-- **`acNfull w t`** — the FULL-range central autoconvolution `Σ_{p=0}^{t} coeffW w p · coeffW w (t−p)`;
`= [f_w²]_t`, the `t`-th Fourier coefficient of the additive square (identity (⋆), pilot-exact). -/
def acNfull (w : Q') (t : Nat) : Q' := acN w (t + 1) t

/-- **`dmomNfull w t`** — the FULL-range antidiagonal-square moment `Σ_{p=0}^{t} D_p²·coeffW w p·coeffW w
(t−p)`; `= −Φ_t''(0)`, the second-cumulant curvature of the two-shift kernel (identity (⋆⋆)). -/
def dmomNfull (w : Q') (t : Nat) : Q' := dmomN w (t + 1) t

/-! ## 2. The two floor predicates (cleared, subtraction-free, `2·⟨D²⟩_{s+1} ≤ ⟨D²⟩_s+⟨D²⟩_{s+2}+2`). -/

/-- **`WindowedFloor w s`** — EXACTLY the `TwoPointTieSubleading.d2var` inequality at `s`: the `−2` floor
on the WINDOWED moments `acN w (s+1) ·`, `dmomN w (s+1) ·` (fixed window `n = s+1`).  This is the object
the mass-gap chain actually consumes. -/
def WindowedFloor (w : Q') (s : Nat) : Prop :=
  Q'.ofNat 2 * (dmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
    ≤ dmomN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
      + dmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1))
      + Q'.ofNat 2 * (acN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2)))

/-- **`FullRangeFloor w s`** — the SAME `−2` floor, but on the FULL-range / Fourier-square moments
`acNfull`, `dmomNfull` (identity (⋆)/(⋆⋆)).  This is the truncation-free object on which the theta /
discrete-Gaussian saddle bound is clean and standard. -/
def FullRangeFloor (w : Q') (s : Nat) : Prop :=
  Q'.ofNat 2 * (dmomNfull w (s + 1) * (acNfull w s * acNfull w (s + 2)))
    ≤ dmomNfull w s * (acNfull w (s + 1) * acNfull w (s + 2))
      + dmomNfull w (s + 2) * (acNfull w s * acNfull w (s + 1))
      + Q'.ofNat 2 * (acNfull w s * (acNfull w (s + 1) * acNfull w (s + 2)))

/-! ## 3. The two named-open residuals of the reframing. -/

/-- **R1 — `SaddleVarianceFloor w`** (the real content).  The `−2` curvature floor on the FULL-range
Fourier-square moments, ∀ window `s`.  By (⋆)/(⋆⋆) this is the second-difference-in-degree of the
theta-tilted position variance `κ₂(t) = ⟨D²⟩_t`,

    Δ²_t κ₂(t) ≥ −2 ,      κ₂(t) = variance of `D = t−2p` under `μ_t(p) ∝ coeffW(w,p)·coeffW(w,t−p)`,

i.e. the parity oscillation of a discrete-Gaussian (theta) variance is bounded below by `−2`.  This is a
clean, well-posed saddle / Laplace statement (Poisson summation / Jacobi θ; `q→1` local CLT), the
truncation-FREE home of the global Gaussian-decay estimate.  Corner-tight: `→ −2` at even-`s`, `w → 0`.
The base window `s = 0` is discharged unconditionally by `fullRangeFloor_zero` (§4.5); the residual is
the uniform-in-`s` tail (see §5).  NAMED-OPEN (never `sorry`; the `s = 0` face is proved). -/
structure SaddleVarianceFloor (w : Q') : Type where
  floor : ∀ s, FullRangeFloor w s

/-- **R2 — `WindowTailTransfer w`** (where the truncation reappears).  The per-window IMPLICATION that
the WINDOWED floor follows from the full-range floor.  The window `n = s+1` drops, for `t = s+2`, the
two boundary terms `p ∈ {s+1, s+2}` (large `|D|`, exponentially small `coeffW` weight); the transfer is
the sign/smallness accounting that these dropped tails do not push `Δ²⟨D²⟩` below `−2`.  Sign-definite
and exp-small at small `w` / large `s`; where larger (large `w`) the floor has large positive slack.
Elementary but NOT identically free.  NAMED-OPEN (never `sorry`). -/
structure WindowTailTransfer (w : Q') : Type where
  transfer : ∀ s, FullRangeFloor w s → WindowedFloor w s

/-! ## 4. THE COMPOSITE — `TwoPointTieSubleading` from the circle/Fourier reframing. -/

/-- **`circleFourier_twoPointTie` — THE REDUCTION.**  R1 (`SaddleVarianceFloor`, the clean theta saddle
floor on the truncation-free Fourier-square moments) plus R2 (`WindowTailTransfer`, the elementary
window-tail transfer) inhabit `MeanComplementClose.TwoPointTieSubleading w` — hence, through the proved
exact ledger `xmsd_of_twoPointTie`/`meanExpConvex_of_twoPointTie`, the fusion-window mean-convexity leaf.
Pure modus ponens over the two residual fields: genuinely axiom-clean, no `sorry`, no algebra faked. -/
def circleFourier_twoPointTie {w : Q'}
    (R1 : SaddleVarianceFloor w) (R2 : WindowTailTransfer w) :
    TwoPointTieSubleading w where
  d2var := fun s => R2.transfer s (R1.floor s)

/-- **`circleFourier_meanExpConvex` — the composite through to `MeanExpConvex`.**  Chains the reduction
above through the existing proved `meanExpConvex_of_twoPointTie`. -/
def circleFourier_meanExpConvex {w : Q'}
    (R1 : SaddleVarianceFloor w) (R2 : WindowTailTransfer w) :
    FusionMarginMonotone.MeanExpConvex w :=
  meanExpConvex_of_twoPointTie (circleFourier_twoPointTie R1 R2)

/-! ## 4.5 The corner base case `s = 0` of R1 is PROVED (not named-open).

At the corner-saturating even window `s = 0` the full-range floor is not merely a named residual: it
is a genuine, axiom-clean theorem.  Two exact mass–moment facts collapse the transcendental content:

  * `dmomNfull w 1 ≃ acNfull w 1` — at `t = 1` every antidiagonal square is `D² = (1−2p)² = 1`
    (`dsq 0 1 = dsq 1 1 = 1`), so the tilted second moment coincides with the mass.  This is the
    exact two-point tie `⟨D²⟩_1 = 1`.
  * `dmomNfull w 0 ≃ 0` — at `t = 0` the only lattice point is `D = 0`, so `⟨D²⟩_0 = 0`.

With these the floor reduces to the MANIFEST nonnegativity `0 ≤ dmomNfull w 2 · (acNfull w 0 · acNfull
w 1)` (the cleared slack is `RHS − LHS ≃ 16·c₀⁴c₁c₂ = 96·w¹¹ ≥ 0`, matching the numerical pilots).
This discharges the tightest corner, where `Δ²⟨D²⟩ → −2` as `w → 0` — so the floor is proved exactly
where it is saturated.  It does NOT close R1 (which quantifies over ALL `s`): for `s ≥ 1` the cleared
slack polynomial acquires sign-changing coefficients of degree growing like `O(s²)` (verified
symbolically), so it is no longer a manifest sum of `coeffW`-products but a genuine positivity
certificate with no uniform-in-`s` form — the residual `SaddleVarianceFloor` isolates. -/

/-- **`fullRangeFloor_zero` — the `s = 0` base case of R1, PROVED (axiom-clean).**  See the section
docstring: the full-range curvature floor holds at the corner-saturating even window `s = 0` for every
`0 ≤ w`, reducing to `0 ≤ dmomNfull w 2 · (acNfull w 0 · acNfull w 1)`. -/
theorem fullRangeFloor_zero {w : Q'} (hw : (0 : Q') ≤ w) : FullRangeFloor w 0 := by
  show Q'.ofNat 2 * (dmomNfull w 1 * (acNfull w 0 * acNfull w 2))
      ≤ dmomNfull w 0 * (acNfull w 1 * acNfull w 2)
        + dmomNfull w 2 * (acNfull w 0 * acNfull w 1)
        + Q'.ofNat 2 * (acNfull w 0 * (acNfull w 1 * acNfull w 2))
  -- (1) middle mass–moment coincidence  dmomNfull w 1 ≃ acNfull w 1  (every D² = 1 at t = 1)
  have hD1A1 : (dmomNfull w 1).eqv (acNfull w 1) := by
    show (((0 : Q') + Q'.ofNat (dsq 0 1) * (coeffW w 0 * coeffW w (1 - 0)))
            + Q'.ofNat (dsq 1 1) * (coeffW w 1 * coeffW w (1 - 1))).eqv
         (((0 : Q') + coeffW w 0 * coeffW w (1 - 0))
            + coeffW w 1 * coeffW w (1 - 1))
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl 0) (Q'.one_mul_eqv _))
      (Q'.one_mul_eqv _)
  -- (2) boundary moment vanishes  dmomNfull w 0 ≃ 0  (only D = 0 at t = 0)
  have hD0 : (dmomNfull w 0).eqv 0 := by
    show ((0 : Q') + Q'.ofNat (dsq 0 0) * (coeffW w 0 * coeffW w (0 - 0))).eqv 0
    exact Q'.eqv_trans _ _ _ (q_zero_add_eqv _) (Q'.zero_mul_eqv _)
  -- nonnegativity of the surviving slack term
  have hD2n : (0 : Q') ≤ dmomNfull w 2 := dmomN_nonneg hw 3 2
  have hA0n : (0 : Q') ≤ acNfull w 0 := acN_nonneg hw 1 0
  have hA1n : (0 : Q') ≤ acNfull w 1 := acN_nonneg hw 2 1
  have hterm2n : (0 : Q') ≤ dmomNfull w 2 * (acNfull w 0 * acNfull w 1) :=
    Q'.mul_nonneg _ _ hD2n (Q'.mul_nonneg _ _ hA0n hA1n)
  -- LHS ≃ T  (exactly the third RHS term, using dmomNfull w 1 ≃ acNfull w 1)
  have hLHSeq :
      (Q'.ofNat 2 * (dmomNfull w 1 * (acNfull w 0 * acNfull w 2))).eqv
        (Q'.ofNat 2 * (acNfull w 0 * (acNfull w 1 * acNfull w 2))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ hD1A1)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (by ring_qeqv)
  -- term1 = dmomNfull w 0 · (A1·A2) ≃ 0
  have hterm1zero : (dmomNfull w 0 * (acNfull w 1 * acNfull w 2)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hD0) (Q'.zero_mul_eqv _)
  -- RHS ≃ term2 + T
  have hRHSeq :
      (dmomNfull w 0 * (acNfull w 1 * acNfull w 2)
        + dmomNfull w 2 * (acNfull w 0 * acNfull w 1)
        + Q'.ofNat 2 * (acNfull w 0 * (acNfull w 1 * acNfull w 2))).eqv
        (dmomNfull w 2 * (acNfull w 0 * acNfull w 1)
          + Q'.ofNat 2 * (acNfull w 0 * (acNfull w 1 * acNfull w 2))) := by
    refine Q'.add_eqv_congr_right _ _ _ ?_
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hterm1zero) (q_zero_add_eqv _)
  -- T ≤ term2 + T  (add the nonnegative slack term on the left)
  have hstep :
      (Q'.ofNat 2 * (acNfull w 0 * (acNfull w 1 * acNfull w 2)))
        ≤ dmomNfull w 2 * (acNfull w 0 * acNfull w 1)
          + Q'.ofNat 2 * (acNfull w 0 * (acNfull w 1 * acNfull w 2)) := by
    have h0 := Q'.add_le_add_right 0 (dmomNfull w 2 * (acNfull w 0 * acNfull w 1))
      (Q'.ofNat 2 * (acNfull w 0 * (acNfull w 1 * acNfull w 2))) hterm2n
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (q_zero_add_eqv _)) h0
  -- LHS ≃ T ≤ term2 + T ≃ RHS
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHSeq)
    (Q'.le_trans' _ _ _ hstep (Q'.ge_of_eqv hRHSeq))

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `circleFourier_twoPointTie` — `SaddleVarianceFloor w → WindowTailTransfer w → TwoPointTieSubleading w`
    (pure modus ponens over the residual fields).
  * `circleFourier_meanExpConvex` — the composite `… → MeanExpConvex w`.
  * `fullRangeFloor_zero` — the `s = 0` base case of R1 (`FullRangeFloor w 0`), the corner-saturating
    even window where `Δ²⟨D²⟩ → −2` as `w → 0`.  Genuine `Q'`-inequality theorem, not a residual field.

NAMED OPEN (Type-level structures, never `sorry`):
  * `SaddleVarianceFloor w` (**R1**) — the `−2` floor on the FULL-range Fourier-square moments, ∀ `s`;
    the clean theta / discrete-Gaussian saddle bound carrying ALL the global Gaussian-decay content.
    The base case `s = 0` is PROVED (`fullRangeFloor_zero`).  The residual is the uniform-in-`s` tail:
    the leading `w²` coefficient of `⟨D²⟩_{2m}` is EXACTLY `C(2m) = 8m(m+2)/(m+1)²` (even; `6, 64/9,
    15/2, … ↑ 8`) and `1` (odd, two-point tie), so the corner slack `→ (C(s)+C(s+2))·w² > 0`; but for
    `s ≥ 1` the CLEARED slack polynomial has sign-changing coefficients of degree `O(s²)` (no manifest
    `coeffW`-product certificate), which is why this remains a genuine positivity residual.
  * `WindowTailTransfer w` (**R2**) — the window-tail transfer (where the finite-window truncation
    reappears): the full-range window `t+1` for `t = s+1, s+2` drops the large-`|D|` boundary terms
    `p ∈ {s+1, s+2}` present in the fixed window `n = s+1`; sign-definite, exp-small at the corner,
    non-free.  Not attempted here.

DOCUMENTED (not a Lean field — the Fourier-integral side of (⋆)/(⋆⋆)):
  * the identity `acNfull w t = [f_w²]_t` and `dmomNfull w t = −Φ_t''(0)` — validated to machine
    precision in the numerical pilot; formalizing the integral side is a routine, NON-load-bearing
    obligation over the `Semicircle*` constructive Riemann-sum circle-integral substrate.
-/

end YMGap.Continuum.CircleFourierPowerModel

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CircleFourierPowerModel.circleFourier_twoPointTie
#print axioms YMGap.Continuum.CircleFourierPowerModel.circleFourier_meanExpConvex
#print axioms YMGap.Continuum.CircleFourierPowerModel.fullRangeFloor_zero
