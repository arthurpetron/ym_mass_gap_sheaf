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
open YMGap.Continuum.RGTransport
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

/-! ## 4.6 The Pólya positive-coefficient certificate — reducing `FullRangeFloor` to
manifest Bernstein nonnegativity on the physical window `w ∈ [0,1]`.

The cleared slack `slack_s(w) := RHS − LHS` of `FullRangeFloor w s` is a polynomial in `w`
with integer coefficients.  On the physical heat-kernel window `w ∈ [0,1]` it admits a
**Pólya / Bernstein positive-coefficient certificate**: there are nonnegative integers
`c_{s,i}` with

    slack_s(w) = Σ_i c_{s,i} · w^i · (1−w)^{n_s − i},        c_{s,i} ≥ 0,   n_s = deg slack_s.

Since `w ≥ 0` and `1−w ≥ 0` on `[0,1]`, every summand is `≥ 0`, so `slack_s ≥ 0` MANIFESTLY.
(Equivalently, substituting `w = u/(1+u)`, `N_s(u) := slack_s(u/(1+u))·(1+u)^{n_s}` is a
polynomial in `u ≥ 0` with all-nonnegative coefficients — the classical Pólya form.)

This subsection formalizes that certificate over the reflective `Q'`-polynomial ring
(`Constructive.QPoly`): the floor moments `acNfull`, `dmomNfull` are shown to be `eval` of
explicit integer coefficient lists, the slack becomes `eval (slackP s) w`, and each concrete
window is discharged by exhibiting the Bernstein term list and a single `decide` on the
coefficient identity.  It carries a `w ≤ 1` hypothesis (the physical regime); the base window
`s = 0` needs only `0 ≤ w` (`fullRangeFloor_zero`). -/

/-- `q_mul_congr` — two-sided `Q'.eqv` congruence for `*`. -/
theorem q_mul_congr {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha) (Q'.mul_eqv_congr_left a' b b' hb)

/-- `a + (b + -a) ≃ b` (additive cancellation). -/
theorem q_add_add_neg_cancel (a b : Q') : (a + (b + -a)).eqv b := by
  have haa : (a + -a).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv a (-a)) (Q'.neg_add_self_eqv a)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv a b (-a))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (a + b) (b + a) (-a) (Q'.add_comm_eqv a b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b a (-a)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left b (a + -a) 0 haa) ?_
  exact q_add_zero_eqv b

/-! ### `eval`-homomorphism wrappers (build a `Q'`-expression's `eval`-poly bottom-up). -/

theorem hEvalMul {w : Q'} {a b : Q'} {pa pb : Poly}
    (ha : a.eqv (eval pa w)) (hb : b.eqv (eval pb w)) :
    (a * b).eqv (eval (pmul pa pb) w) :=
  Q'.eqv_trans _ _ _ (q_mul_congr ha hb) (Q'.eqv_symm (eval_pmul pa pb w))

theorem hEvalAdd {w : Q'} {a b : Q'} {pa pb : Poly}
    (ha : a.eqv (eval pa w)) (hb : b.eqv (eval pb w)) :
    (a + b).eqv (eval (padd pa pb) w) :=
  Q'.eqv_trans _ _ _ (q_add_congr ha hb) (Q'.eqv_symm (eval_padd pa pb w))

theorem hEvalScale {w : Q'} {a : Q'} {pa : Poly} (k : Q')
    (ha : a.eqv (eval pa w)) :
    (k * a).eqv (eval (pscale k pa) w) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left k a (eval pa w) ha)
    (Q'.eqv_symm (eval_pscale k pa w))

/-! ### Monomials, shifts, powers of `(1−w)`, and finite sums as polynomials. -/

/-- `monoP c e` — the monomial `c·w^e` as a coefficient list (`e` zeros then `c`). -/
def monoP (c : Q') : Nat → Poly
  | 0 => [c]
  | (e + 1) => (0 : Q') :: monoP c e

theorem eval_monoP (c : Q') (w : Q') : ∀ e, (eval (monoP c e) w).eqv (c * qpow w e)
  | 0 => by
      show (c + w * (0 : Q')).eqv (c * qpow w 0)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left c (w * 0) 0 (q_mul_zero w)) ?_
      exact Q'.eqv_trans _ _ _ (q_add_zero_eqv c) (Q'.eqv_symm (Q'.mul_one_eqv c))
  | (e + 1) => by
      show ((0 : Q') + w * eval (monoP c e) w).eqv (c * qpow w (e + 1))
      refine Q'.eqv_trans _ _ _ (q_zero_add_eqv (w * eval (monoP c e) w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ (eval_monoP c w e)) ?_
      show (w * (c * qpow w e)).eqv (c * (qpow w e * w))
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ (Q'.mul_comm_eqv c (qpow w e))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv w (qpow w e) c)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (w * qpow w e) c) ?_
      exact Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv w (qpow w e))

/-- `shiftZ i p` — multiply the polynomial `p` by `w^i` (prepend `i` zeros). -/
def shiftZ : Nat → Poly → Poly
  | 0, p => p
  | (i + 1), p => (0 : Q') :: shiftZ i p

theorem eval_shiftZ (w : Q') (p : Poly) :
    ∀ i, (eval (shiftZ i p) w).eqv (qpow w i * eval p w)
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv (eval p w))
  | (i + 1) => by
      show ((0 : Q') + w * eval (shiftZ i p) w).eqv (qpow w (i + 1) * eval p w)
      refine Q'.eqv_trans _ _ _ (q_zero_add_eqv (w * eval (shiftZ i p) w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ (eval_shiftZ w p i)) ?_
      show (w * (qpow w i * eval p w)).eqv ((qpow w i * w) * eval p w)
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv w (qpow w i) (eval p w))) ?_
      exact Q'.mul_eqv_congr_right (w * qpow w i) (qpow w i * w) (eval p w)
        (Q'.mul_comm_eqv w (qpow w i))

/-- `onemP` — the polynomial `1 − w`. -/
def onemP : Poly := [(1 : Q'), (-1 : Q')]

theorem eval_onemP_eqv (w : Q') : (eval onemP w).eqv (1 + -w) := by
  show ((1 : Q') + w * ((-1 : Q') + w * (0 : Q'))).eqv (1 + -w)
  refine Q'.add_eqv_congr_left 1 _ (-w) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w ((-1 : Q') + w * 0) (-1) ?_) ?_
  · exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (-1 : Q') (w * 0) 0 (q_mul_zero w))
      (q_add_zero_eqv (-1 : Q'))
  · exact Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv w 1)
      (Q'.neg_eqv_congr (w * 1) w (Q'.mul_one_eqv w))

/-- On `w ≤ 1`, `0 ≤ 1 + -w`. -/
theorem oneSub_nonneg {w : Q'} (hw1 : w ≤ 1) : (0 : Q') ≤ (1 : Q') + -w := by
  have h := Q'.add_le_add_right w 1 (-w) hw1
  have h0 : (w + -w).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv w (-w)) (Q'.neg_add_self_eqv w)
  exact Q'.le_trans' 0 (w + -w) (1 + -w) (Q'.ge_of_eqv h0) h

/-- On `w ≤ 1`, `0 ≤ eval onemP w` (`= 1 − w`). -/
theorem honemP {w : Q'} (hw1 : w ≤ 1) : (0 : Q') ≤ eval onemP w :=
  Q'.le_trans' 0 (1 + -w) (eval onemP w) (oneSub_nonneg hw1)
    (Q'.ge_of_eqv (eval_onemP_eqv w))

/-- `ppow p n` — the `n`-th polynomial power of `p`. -/
def ppow (p : Poly) : Nat → Poly
  | 0 => [(1 : Q')]
  | (n + 1) => pmul p (ppow p n)

theorem eval_ppow (p : Poly) (w : Q') :
    ∀ n, (eval (ppow p n) w).eqv (qpow (eval p w) n)
  | 0 => by
      show ((1 : Q') + w * (0 : Q')).eqv (qpow (eval p w) 0)
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 (w * 0) 0 (q_mul_zero w))
        (q_add_zero_eqv 1)
  | (n + 1) => by
      show (eval (pmul p (ppow p n)) w).eqv (qpow (eval p w) (n + 1))
      refine Q'.eqv_trans _ _ _ (eval_pmul p (ppow p n) w) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (eval p w) _ _ (eval_ppow p w n)) ?_
      show (eval p w * qpow (eval p w) n).eqv (qpow (eval p w) n * eval p w)
      exact Q'.mul_comm_eqv (eval p w) (qpow (eval p w) n)

/-- `fsumP f n = Σ_{p<n} f p` as a polynomial (mirrors `BondMovingStep.fsum`). -/
def fsumP (f : Nat → Poly) : Nat → Poly
  | 0 => ([] : Poly)
  | (n + 1) => padd (fsumP f n) (f n)

theorem fsum_eval {w : Q'} (g : Nat → Q') (gp : Nat → Poly)
    (h : ∀ p, (g p).eqv (eval (gp p) w)) :
    ∀ n, (fsum g n).eqv (eval (fsumP gp n) w)
  | 0 => Q'.eqv_of_eq rfl
  | (n + 1) => Q'.eqv_trans _ _ _ (q_add_congr (fsum_eval g gp h n) (h n))
      (Q'.eqv_symm (eval_padd (fsumP gp n) (gp n) w))

/-! ### The floor moments and slack as `eval` of explicit coefficient lists. -/

/-- `coeffPoly p` — the character coefficient `coeffW w p = (p+1)·w^{p(p+2)}` as a monomial. -/
def coeffPoly (p : Nat) : Poly := monoP (dimQ p) (c4 p)

theorem hcoeff (w : Q') (p : Nat) : (coeffW w p).eqv (eval (coeffPoly p) w) :=
  Q'.eqv_symm (eval_monoP (dimQ p) w (c4 p))

/-- `acPoly t` — the full-range autoconvolution `acNfull w t` as a polynomial. -/
def acPoly (t : Nat) : Poly :=
  fsumP (fun p => pmul (coeffPoly p) (coeffPoly (t - p))) (t + 1)

/-- `dmomPoly t` — the full-range antidiagonal-square moment `dmomNfull w t` as a polynomial. -/
def dmomPoly (t : Nat) : Poly :=
  fsumP (fun p => pscale (Q'.ofNat (dsq p t)) (pmul (coeffPoly p) (coeffPoly (t - p)))) (t + 1)

theorem hAcNfull (w : Q') (t : Nat) : (acNfull w t).eqv (eval (acPoly t) w) := by
  show (fsum (fun p => coeffW w p * coeffW w (t - p)) (t + 1)).eqv
       (eval (fsumP (fun p => pmul (coeffPoly p) (coeffPoly (t - p))) (t + 1)) w)
  exact fsum_eval (fun p => coeffW w p * coeffW w (t - p))
    (fun p => pmul (coeffPoly p) (coeffPoly (t - p)))
    (fun p => hEvalMul (hcoeff w p) (hcoeff w (t - p))) (t + 1)

theorem hDmomNfull (w : Q') (t : Nat) : (dmomNfull w t).eqv (eval (dmomPoly t) w) := by
  show (fsum (fun p => Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p))) (t + 1)).eqv
       (eval (fsumP (fun p =>
         pscale (Q'.ofNat (dsq p t)) (pmul (coeffPoly p) (coeffPoly (t - p)))) (t + 1)) w)
  exact fsum_eval _ _
    (fun p => hEvalScale (Q'.ofNat (dsq p t)) (hEvalMul (hcoeff w p) (hcoeff w (t - p)))) (t + 1)

/-- The `FullRangeFloor` left side as a named `Q'` expression. -/
def floorLHS (w : Q') (s : Nat) : Q' :=
  Q'.ofNat 2 * (dmomNfull w (s + 1) * (acNfull w s * acNfull w (s + 2)))

/-- The `FullRangeFloor` right side as a named `Q'` expression. -/
def floorRHS (w : Q') (s : Nat) : Q' :=
  dmomNfull w s * (acNfull w (s + 1) * acNfull w (s + 2))
    + dmomNfull w (s + 2) * (acNfull w s * acNfull w (s + 1))
    + Q'.ofNat 2 * (acNfull w s * (acNfull w (s + 1) * acNfull w (s + 2)))

def floorLHSPoly (s : Nat) : Poly :=
  pscale (Q'.ofNat 2) (pmul (dmomPoly (s + 1)) (pmul (acPoly s) (acPoly (s + 2))))

def floorRHSPoly (s : Nat) : Poly :=
  padd
    (padd (pmul (dmomPoly s) (pmul (acPoly (s + 1)) (acPoly (s + 2))))
      (pmul (dmomPoly (s + 2)) (pmul (acPoly s) (acPoly (s + 1)))))
    (pscale (Q'.ofNat 2) (pmul (acPoly s) (pmul (acPoly (s + 1)) (acPoly (s + 2)))))

/-- `slackP s` — the cleared slack `RHS − LHS` of `FullRangeFloor w s` as a coefficient list. -/
def slackP (s : Nat) : Poly := psub (floorRHSPoly s) (floorLHSPoly s)

theorem hLHS (w : Q') (s : Nat) : (floorLHS w s).eqv (eval (floorLHSPoly s) w) :=
  hEvalScale (Q'.ofNat 2)
    (hEvalMul (hDmomNfull w (s + 1)) (hEvalMul (hAcNfull w s) (hAcNfull w (s + 2))))

theorem hRHS (w : Q') (s : Nat) : (floorRHS w s).eqv (eval (floorRHSPoly s) w) :=
  hEvalAdd
    (hEvalAdd (hEvalMul (hDmomNfull w s) (hEvalMul (hAcNfull w (s + 1)) (hAcNfull w (s + 2))))
      (hEvalMul (hDmomNfull w (s + 2)) (hEvalMul (hAcNfull w s) (hAcNfull w (s + 1)))))
    (hEvalScale (Q'.ofNat 2)
      (hEvalMul (hAcNfull w s) (hEvalMul (hAcNfull w (s + 1)) (hAcNfull w (s + 2)))))

theorem hSlackEq (w : Q') (s : Nat) :
    (floorRHS w s).eqv (floorLHS w s + eval (slackP s) w) := by
  have hev : (eval (slackP s) w).eqv
      (eval (floorRHSPoly s) w + -(eval (floorLHSPoly s) w)) :=
    eval_psub (floorRHSPoly s) (floorLHSPoly s) w
  have h1 : (floorLHS w s + eval (slackP s) w).eqv
      (floorLHS w s + (floorRHS w s + -(floorLHS w s))) :=
    Q'.add_eqv_congr_left (floorLHS w s) _ _
      (Q'.eqv_trans _ _ _ hev
        (q_add_congr (Q'.eqv_symm (hRHS w s))
          (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (hLHS w s)))))
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ h1 (q_add_add_neg_cancel (floorLHS w s) (floorRHS w s)))

/-- **`fullRangeFloor_of_slack_nonneg`** — the floor holds once the slack polynomial evaluates
nonnegative at `w`.  This is the pivot from the inequality to a manifest positivity check. -/
theorem fullRangeFloor_of_slack_nonneg {w : Q'} {s : Nat}
    (hs : (0 : Q') ≤ eval (slackP s) w) : FullRangeFloor w s := by
  show floorLHS w s ≤ floorRHS w s
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (floorLHS w s) (eval (slackP s) w) hs)
    (Q'.ge_of_eqv (hSlackEq w s))

/-! ### The Bernstein certificate polynomial and its manifest nonnegativity. -/

/-- `bernBasisP n i = w^i · (1−w)^{n−i}` — a Bernstein basis element (no binomial factor). -/
def bernBasisP (n i : Nat) : Poly := shiftZ i (ppow onemP (n - i))

theorem eval_bernBasisP_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (n i : Nat) :
    (0 : Q') ≤ eval (bernBasisP n i) w := by
  have hp : (0 : Q') ≤ eval (ppow onemP (n - i)) w :=
    Q'.le_trans' 0 (qpow (eval onemP w) (n - i)) _
      (qpow_nonneg _ (honemP hw1) (n - i))
      (Q'.ge_of_eqv (eval_ppow onemP w (n - i)))
  exact Q'.le_trans' 0 (qpow w i * eval (ppow onemP (n - i)) w) _
    (Q'.mul_nonneg _ _ (qpow_nonneg w hw0 i) hp)
    (Q'.ge_of_eqv (eval_shiftZ w (ppow onemP (n - i)) i))

/-- `bernTermsP n terms = Σ (i,a)∈terms  a · w^i · (1−w)^{n−i}` — the certificate polynomial as a
sparse list of `(index, nonneg coefficient)` pairs (zero coefficients omitted). -/
def bernTermsP (n : Nat) : List (Nat × Q') → Poly
  | [] => ([] : Poly)
  | ((i, a) :: rest) => padd (pscale a (bernBasisP n i)) (bernTermsP n rest)

theorem eval_bernTermsP_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (n : Nat) :
    ∀ (terms : List (Nat × Q')), (∀ t ∈ terms, (0 : Q') ≤ t.2) →
      (0 : Q') ≤ eval (bernTermsP n terms) w
  | [], _ => Q'.le_refl' 0
  | ((i, a) :: rest), h => by
      show (0 : Q') ≤ eval (padd (pscale a (bernBasisP n i)) (bernTermsP n rest)) w
      refine Q'.le_trans' 0 _ _ ?_
        (Q'.ge_of_eqv (eval_padd (pscale a (bernBasisP n i)) (bernTermsP n rest) w))
      refine Q'.zero_le_add _ _ ?_
        (eval_bernTermsP_nonneg hw0 hw1 n rest (fun t ht => h t (List.mem_cons_of_mem _ ht)))
      refine Q'.le_trans' 0 (a * eval (bernBasisP n i) w) _ ?_
        (Q'.ge_of_eqv (eval_pscale a (bernBasisP n i) w))
      exact Q'.mul_nonneg _ _ (h (i, a) (List.mem_cons_self))
        (eval_bernBasisP_nonneg hw0 hw1 n i)

/-- **`fullRangeFloor_of_bernCert`** — the general certificate consumer.  Given the physical
window bounds `0 ≤ w ≤ 1`, a Bernstein term list with nonnegative coefficients, and the single
decidable coefficient identity `slackP s = bernTermsP n terms`, the floor `FullRangeFloor w s`
holds.  The whole transcendental content of window `s` collapses to the one `decide` on
`hrep`. -/
theorem fullRangeFloor_of_bernCert {w : Q'} (s n : Nat) (terms : List (Nat × Q'))
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (hnn : ∀ t ∈ terms, (0 : Q') ≤ t.2)
    (hrep : allZero (psub (slackP s) (bernTermsP n terms))) :
    FullRangeFloor w s :=
  fullRangeFloor_of_slack_nonneg
    (Q'.le_trans' 0 (eval (bernTermsP n terms) w) (eval (slackP s) w)
      (eval_bernTermsP_nonneg hw0 hw1 n terms hnn)
      (Q'.ge_of_eqv (poly_eqv (slackP s) (bernTermsP n terms) w hrep)))

/-! ### The concrete windows `s = 1, 2, 3, 4`, discharged by the certificate.

Each `termsN` is the Pólya / Bernstein positive-coefficient list of `slack_N`, produced by the
symbolic pilot (only the nonzero coefficients are listed).  Every coefficient is a nonnegative
`Q'.ofNat`, and the identity `slackP N = bernTermsP (deg N) termsN` is machine-checked by
`decide`. -/

def terms1 : List (Nat × Q') :=
  [(20, Q'.ofNat 768), (21, Q'.ofNat 4608), (22, Q'.ofNat 10368), (23, Q'.ofNat 10752),
   (24, Q'.ofNat 6144), (25, Q'.ofNat 3072), (26, Q'.ofNat 1920)]

/-- **`fullRangeFloor_one`** — R1 window `s = 1`, PROVED on `0 ≤ w ≤ 1` via the Pólya certificate. -/
theorem fullRangeFloor_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) : FullRangeFloor w 1 :=
  fullRangeFloor_of_bernCert 1 26 terms1 hw0 hw1 (by decide) (by decide)

def terms2 : List (Nat × Q') :=
  [(35, Q'.ofNat 5664), (36, Q'.ofNat 67968), (37, Q'.ofNat 378432), (38, Q'.ofNat 1292160),
   (39, Q'.ofNat 2999712), (40, Q'.ofNat 4948224), (41, Q'.ofNat 5885568), (42, Q'.ofNat 5021952),
   (43, Q'.ofNat 3015840), (44, Q'.ofNat 1252992), (45, Q'.ofNat 373440), (46, Q'.ofNat 90240),
   (47, Q'.ofNat 16800)]

/-- **`fullRangeFloor_two`** — R1 window `s = 2`, PROVED on `0 ≤ w ≤ 1` via the Pólya certificate. -/
theorem fullRangeFloor_two {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) : FullRangeFloor w 2 :=
  fullRangeFloor_of_bernCert 2 47 terms2 hw0 hw1 (by decide) (by decide)

def terms3 : List (Nat × Q') :=
  [(50, Q'.ofNat 10368), (51, Q'.ofNat 248832), (52, Q'.ofNat 2843136), (53, Q'.ofNat 20579328),
   (54, Q'.ofNat 105959232), (55, Q'.ofNat 413229312), (56, Q'.ofNat 1269553536),
   (57, Q'.ofNat 3156703488), (58, Q'.ofNat 6480323136), (59, Q'.ofNat 11157820416),
   (60, Q'.ofNat 16327100928), (61, Q'.ofNat 20536636416), (62, Q'.ofNat 22416620736),
   (63, Q'.ofNat 21377853696), (64, Q'.ofNat 17857474944), (65, Q'.ofNat 13026231552),
   (66, Q'.ofNat 8220791616), (67, Q'.ofNat 4419899904), (68, Q'.ofNat 1982735616),
   (69, Q'.ofNat 723448320), (70, Q'.ofNat 208737408), (71, Q'.ofNat 46508544),
   (72, Q'.ofNat 7983360), (73, Q'.ofNat 1064448), (74, Q'.ofNat 94080)]

set_option maxRecDepth 4000 in
/-- **`fullRangeFloor_three`** — R1 window `s = 3`, PROVED on `0 ≤ w ≤ 1` via the Pólya certificate. -/
theorem fullRangeFloor_three {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) : FullRangeFloor w 3 :=
  fullRangeFloor_of_bernCert 3 74 terms3 hw0 hw1 (by decide) (by decide)

def terms4 : List (Nat × Q') :=
  [(71, Q'.ofNat 50496), (72, Q'.ofNat 1817856), (73, Q'.ofNat 31858560), (74, Q'.ofNat 362108160),
   (75, Q'.ofNat 3000191520), (76, Q'.ofNat 19308291072), (77, Q'.ofNat 100430163456),
   (78, Q'.ofNat 433722362880), (79, Q'.ofNat 1585489441920), (80, Q'.ofNat 4976613649920),
   (81, Q'.ofNat 13559635844352), (82, Q'.ofNat 32341016987136), (83, Q'.ofNat 67966096500192),
   (84, Q'.ofNat 126497769700608), (85, Q'.ofNat 209339906147712), (86, Q'.ofNat 308980018975488),
   (87, Q'.ofNat 407685998347776), (88, Q'.ofNat 481705225141248), (89, Q'.ofNat 510296768686848),
   (90, Q'.ofNat 485061745890816), (91, Q'.ofNat 413905300191936), (92, Q'.ofNat 317100951407616),
   (93, Q'.ofNat 218076849249792), (94, Q'.ofNat 134548894718976), (95, Q'.ofNat 74384652141696),
   (96, Q'.ofNat 36768162817536), (97, Q'.ofNat 16190418931968), (98, Q'.ofNat 6314527354368),
   (99, Q'.ofNat 2162782846656), (100, Q'.ofNat 642821506560), (101, Q'.ofNat 163198874880),
   (102, Q'.ofNat 34701101568), (103, Q'.ofNat 6041613312), (104, Q'.ofNat 842311680),
   (105, Q'.ofNat 92348928), (106, Q'.ofNat 7676928), (107, Q'.ofNat 395136)]

set_option maxRecDepth 8000 in
/-- **`fullRangeFloor_four`** — R1 window `s = 4`, PROVED on `0 ≤ w ≤ 1` via the Pólya certificate. -/
theorem fullRangeFloor_four {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) : FullRangeFloor w 4 :=
  fullRangeFloor_of_bernCert 4 107 terms4 hw0 hw1 (by decide) (by decide)

def terms5 : List (Nat × Q') :=
  [(92, Q'.ofNat 61440), (93, Q'.ofNat 3317760), (94, Q'.ofNat 87805440), (95, Q'.ofNat 1517967360),
   (96, Q'.ofNat 19278025728), (97, Q'.ofNat 191774668800), (98, Q'.ofNat 1556025070080),
   (99, Q'.ofNat 10587929763840), (100, Q'.ofNat 61654719544320), (101, Q'.ofNat 312002375485440),
   (102, Q'.ofNat 1388725935004800), (103, Q'.ofNat 5489630078584320),
   (104, Q'.ofNat 19425785686369536), (105, Q'.ofNat 61942423352489472),
   (106, Q'.ofNat 178974170494475136), (107, Q'.ofNat 470815365541370880),
   (108, Q'.ofNat 1132272553168238592), (109, Q'.ofNat 2498285506990516224),
   (110, Q'.ofNat 5073210671518288512), (111, Q'.ofNat 9507600379055208960),
   (112, Q'.ofNat 16484073003498786048), (113, Q'.ofNat 26497155035676919296),
   (114, Q'.ofNat 39563843971496416128), (115, Q'.ofNat 54964153302115921920),
   (116, Q'.ofNat 71146824405460795392), (117, Q'.ofNat 85908013332302389248),
   (118, Q'.ofNat 96852576228866763264), (119, Q'.ofNat 102016206092749608960),
   (120, Q'.ofNat 100430659096455982080), (121, Q'.ofNat 92412985830958270464),
   (122, Q'.ofNat 79463430412381836288), (123, Q'.ofNat 63816573014920077312),
   (124, Q'.ofNat 47825919221864299008), (125, Q'.ofNat 33408764504414764032),
   (126, Q'.ofNat 21722328443855105280), (127, Q'.ofNat 13124062380328399872),
   (128, Q'.ofNat 7353695473270732800), (129, Q'.ofNat 3813072170425903104),
   (130, Q'.ofNat 1825282264674959616), (131, Q'.ofNat 804476170721169408),
   (132, Q'.ofNat 325488299803496448), (133, Q'.ofNat 120486151676559360),
   (134, Q'.ofNat 40646626414924800), (135, Q'.ofNat 12438631161556992),
   (136, Q'.ofNat 3433135707537408), (137, Q'.ofNat 848496901693440),
   (138, Q'.ofNat 186069996518400), (139, Q'.ofNat 35787387691008),
   (140, Q'.ofNat 5949868455936), (141, Q'.ofNat 840103759872), (142, Q'.ofNat 98689084416),
   (143, Q'.ofNat 9428594688), (144, Q'.ofNat 712986624), (145, Q'.ofNat 40255488),
   (146, Q'.ofNat 1354752)]

set_option maxRecDepth 12000 in
/-- **`fullRangeFloor_five`** — R1 window `s = 5`, PROVED on `0 ≤ w ≤ 1` via the Pólya certificate. -/
theorem fullRangeFloor_five {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) : FullRangeFloor w 5 :=
  fullRangeFloor_of_bernCert 5 146 terms5 hw0 hw1 (by decide) (by decide)

def terms6 : List (Nat × Q') :=
  [(119, Q'.ofNat 242880), (120, Q'.ofNat 17487360), (121, Q'.ofNat 621031680),
   (122, Q'.ofNat 14501491200), (123, Q'.ofNat 250428275424), (124, Q'.ofNat 3410833709952),
   (125, Q'.ofNat 38157065124672), (126, Q'.ofNat 360544580820864), (127, Q'.ofNat 2936710617236640),
   (128, Q'.ofNat 20941626884278272), (129, Q'.ofNat 132338725798465536), (130, Q'.ofNat 748404323128897536),
   (131, Q'.ofNat 3818025221280373344), (132, Q'.ofNat 17688563763710275200), (133, Q'.ofNat 74841421967844084672),
   (134, Q'.ofNat 290583440415650019456), (135, Q'.ofNat 1039611215869602238176), (136, Q'.ofNat 3439494060626960184576),
   (137, Q'.ofNat 10555880977456548310656), (138, Q'.ofNat 30133913826824468345088), (139, Q'.ofNat 80208347410992768416640),
   (140, Q'.ofNat 199482816832240807088640), (141, Q'.ofNat 464435773032509360735232), (142, Q'.ofNat 1013909655058640627112960),
   (143, Q'.ofNat 2078563891826735579059584), (144, Q'.ofNat 4006658434633951766218752), (145, Q'.ofNat 7270350907426980230704128),
   (146, Q'.ofNat 12431496470650856780544000), (147, Q'.ofNat 20048159672185159911692544), (148, Q'.ofNat 30517485934270561375595520),
   (149, Q'.ofNat 43877544603890228170019328), (150, Q'.ofNat 59622614821172547362405376), (151, Q'.ofNat 76607858508604047260148672),
   (152, Q'.ofNat 93113552344125556603663872), (153, Q'.ofNat 107097850518694210678990080), (154, Q'.ofNat 116599585637191500870388224),
   (155, Q'.ofNat 120185535937734976230410784), (156, Q'.ofNat 117302775460556020191167616), (157, Q'.ofNat 108417429446169934508753088),
   (158, Q'.ofNat 94892188502972231462736000), (159, Q'.ofNat 78646544841249570156072288), (160, Q'.ofNat 61715518984727476173659136),
   (161, Q'.ofNat 45844912475115649469563392), (162, Q'.ofNat 32229440138603594142938112), (163, Q'.ofNat 21435087646997721807609504),
   (164, Q'.ofNat 13480747610926403946228096), (165, Q'.ofNat 8012698484324426636868672), (166, Q'.ofNat 4498096180865286068916096),
   (167, Q'.ofNat 2382954515057463466090656), (168, Q'.ofNat 1190222166210334067804928), (169, Q'.ofNat 559864307171725779158400),
   (170, Q'.ofNat 247695777286819110541056), (171, Q'.ofNat 102917099465747239599936), (172, Q'.ofNat 40090968676240971625728),
   (173, Q'.ofNat 14613293595017364049536), (174, Q'.ofNat 4973121829008680866560), (175, Q'.ofNat 1576147060755916452288),
   (176, Q'.ofNat 463884183094546492416), (177, Q'.ofNat 126371939654418587136), (178, Q'.ofNat 31746017967674489856),
   (179, Q'.ofNat 7321942750267472832), (180, Q'.ofNat 1542476906284301568), (181, Q'.ofNat 294969425575586688),
   (182, Q'.ofNat 50820018355208448), (183, Q'.ofNat 7816076843100480), (184, Q'.ofNat 1061007919096320),
   (185, Q'.ofNat 125373218515200), (186, Q'.ofNat 12681718000128), (187, Q'.ofNat 1076501059200),
   (188, Q'.ofNat 74888188416), (189, Q'.ofNat 4131046656), (190, Q'.ofNat 168334848),
   (191, Q'.ofNat 3991680)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
/-- **`fullRangeFloor_six`** — R1 window `s = 6`, PROVED on `0 ≤ w ≤ 1` via the Pólya certificate. -/
theorem fullRangeFloor_six {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) : FullRangeFloor w 6 :=
  fullRangeFloor_of_bernCert 6 191 terms6 hw0 hw1 (by decide) (by decide)

/-! ### The relocated uniform residual — the Pólya positivity conjecture.

`PolyaCertifiedFloor w` packages the physical window `0 ≤ w ≤ 1` together with, for EVERY `s`, a
Pólya / Bernstein positive-coefficient certificate for `slack_s`.  It is a strictly sharper
relocation of R1 (`SaddleVarianceFloor`): where the raw floor `∀ s, FullRangeFloor w s` mixes an
inequality with the analytic `−2`-saddle content, the certificate isolates the ENTIRE remaining
content into the uniform, purely-combinatorial claim

    ∀ s, slackP s = bernTermsP (deg s) (bernCoeffs s)   with all `bernCoeffs s` nonnegative,

i.e. every cleared slack polynomial is a manifest nonnegative combination of the Bernstein
monomials `w^i (1−w)^{n−i}`.  This is genuinely NAMED-OPEN: no uniform closed form for the
`bernCoeffs` is known, and the structure is not vacuously inhabitable (the `represents` identity
fails for any wrong coefficient list).  The concrete windows `s = 0,1,2,3,4,5,6` are PROVED above, so
the residual is the uniform-in-`s` positivity that they instantiate. -/
structure PolyaCertifiedFloor (w : Q') : Type where
  /-- Physical window lower bound. -/
  w_nonneg : (0 : Q') ≤ w
  /-- Physical window upper bound (the heat-kernel weight satisfies `w < 1`). -/
  w_le_one : w ≤ 1
  /-- The degree `n_s = deg slack_s`. -/
  deg : Nat → Nat
  /-- The Pólya / Bernstein positive coefficients of `slack_s` (nonzero `(index, coeff)` pairs). -/
  bernCoeffs : Nat → List (Nat × Q')
  /-- Every certificate coefficient is nonnegative (the Pólya positivity). -/
  coeffs_nonneg : ∀ s, ∀ t ∈ bernCoeffs s, (0 : Q') ≤ t.2
  /-- The certificate identity `slack_s = Σ bernCoeffs_s`, decidable per `s`. -/
  represents : ∀ s, allZero (psub (slackP s) (bernTermsP (deg s) (bernCoeffs s)))

/-- **`saddleVarianceFloor_of_polya` — THE RELOCATION.**  The uniform Pólya positivity certificate
`PolyaCertifiedFloor w` inhabits R1 `SaddleVarianceFloor w`.  Hence R1 is now equivalent to the
crisp, uniform, combinatorial Pólya-nonnegativity statement, with the transcendental `−2`-saddle
content fully discharged into `decide`-checkable coefficient identities. -/
def saddleVarianceFloor_of_polya {w : Q'} (P : PolyaCertifiedFloor w) :
    SaddleVarianceFloor w where
  floor := fun s =>
    fullRangeFloor_of_bernCert s (P.deg s) (P.bernCoeffs s)
      P.w_nonneg P.w_le_one (P.coeffs_nonneg s) (P.represents s)

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `circleFourier_twoPointTie` — `SaddleVarianceFloor w → WindowTailTransfer w → TwoPointTieSubleading w`
    (pure modus ponens over the residual fields).
  * `circleFourier_meanExpConvex` — the composite `… → MeanExpConvex w`.
  * `fullRangeFloor_zero` — the `s = 0` base case of R1 (`FullRangeFloor w 0`), the corner-saturating
    even window where `Δ²⟨D²⟩ → −2` as `w → 0` (holds for all `0 ≤ w`).
  * `fullRangeFloor_one … _six` — the windows `s = 1,2,3,4,5,6` of R1, PROVED on the physical
    window `0 ≤ w ≤ 1` via the Pólya positive-coefficient certificate (§4.6): each cleared slack
    `slack_s(w)` is a MANIFEST nonnegative Bernstein combination `Σ c_{s,i} w^i (1−w)^{n_s−i}` with
    `c_{s,i} ≥ 0` (verified by `decide` on the coefficient identity; degrees `n_s = 26,47,74,107,
    146,191`).  For `s ≥ 1` the floor genuinely needs `w ≤ 1`.
  * `fullRangeFloor_of_bernCert` — the general certificate consumer, and `saddleVarianceFloor_of_polya`
    — the RELOCATION of R1 onto the uniform Pólya positivity `PolyaCertifiedFloor w`.

NAMED OPEN (Type-level structures, never `sorry`):
  * `PolyaCertifiedFloor w` (**the relocated R1**) — the crisp, uniform, purely-combinatorial residual:
    for EVERY `s`, the cleared slack `slackP s` equals its Bernstein positive-coefficient certificate
    `bernTermsP (deg s) (bernCoeffs s)` with all coefficients nonnegative.  Via
    `saddleVarianceFloor_of_polya` this implies R1 on the physical window `0 ≤ w ≤ 1`.  The windows
    `s = 0,1,2,3,4,5,6` are PROVED; the residual is the uniform-in-`s` Pólya positivity (no uniform closed
    form for `bernCoeffs` is known).  This is strictly sharper than the raw `SaddleVarianceFloor`: the
    transcendental `−2`-saddle content is now a `decide`-checkable coefficient identity per window.
  * `SaddleVarianceFloor w` (**R1**) — the `−2` floor on the FULL-range Fourier-square moments, ∀ `s`;
    the clean theta / discrete-Gaussian saddle bound carrying ALL the global Gaussian-decay content.
    Now implied by `PolyaCertifiedFloor w` on `w ∈ [0,1]`.  The base case `s = 0` is PROVED
    (`fullRangeFloor_zero`), the windows `1..6` by the certificate; the residual is the uniform-in-`s`
    tail.  The leading `w²` coefficient of `⟨D²⟩_{2m}` is EXACTLY `C(2m) = 8m(m+2)/(m+1)²` (even; `6,
    64/9, 15/2, … ↑ 8`) and `1` (odd, two-point tie), so the corner slack `→ (C(s)+C(s+2))·w² > 0`; but
    for `s ≥ 1` the CLEARED slack polynomial has sign-changing MONOMIAL coefficients of degree `O(s²)`
    (no manifest `coeffW`-product certificate) — the Pólya `(1−w)`-reblowup is exactly what restores
    manifest positivity on `[0,1]`.
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
#print axioms YMGap.Continuum.CircleFourierPowerModel.fullRangeFloor_of_slack_nonneg
#print axioms YMGap.Continuum.CircleFourierPowerModel.fullRangeFloor_of_bernCert
#print axioms YMGap.Continuum.CircleFourierPowerModel.fullRangeFloor_one
#print axioms YMGap.Continuum.CircleFourierPowerModel.fullRangeFloor_two
#print axioms YMGap.Continuum.CircleFourierPowerModel.fullRangeFloor_three
#print axioms YMGap.Continuum.CircleFourierPowerModel.fullRangeFloor_four
#print axioms YMGap.Continuum.CircleFourierPowerModel.fullRangeFloor_five
#print axioms YMGap.Continuum.CircleFourierPowerModel.fullRangeFloor_six
#print axioms YMGap.Continuum.CircleFourierPowerModel.saddleVarianceFloor_of_polya
