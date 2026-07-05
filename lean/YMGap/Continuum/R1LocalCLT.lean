/-
Track B / local-CLT — the CONSTRUCTIVE structural frame for the R1 corner residuals.

# Why this file exists (read first — load-bearing honesty)

The corner residuals (M1/M2 moment envelopes, Lemma C variance-curvature) are all corollaries of ONE
structural fact: the SU(2) fusion measure `μ_t(p) ∝ coeffW w p · coeffW w (t−p)` is **log-concave**.
The algebraic-certificate approach (per-`s` Bernstein families, cumulant Taylor expansions) fought the
uniform-in-`s` nature of these statements — they are moment bounds of a log-concave measure, hence a
*local central limit theorem*, uniform by construction.  This file begins the constructive local-CLT
frame from the log-concavity anchor.

# What this file provides (PROVED, axiom-clean, CONSTRUCTIVE)

  * `fusionMeasure_logConcave` — the two-body fusion weight `coeffW w p · coeffW w (t−p)` is
    log-concave in `p`.  Elementary: it is a product of the log-concave `coeffW` sequence and its
    reflection, so the interior log-concavity is `coeffW_logConcave` at `p−1` times the same at
    `(t−p)−1`, multiplied (nonneg factors).  This is the structural anchor for the whole frame — the
    fusion channel is a discrete-Gaussian × downward-parabola, and both factors are log-concave.

The remaining M1/M2 (via the Poisson/Jacobi modular dual + the Bernoulli log-gap `1−u ≤ −ln u`) and
Lemma C (the tilt-deficit convexity `e(t)=Var_par(t)−Var_q(t)` is convex) are the frame's next lemmas.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`,
no custom `axiom`.
-/

import YMGap.Continuum.FusionResidualBound

namespace YMGap.Continuum.R1LocalCLT

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep

/-- **`fusionMeasure_logConcave`** — the two-body fusion weight is log-concave (interior form, no `Nat`
subtraction): for all `a, b`,

    `(coeffW w a · coeffW w (a+2)) · (coeffW w b · coeffW w (b+2))
        ≤ (coeffW w (a+1) · coeffW w (a+1)) · (coeffW w (b+1) · coeffW w (b+1))`.

With `a = p−1`, `b = (t−p)−1` this is exactly `μ_t(p−1)·μ_t(p+1) ≤ μ_t(p)²` for `μ_t(p) =
coeffW w p · coeffW w (t−p)` — log-concavity of the fusion measure on the antidiagonal lattice.
Proof: `coeffW_logConcave` at `a` and at `b` (the log-concave `coeffW`), multiplied (nonneg factors).
Elementary and constructive — the structural anchor of the local-CLT frame. -/
theorem fusionMeasure_logConcave {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (a b : Nat) :
    (coeffW w a * coeffW w (a + 2)) * (coeffW w b * coeffW w (b + 2))
      ≤ (coeffW w (a + 1) * coeffW w (a + 1)) * (coeffW w (b + 1) * coeffW w (b + 1)) := by
  have ha : coeffW w a * coeffW w (a + 2) ≤ coeffW w (a + 1) * coeffW w (a + 1) :=
    FusionResidualBound.coeffW_logConcave hw0 hw1 a
  have hb : coeffW w b * coeffW w (b + 2) ≤ coeffW w (b + 1) * coeffW w (b + 1) :=
    FusionResidualBound.coeffW_logConcave hw0 hw1 b
  have hbnn : (0 : Q') ≤ coeffW w b * coeffW w (b + 2) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 b) (coeffW_nonneg hw0 (b + 2))
  have hann : (0 : Q') ≤ coeffW w (a + 1) * coeffW w (a + 1) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 (a + 1)) (coeffW_nonneg hw0 (a + 1))
  -- (aa)·(bb) ≤ (Aa²)·(bb) ≤ (Aa²)·(Ab²)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ ha hbnn)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hb hann)

/-! ## Doc-section — PROVED vs the frame's remaining lemmas (honesty)

PROVED (axiom-clean, constructive):
  * `fusionMeasure_logConcave` — the fusion measure is log-concave (the structural anchor).

FRAME (the local-CLT statements the anchor feeds, verified but not yet formalized here):
  * M1 `V_p^∞·(1−u) ≤ 2`, M2 `Var_p·(1−u)² ≤ 8` — via the Poisson/Jacobi modular dual (free constants
    `2, 8` = continuum-Gaussian leading terms) + the Bernoulli log-gap `1−u ≤ −ln u`
    (`R1CornerAtoms.oneSub_qpow_le`).  Template: `JTPIdentity`/`ThetaConv`.
  * Lemma C ⟺ `e(t) = Var_par(t) − Var_q(t)` convex in `t` — the log-concave tilt deficit; the one
    residual whose structural (TP₂/Turán) closure is under active derivation.
-/

end YMGap.Continuum.R1LocalCLT

/-! ## Axiom-dependency gate (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.R1LocalCLT.fusionMeasure_logConcave
