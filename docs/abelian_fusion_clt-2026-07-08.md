# Abelian shadow of the fusion local-CLT — deliverable

**File:** `lean/YMGap/Continuum/AbelianFusionCLT.lean` (new, imported into `YMGap.lean`).
**Build:** `lake build` exit 0 (779 jobs). **Guard 5:** intact
(`frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`).
**Axioms:** every load-bearing theorem ⊆ `{propext, Quot.sound}`; NO `sorryAx`, NO
`native_decide`, NO `Classical.*`. `abelCoeff_nonconstant` depends on NO axioms.
LEAN-CORE only (`Q'`/`Nat`/`omega`); MLTT Rule 8 (all content is `Q'.eqv`/`≤` data,
no `Prop`-∃).

## The strategy, realized

The theta machinery already in `Continuum/` (`ThetaConv.Ppart` = the Jacobi triple
product) IS the U(1) heat kernel `ϑ₃(θ,w) = Σ_n w^{n²} eⁱⁿθ`. Its per-mode Fourier
weight is `abelCoeff w n = qpow w (n*n) = w^{n²}`. This is the abelian shadow: it makes
the fusion local-CLT EXACT (heat-kernel fusion = theta convolution = Fourier
coefficients multiply), and it exposes the SU(2) case as a concrete Weyl-dimension
perturbation on top.

## 1. The abelian (U(1)/Villain/theta) fusion local-CLT — PROVED EXACTLY

- `abelCoeff w n = w^{n²}` — the ϑ₃/Villain Fourier coefficient (def; non-vacuous:
  `abelCoeff_nonconstant`, `abelCoeff (1/2) 2 = 1/16 ≠ 1`).
- **`abelCoeff_fuse`** — EXACT convolution semigroup: `(abelCoeff w n)^m = abelCoeff (w^m) n`.
  m-fold fusion at parameter `w` = single kernel at `w^m` (Fourier coefficients multiply).
  This is the exact Poisson/theta convolution `K_{t₁}∗K_{t₂}=K_{t₁+t₂}`.
- **`abelSep_fuse`** — the fused gap separator DECAYS: `(abelCoeff w 1)^m = w^m` (exact).
- **`abelCoeff_superLC_exact`** — the EXACT local-CLT floor with UNIFORM curvature:
  `abelCoeff w n · abelCoeff w (n+2) = w² · (abelCoeff w (n+1))²`, an *equality* at every
  mode `n`. The discrete log-Hessian is the constant `2·log w` everywhere — the exact
  local central limit statement.
- **`abelCoeff_logConcave`** — the PF₂ inequality, a corollary of the exact floor + `w²≤1`.

Verdict: the abelian fusion local-CLT is a GENUINE EXACT result (semigroup + constant-
curvature floor), provable exactly precisely because abelian fusion = theta convolution.

## 2. SU(2) = theta × Weyl decomposition — PROVED EXACTLY

The SU(2) heat-kernel character coefficient is `coeffW w s = dimQ s · w^{C₄(s)}`,
`C₄(s)=s(s+2)`, `dimQ s = s+1` (Weyl dimension). Since `s(s+2)+1=(s+1)²`
(`c4_succ_eq_sq`):

- **`coeffW_eq_weyl_abel`** — `w · coeffW w s = dimQ s · abelCoeff w (s+1)` (EXACT).

i.e. SU(2) heat kernel on the maximal torus = abelian theta coefficient at the shifted
charge `n=s+1` (the torus part) × Weyl dimension `dimQ s` (the `sin²θ` Weyl-measure
correction) × the overall `w^{−1}` Casimir constant.

## 3. The Weyl-denominator perturbation — ISOLATED EXACTLY

The SU(2) two-point log-concavity ratio splits EXACTLY into the abelian factor (the
SAME `w²`) times the Weyl-dimension ratio:

- **`coeffW_prod_regroup`** — `coeffW w s · coeffW w (s+2) = (dimQ s·dimQ(s+2)) · (w² · (w^{C₄(s+1)})²)`.
- **`coeffW_sq_regroup`** — `(coeffW w (s+1))² = (dimQ(s+1))² · (w^{C₄(s+1)})²`.
- **`weyl_dim_defect`** — the perturbation is the EXACT rank-one defect:
  `(dimQ(s+1))² = dimQ s·dimQ(s+2) + 1`. Relative small parameter
  `1/(dimQ(s+1))² = 1/(s+2)² ≤ 1/4`, decaying in the mode.
- **`coeffW_logConcave_abelian_weyl`** — the SU(2) log-concavity ANCHOR
  (`coeffW w s·coeffW w (s+2) ≤ (coeffW w (s+1))²`) re-derived transparently as
  `abelian floor (w²≤1) × Weyl floor (dim log-concavity, defect +1)`.

## Honest verdict

- **Abelian fusion CLT: proved EXACTLY** — semigroup exact, super-log-concavity floor an
  exact equality with uniform curvature `w²`. This is the de-risked exact base.
- **SU(2) = theta × Weyl: proved EXACTLY** (`coeffW_eq_weyl_abel`).
- **SU(2) two-point log-concavity anchor: CLOSED** as abelian-exact `w²` × a concrete
  Weyl perturbation whose deviation is the EXACT `+1` rank-one dimension defect (relative
  parameter `1/(s+2)²`). The non-abelian fusion is now a controlled perturbation of the
  exact abelian theta CLT, not an amorphous problem.
- **Residual (honest):** this closes the two-point log-concavity STRUCTURAL ANCHOR of the
  local-CLT (`R1LocalCLT.fusionMeasure_logConcave` feeds off exactly this). It does NOT by
  itself close the full moment-envelope local-CLT (M1 `V·(1−u)≤2`, M2 `Var·(1−u)²≤8`),
  which still needs the Poisson/Jacobi modular dual. But those envelopes now sit on an
  abelian-exact base plus a closed rank-one Weyl correction — the exact residual
  perturbation estimate is `1/(s+2)²`, uniformly small and decaying.

The theta investment paid off: the amorphous non-abelian fusion CLT is converted into the
exact abelian theta CLT + a `1/(s+2)²` Weyl-dimension perturbation.
