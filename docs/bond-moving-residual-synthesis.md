# The bond-moving residual: what it is, what's proved, what's open (2026-06-20)

Synthesis of four parallel investigations (Lean structure map; numerical simulation;
category-theoretic framing; deep literature research) into the single object that now
governs the full-mode continuum gap: the per-step Migdal–Kadanoff **bond-moving residual**
on the SU(2) heat kernel, and whether it sums along the asymptotic-freedom trajectory.

## The question

The full-mode RG gap chain needs a per-step defect `δ_k` with `∑_k δ_k < ∞`, so the running
product `∏_k (1 − δ_k)` has a strictly positive floor (= the mass gap survives `a→0`). `δ_k`
is the deviation of one block-spin RG step from the exact heat-kernel flow. Decimation
(bonds in series) is EXACT on the heat kernel (semigroup: `f_τ → f_{bτ}`). Bond-moving
(bonds in parallel) replaces `f` by `f^n` (`n = b^{d−1}`, pointwise power = `n`-fold SU(2)
Clebsch–Gordan fusion convolution of the character coefficients); `f^n` is NOT a heat
kernel in `d>2`, and that deviation is the residual.

## The obstruction that prompted this — and its resolution

The chain currently measures the defect with the **Casimir-square envelope**
`casimirSqSum = ∑_s μ_τ(s)·qfac^q·C₄(s)²` (no division by the heat-kernel coefficient).
The renormalized defect `(1−w)²·casimirSqSum = ∑_s μ_τ(s)(1+y_s)^q y_s²` (`y_s = τ·C₄(s)`)
is a **bounded Gaussian moment that converges to a positive CONSTANT** as `τ→0`, not to 0 —
so summed along the trajectory it DIVERGES and the product floor collapses to 0. This is
real and was independently confirmed two ways:
- numerically: the envelope moment → ≈16.9 (this normalization) as `τ→0`;
- analytically (literature): under `μ_τ(j) ∝ (2j+1)²e^{−τj(j+1)}`, exactly
  `⟨τ·C₂⟩ → 3/2` and `∑μ_τ(τ·C₂)² → 15/4` — finite, nonzero Gaussian constants.

**The resolution: the envelope is not the residual.** The genuine residual is the deviation
of `f^n` from the *nearest genuine heat kernel* after the `s=1`-matched retune (the project's
`renormW`), measured RELATIVELY (divided by the heat-kernel coefficient `Kτ(s)=(s+1)w^{C₄(s)}`)
in the heat-kernel-weighted norm `scaledNorm(r) = ∑_s μ_τ(s)·qfac^q·|r_s/Kτ(s)|`. That norm
already exists in the formalization; it is simply not yet wired to the genuine residual.

## What the numerics show (committed: `visualizations/pilot/su2/bondmove-residual-n8`)

Building the actual SU(2) coefficients → `n`-fold fusion → `s=1`-retuned relative residual,
and sweeping `τ→0`:

| object | scaling as `τ→0` | summable along `τ_k≍1/k`? |
|---|---|---|
| `C₄²` envelope moment | `τ^{−0.01}` → **const ≈ 16.9** | **no** (∑ diverges, floor → 0) |
| genuine `∑μ·qfac^q·\|r_s/Kτ\|`, `s=1` retune | **`τ^{+2.00}`, M ≈ 10.5 (flat to 4 digits)** | **yes** |
| same residual, NO retune | → const | no |

Along an AF trajectory `τ_k = τ₀/(k+1)`: the genuine residual gives `∑δ_k ≈ 1.56` (finite)
→ **product floor ≈ 0.028 > 0**; the envelope diverges → floor 0. The retune is essential:
it is the 2-parameter subtraction (match the vacuum `s=0` AND the `s=1` slope) that removes
the residual through first order in the Casimir, leaving second order = `τ²`.

## Why `τ²` — the mechanism, and the proved/conjectured boundary

PROVED (standard heat-kernel asymptotics; re-derived):
- The exact S³=SU(2) kernel is `K_t(φ) = (4πt)^{−3/2}e^{t}(φ/sinφ)e^{−φ²/4t} + (image terms)`.
- On a CLOSED manifold the Minakshisundaram expansion has only INTEGER powers of `t`
  (`a₁ = R/6`, no `τ^{1/2}` term). So the leading non-Gaussian correction of the SINGLE
  kernel is RELATIVE order `τ¹` (β=1) — the **marginal** term.
- `τ_k = Θ(1/k)` along the 2-loop AF trajectory (`a_k = 2^{−k}a₀`), with a `−(ln k)/k²`
  two-loop correction. `β₀ = 11N/(48π²)`, `β₁ = (34/3)(N/16π²)²`.
- The p-series boundary: `δ_k ≍ τ_k^{2−α} ≍ k^{−(2−α)}` sums iff `α < 1` (harmonic at `α=1`).

CONJECTURE / research-novel (NOT a theorem — this IS the open crossover in miniature):
- The `e^{(R/6)τ}` curvature-shift scalar is a pure normalization (reabsorbable). The
  `s=1` retune subtracts the scalar AND the linear-in-Casimir term, so the genuine residual
  is second order. Numerically `τ²`; heuristically `O(τ^{1+ε})` suffices (`α<1`).
- The near-cancellation in the Clebsch–Gordan fusion convolution that makes the genuine
  residual BEAT its non-vanishing Casimir-square envelope is **unsourced**. No paper bounds
  the single-step heat-kernel bond-moving residual as a function of `τ`, nor proves its
  summability along the `d=4` AF trajectory. This is exactly the weak↔strong crossover.

So: the marginal `O(τ)` is proved; the quadratic `O(τ²)` after the `s=1` retune is
numerically confirmed and heuristically grounded but is a CONJECTURE, the realistic
constructive target being a SINGLE-step bound, not the full crossover.

## Category-theoretic frame

The heat-kernel family `{f_τ}` is the integral curve of the EXACT RG: decimation `D` is a
strict semigroup endomorphism preserving the line (`f_τ ↦ f_{bτ}`). Bond-moving `B: f ↦ f^n`
maps OFF the line; the residual `r` is precisely the **obstruction to `B` preserving the
heat-kernel subobject** — the second fundamental form (extrinsic curvature) of the line
embedded in theory-space. The `s=1` retune `ρ` is the retraction onto the line; it kills the
tangent (first-order) deviation, leaving the curvature = second order = `τ²`. The product
floor `∏(1−δ_k)` is holonomy/transport along the trajectory (the home of the existing
codynamic transfer category); `∑δ_k < ∞` is the statement that this curvature is INTEGRABLE,
so transport to the continuum endpoint does not degenerate. The simulation's `τ²` is that
extrinsic curvature; the `s=1` reabsorption of the linear term is the proved marginal→
quadratic separation, now exhibited for ALL modes.

## The realistic Lean target (sharply located)

The chain needs no surgery: `FullModeDefect` accepts ANY `d k` with
`d_quad : d k ≤ M·(1−w_k)²`, M w-independent, and everything downstream (inverse-square →
summable → exponential product floor → gap) is proved and agnostic to how `d` is built.
The single new obligation is

> `genuine_residual_quadratic : scaledNorm(w_k, rrel_k) ≤ M·(1−w_k)²`, M w-independent,
> where `rrel_s = (genuine s=1-retuned fusion residual)_s / Kτ(s)`.

which factors as
- (i) a PER-MODE bound `|rrel_s| ≤ (1−w)²·P(y_s)`, P a fixed polynomial in `y_s = τ·C₄(s)`
  — the genuinely new fusion-residual analysis (the conjectural near-cancellation); then
- (ii) `∑_s μ_τ(s)·qfac^q·P(y_s) ≤ const` — a bounded Gaussian moment, which the EXISTING
  tools deliver: Pillar 1 (`Zsum ≥ c·τ^{−3/2}`), Pillar 2 (`∑μ ≤ 1`), and `geom_beats_pow`.

So the moving-cutoff work already built is the summation engine for the RIGHT integrand;
the open piece is (i). NOTE: the existing `modeDefect` is the decimation-LINEARIZATION
overshoot, and `modeDefect/Kτ` GROWS like `e^{y}` — it is the wrong per-mode object, and the
`modeDefect → C₄²-envelope` route is what manufactured the obstruction. (i) must bound the
genuine FUSION residual, not `modeDefect`.

Tools the literature supplies for (i):
- sharp two-sided S³ heat-kernel bounds (Nowak–Sjögren–Szarek, J. Math. Pures Appl. 2019;
  Math. Ann. 2022);
- Amos-type two-sided modified-Bessel-ratio bounds (the SU(2) Wilson coefficients are
  `c_j = I_{2j+1}(β)/I_1(β)`);
- log-concavity / Pólya-frequency of the heat-kernel coefficients: `log c_j = log(2j+1) −
  τj(j+1)` has second difference `−2τ < 0`, so `{c_j}` is strictly log-concave (constrains
  the fusion convolution). Caveat: total positivity of order ≥5 can fail; do not assume
  all-order TP.

Best tractable rigorous statement to aim for: a `τ`-explicit upper bound on the actual
SINGLE-step relative residual in the weighted norm that is `o(1)` (ideally `O(τ^{1+ε})`),
via (a) subtract the reabsorbable `e^{(R/6)τ}` scalar, (b) use the sharp kernel/Bessel/
log-concavity bounds to control the fusion convolution and exhibit the near-cancellation.
That single lemma — not a full crossover proof — converts the `β=1` heuristic into a one-step
theorem; then `τ_k = Θ(1/k)` + the p-series give the product floor.

## Honest status

The continuum 4D non-abelian YM mass gap is OPEN. The only rigorous gap results are
lattice + strong coupling (Osterwalder–Seiler 1978; Shen–Zhu–Zhu CMP 2022, SPDE/LSI),
spacing-FIXED; Balaban gives UV stability but no continuum gap; the weak↔strong crossover
is the wall. This work does NOT close it. What it DOES: (i) it correctly diagnoses the
full-mode obstruction as an artifact of the Casimir-square envelope, not the physics;
(ii) it confirms numerically that the genuine `s=1`-retuned bond-moving residual scales as
`τ²` (α=0, comfortably summable) with a `w`-independent constant; (iii) it locates the
single open lemma — a one-step relative-residual bound exhibiting the fusion near-cancellation
— and identifies the sharp-kernel tools to attempt it; (iv) it confirms the existing chain
and the moving-cutoff summation machinery are built to receive that bound. The `τ²` rate is
a numerically-supported, heuristically-grounded CONJECTURE — the crossover problem in
miniature — not a theorem.

## Source flags

WITHDRAWN: arXiv:2506.00284 (Jacobsen SU(3), withdrawn 2025-06-13). Conditional/assumes-the-
gap: arXiv:2406.16881 (Farinelli). Citation correction: the "plaquette within 10% / g₀²(a)
worse" empirical MK accuracy is Caracciolo–Menotti NPB B180 (1981), not Nauenberg–Toussaint
B190. Do not cite arXiv:0802.3320 for the bi-invariant kernel (it is the subelliptic kernel;
use Camporesi Phys. Rep. 196 (1990)). Refereed sources: Osterwalder–Seiler Ann. Phys. 110
(1978); Kadanoff Ann. Phys. 100 (1976); Caracciolo–Menotti NPB B180 (1981); Nauenberg–
Toussaint NPB B190 (1981); Menotti–Onofri NPB B190 (1981); Ito PRL 55 (1985); Magnen–
Rivasseau–Sénéor CMP 155 (1993); Shen–Zhu–Zhu CMP (2022, arXiv:2204.12737); Vassilevich
Phys. Rep. 388 (2003); Nowak–Sjögren–Szarek (J. Math. Pures Appl. 2019, Math. Ann. 2022);
Chatterjee arXiv:1803.01950.
