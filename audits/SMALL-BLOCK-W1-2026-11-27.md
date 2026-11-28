# Small-block W₁ certificate for SLICE-AMP at u = 1/8 (YB-14, 2026-11-27)

**Scripts:** box-only, `/workspace/novel_paths/yb14/` (`small_block_w1.py`, `two_link_w1.py`); not committed (docs-only).

**Label: paper analysis + box numerics. No Lean in this commit. NOT gap evidence.**
Base: origin/main **a465c001** (SLICE-AMP design note plus `DobrushinNeumann.lean`). Continues
`audits/SLICE-AMP-DESIGN-2026-11-27.md`. The target is still SLICE-AMP(1/2): a uniform
product-geodesic W₁ Lipschitz constant κ_* ≤ **216/793** ≈ 0.272383 for a one-link
kinetic-boundary change of the 3D slice at w = 1/2, u = w³ = 1/8.

Nothing here discharges `hfine_T2_half_OPEN`. SLICE-AMP itself is not refuted (the
slice-MC lower bounds of the design note, max tot2s = 0.148, still sit under the budget).
What fails is the *small-block Dobrushin row-sum / `cpow_resolvent` certificate*.

**U(1):** the obstruction is U(1)-true at matched activity (see §6). Not non-abelian evidence.
The S³ H⁻¹ constants 5/6 and 1/8 are geometry-specific (U(1)-false as numbers); the
contraction failure 12κ > 1 is not.

## 0. Verdict (honest)

| Claim | Status | Margin |
|---|---|---|
| 1-link κ, aligned environment, lower bound | **On paper** (1D class-function integral; box quadrature) | κ ≥ \|v\| = 0.0900 (geodesic W₁ ≥ this; a previous geodesic dual gave ≥ 0.093) |
| 1-link κ, aligned, H⁻¹ upper bound | **Numerically supported** (same 1D reduction; Haar quadrature 40×24×48, exact cell masses) | κ ≤ 0.1233 |
| 1-link κ, uniform over staple environments, upper bound | **Numerically supported, not proved** | H⁻¹ ≤ 0.1643 on 800 Haar random 6-tuples, ≤ 0.1610 on 400 random tangents, ≤ 0.1550 on a structured family; \|v\| ≤ 0.1344. A conservative numerical envelope is **0.17**. No Lipschitz-net certificate. |
| 1-site Dobrushin contraction at u = 1/8 | **Fails, on paper** | 12κ ≥ 12 × 0.0900 = **1.080 > 1**. To meet 216/793 via κ/(1−12κ) one needs κ ≤ 216/3385 ≈ 0.06381; the aligned lower bound already overshoots that by 0.0900/0.06381 ≈ **1.41×**. |
| 2-link *parallel-chain* tiling (T1) row sum | **Fails, on paper** | The two links of a T1 block are *not* plaquette-adjacent, so they are conditionally independent given the boundary. The block graph has **16** neighbours and C_{B,B'} = κ_1, hence row sum = 16κ ≥ **1.440 > 1**. Worse than 1-site. |
| 2-link *plaquette-corner* (perp) block | **Numerically supported failure** of any “internal mixing saves us” hope | An external staple of U gives product-geodesic lower bound \|dEU\|+\|dEV\| = 0.1011 (aligned) up to 0.1479 (random); \|dEV\|/\|dEU\| ≈ 0.10. U-marginal H⁻¹ is 0.123–0.167, the same size as 1-link. The pair does not contract influence enough to drop C below ~κ_1. No complete tiling of the 3D link lattice by perp pairs alone. |
| Plaquette 4-block | **Fails as a row-sum strategy** | 28 external spatial links; no cheaper degree than 1-site was found. |
| SLICE-AMP(1/2) ≤ 216/793 | **Still OPEN** | Small-block Dobrushin cannot prove it. Typical-case slice MC is not a no-go. |

The rest of the note gives the bounds, the tiling count, what would go into Lean, and the U(1) test.

## 1. Setup and methods

The 1-link conditional at six staples S_1,…,S_6 is

> dP(U) ∝ [ Π_{i=1}^6 f_w(⟨U,S_i⟩) ] dHaar(U),    f_w(c) = Σ_{s≥0} (s+1) w^{s(s+2)} χ_s(c),

with χ_s = U_s the Chebyshev of the second kind, χ_1 = 2c, so the s = 1 term is 1 + 4u c.
A unit tangent move of staple 1 has score ψ(U) = φ'(⟨U,S_1⟩) ⟨U, dS_1⟩, φ = log f_w.
The product-geodesic W₁ Lipschitz constant of this conditional is the 1-link κ (uniformly in the
environment, for the Dobrushin matrix).

Three candidate methods were tried.

### 1.1 Explicit coupling (reflection / synchronous on S³)

For a von Mises–Fisher approximation P ∝ exp(⟨A,U⟩) dHaar, a radial change of λ = |A| is
stochastically monotone in the colatitude ψ, and W₁ equals |Δ E[ψ]| under the optimal
1D coupling. That part is tight and constructive.

A synchronous rotation of the axis n, with cost ω(λ) d(n,n') where ω(λ) = E √(U_0²+U_1²), is
*not* tight at small λ: ω(0) ≈ 0.667, so ω(λ)/λ diverges as λ → 0, while the two measures both
approach Haar and the true W₁ is O(|ΔA|). The coupling cost does not vanish. This bound cannot
be used uniformly on the staple ball (which includes A = 0). It was discarded as a uniform
certificate.

### 1.2 Lipschitz of the density plus Kantorovich–Rubinstein, via H⁻¹

The step-1 Beckmann / H⁻¹(Haar) bound on unit S³ (`steps01_uniform.md` §9) remains valid at
any w:

> κ² ≤ sup_P  [ (5/6) |v|² + (1/8) E_Haar[h²] ],    v_e = Cov_P(ψ, U_e),    h = (ψ − E_P ψ) · dP/dHaar.

This is a *constructive upper bound* for geodesic W₁, for each environment, once the two moments
are computed. At Haar (linear response) it recovers the step-1 scale 1.155 u: here 1.155 × 1/8 =
0.1444, and a direct vMF evaluation at λ = 0, |ξ| = 1, times 4u, gives 0.2889 × 0.5 = 0.1445.

### 1.3 1D class-function reduction

When all six staples are aligned, P is a class function of U relative to a fixed axis, the score
and the H⁻¹ moments reduce to integrals on ψ ∈ [0,π] with weight sin²ψ, and the lower bound
|v| = |d E[U]/dθ| is a 1D quadrature. This is the source of the on-paper 1-link lower bound.

### 1.4 Staple-sum / vMF reduction (for a uniform net)

log f_w is not linear at w = 1/2. A minimax fit on [−1,1], 4001 nodes:

| model | a | ε = ‖φ − (at+b+…)‖_∞ | η = 6ε | e^{4η} |
|---|---|---|---|---|
| linear (vMF) | 0.52753 | 0.04413 | 0.2648 | 2.884 |
| quadratic | 0.52153, c₂ ≈ −0.09 | 0.00647 | 0.0388 | 1.168 |
| cubic | — | 0.00136 | 0.00817 | 1.033 |

(The linear ε at w = 7/20 is 0.00610, matching the step-1 note’s 6.11×10⁻³; the same fit is
much worse at w = 1/2.) Also max |φ'| = 0.76436 at c = −1, φ'(1) = 0.38824, f(1) ≈ 1.53565,
f(−1) ≈ 0.53467. The linear remainder η = 0.265 makes a crude e^{±2η} inflation of H⁻¹ too
loose to be interesting (≈ 0.15 × e^{2η} ≈ 0.26). A quadratic or cubic sufficient statistic
restores a step-1-sized remainder, at the cost of a higher-dimensional net (§5).

The product Π f(⟨U,S_i⟩) is a function of a single SU(2) sum *only* after an exponential
(vMF) approximation. The exact 6-staple law, even after gauge-fixing S_1 = 1, is 15-dimensional
and is not a certificate net.

## 2. 1-link numbers at u = 1/8

Haar grid: N_ψ × N_θ × N_φ = 40 × 24 × 48 = 46 080 cells, exact integrals of sin²ψ and sinθ
as cell masses (same family as the design note). H⁻¹ and |v| for a staple-1 tangent:

| environment | \|v\| (W₁ lower) | H⁻¹ (W₁ upper) |
|---|---|---|
| all six staples aligned, any common angle | 0.0900 | 0.1233 |
| four spatial = 1, kinetic at angle π | 0.1227 | 0.1436 |
| 2+2 cancelled spatial, kinetic = 1 | 0.1227 | 0.1436 |
| structured family (34 configs) | ≤ 0.1337 | 0.1233–0.1550 |
| 800 random Haar 6-tuples | mean \|v\| 0.1166, max 0.1331 | mean 0.1407, p90 0.1504, p99 0.1564, **max 0.1643** |
| 400 random 6-tuples × random tangent | max 0.1344 | max 0.1610 |

The H⁻¹ bound is reasonably tight: aligned 0.1233 versus lower 0.090–0.093 (about 35% slack);
on random environments the gap between max |v| = 0.134 and max H⁻¹ = 0.164 is about 22%.
The worst-case 1-link κ therefore lives in roughly **[0.148, 0.17]** if one includes the
design-note geodesic dual lower bound 0.148 on random 6-tuples, or in **[0.134, 0.17]** from
this round’s |v| and H⁻¹ alone. Either way 12κ > 1.

These are not interval-certified: they are floating-point quadratures. The aligned lower bound
is a 1D integral of a real-analytic integrand and can be pushed to a rational certificate
(§5); the uniform upper bound needs a net (§5) and was not produced.

## 3. Block-to-block row sums

Dobrushin on a partition of the 3D link lattice: C_{B,B'} is the product-geodesic W₁ Lip of
the conditional of block B when the configuration of a neighbouring block B' moves, and the
row-sum bound α = max_B Σ_{B'} C_{B,B'} must be < 1 for `cpow_resolvent` to give a finite
ℓ¹ lift. For SLICE-AMP one also needs (source)/(1−α) ≤ 216/793. The source is the influence
of a single kinetic staple on the unique block that contains that spatial link, so
‖b‖_1 ≤ C_{B,kin} ≤ O(κ). Meeting the budget with a barely-contracting α (say α = 0.9)
would already require a source ≲ 0.027, far below the 1-link scale 0.09. In fact one never
reaches a finite resolvent: α itself exceeds 1.

### 3.1 One site (review)

Degree 12 in the spatial plaquette graph. Row sum = 12κ ≥ 1.080 > 1, from the aligned lower
bound alone. The Neumann series for a kinetic source of size κ would be κ/(1−12κ), which is
not defined as a positive bound. This already closed the 1-site route in the design note;
the new H⁻¹ upper bound only makes the same no-go quantitative (12 × 0.1233 = 1.48 on the
aligned environment, 12 × 0.17 ≈ 2.04 as a numerical envelope of the uniform row sum).

### 3.2 T1: parallel-chain 2-link tiling

Pair consecutive parallel links along each direction (the link (x,y,z,μ) with x_μ even is
paired with its translate by +e_μ). This is a perfect matching of all links of ℤ³ (or of any
even torus).

The two partners **do not share a plaquette**. They have 20 external spatial neighbours, of
which 4 are common, and these fall into **16 neighbouring T1-blocks**: 12 that touch the
block in one link and 4 that touch it in two. Given the boundary, the two links of the block
are conditionally independent, so

> W₁(B) = W₁(U) + W₁(V),    C_{B,B'} = κ_1

for every neighbouring B' (if B' touches both partners, W₁(B) ≤ κ d_1 + κ d_2, hence
C ≤ κ as a Lip constant in the product metric of B' as well; the sup is still κ). Therefore

> row sum = 16 κ_1 ≥ 16 × 0.0900 = **1.440 > 1**.

This is a paper no-go, and it is *worse* than 1-site (degree 16 versus 12). A 2-link block
that does not contain its strongest partners only lengthens the block graph.

### 3.3 Perp / gauge-fixed-plaquette 2-link

The coupled pair is a plaquette corner: U along x and V along y at the same vertex, with the
shared xy-plaquette (the other two edges frozen in the environment). This *does* mix. Nested
Haar quadrature (12 × 8 × 16 = 1536 nodes per factor, 2.36×10⁶ pairs) at w = 1/2:

| environment, score = external staple of U | \|dEU\| | \|dEV\| | lower \|dEU\|+\|dEV\| | U-marginal H⁻¹ |
|---|---|---|---|---|
| all staples and W aligned | 0.0920 | 0.0091 | 0.1011 | 0.1232 |
| anti U-staple, rest 1 | 0.1293 | 0.0128 | 0.1421 | 0.1666 |
| 12 random environments, max | 0.1322 | 0.0157 | 0.1479 | 0.1570 |

The second link moves at about **10%** of the first. The product-geodesic lower bound is only
about 1.10× the 1-link lower bound; the U-marginal H⁻¹ stays in the same 0.12–0.17 band as
the 1-link H⁻¹. A clean analytic envelope of the form W₁(joint) ≤ κ_1 (1+κ_1) is available
when the score depends only on U (Lip of E[f|U] is ≤ 1+κ_{V←U}, and the U-marginal is a
1-link law with one extra integrated-neighbour potential): at κ_1 ≈ 0.16 this is ≈ 0.19,
only a modest worsening, not a reduction.

This pair cannot be used as a complete tiling by itself (z-links and a colouring obstruction
remain). Even as a Dobrushin–Shlosman cluster it has 18 external spatial neighbours, and C
stays Θ(κ_1). It does not open a row-sum < 1.

A 4-link plaquette cluster has 28 external spatial links. Unless a tiling with unusually
small block-degree exists — none was found — this is the wrong direction: more surface, not
less.

### 3.4 What the row-sum comparison with 216/793 means

The budget 216/793 is a bound on the *global* slice Lipschitz constant κ_*, not on the
internal row sum α. The small-block certificate would give κ_* ≤ ‖b‖_1 / (1−α). With
α ≥ 1 the crude resolvent bound is infinite, so there is nothing to compare with 216/793
except the observation that one is not even in the regime where the comparison is defined.
The failure margin on the *contraction hypothesis* is

- 1-site: 12κ ≥ 1.080, i.e. **at least 8% above 1**, and ≈ 1.7–2.0 with the numerical
  uniform κ;
- T1 2-link: 16κ ≥ 1.440, i.e. **at least 44% above 1**, and ≈ 2.4–2.7 with the numerical
  uniform κ.

Relative to the κ that would have been needed for 1-site to meet the budget (0.06381), the
aligned lower bound is 41% too large, and the numerical uniform κ is about 2.4× too large.

## 4. What this does *not* say

- It does **not** refute SLICE-AMP(1/2). A crude Dobrushin row sum is a sufficient condition,
  not a necessary one. The high-stat slice MC of the design note (L=2,3) still shows a
  2σ-thresholded total ≈ 0.15 < 216/793 on typical and structured kinetic boundaries, with
  no visible in-slice amplification. That remains a typical-case lower-bound probe, not a
  proof, and not a no-go.
- It does **not** produce a uniform, machine-checked 1-link upper bound. The H⁻¹ numbers of
  §2 are a numerical envelope on a large sample, tight enough to be useful as a *target* for
  a later GRID-SUP certificate, and not needed to kill the row-sum argument (the lower bound
  already does that).
- Large-block Dobrushin–Shlosman is a different method. It would need an input comparable to
  a mass gap inside the block, which is circular for a step-2 certificate. Self-avoiding-walk
  / cluster / polymer expansions can in principle converge when 12κ > 1; they are not analysed
  here.

## 5. What would go into Lean (rationals + GRID-SUP)

Recommended split: a small formal no-go for the row-sum certificate, and an optional uniform
1-link upper bound that does not close SLICE-AMP.

### 5.1 Paper no-go, Lean-sized (should be done if anything is)

1. The aligned 1-link lower bound κ ≥ 9/100, or a slightly weaker rational such as 2/25 = 0.08.
   The integrand is a rational function of W = 1/2, Chebyshev polynomials, and sin²ψ. A 1D
   GRID-SUP on ψ ∈ [0,π] with exact cell masses, a few thousand cells, and outward-rounded
   rationals or a fixed-point interval type (as in the existing step-1 `cert_kappa.py` style)
   is enough. Net size: **O(10³)–O(10⁴)**, 1-dimensional.
2. The elementary inequalities 12 × (that rational) > 1 and 16 × (that rational) > 1.
3. The T1 degree count (16 neighbouring blocks, conditional independence of the two partners).
   This is finite combinatorics on the ℤ³ link lattice, no analysis.

That package shows, with axioms only {propext, Quot.sound} and no `sorry`, that 1-site and
T1 2-link Dobrushin row sums at u = 1/8 are > 1. It does not touch Föllmer, EvenDecay, or
the gap.

### 5.2 Optional uniform 1-link H⁻¹ upper bound

Reuse the H⁻¹ inequality (5/6, 1/8) already used at w = 7/20, with rational arithmetic.

- *Linear / vMF path.* Domain |A| ≤ 6a with a = 0.52753, so |A| ≤ 3.17. After rotation the
  environment is (λ, θ) with λ ∈ [0, 3.17] and θ the angle between A and the staple tangent
  ξ, or a 3-parameter cube (A_∥, A_d, A_⊥). A 2-parameter net with Δλ = 0.02, Δθ = 0.05 has
  about **10⁴** points; a 3-parameter cube net with h = 0.1 and octant symmetry has about
  **1.5×10⁴** cubes, and with h = 0.05 about **5×10⁵**. Feasible as an external grid plus a
  Lean checker, or as a compiled data file; heavy if every cube is unfolded in the kernel.
  The obstacle is the remainder η = 0.265, which inflates T by a factor of order e^{2η}–e^{4η}
  ∈ [1.70, 2.88] unless the score remainder φ' − a and the density tilt are tracked more
  carefully than a crude e^{±2η}. Even a tight version would only certify κ ≲ 0.20–0.26, which
  still has 12κ > 1.
- *Quadratic / cubic path.* ε drops to 0.00647 or 0.00136 (η = 0.039 or 0.008), comparable to
  step 1, but the sufficient statistic is no longer a single A ∈ ℝ⁴. A 5–6 dimensional net
  at 15–20 points per axis is **10⁶–10⁷** cubes: a computer certificate, not a hand net.
- *Exact 6-staple path.* After gauge-fixing S_1 = 1 one still has 15 dimensions. A raw
  GRID-SUP is a no-go (the same counting that killed a raw 3D-box net in the design note).

None of these nets is worth a Prover push *as a SLICE-AMP closer*. They would only supply a
uniform 1-link κ_ub for other estimates.

## 6. U(1) verdicts

| Item | U(1) test |
|---|---|
| SLICE-AMP statement, small-block Dobrushin, T1 degree 16, 1-site degree 12 | **U(1)-true.** The same certificate shape exists for compact U(1) at the matched heat kernel, and the same degree-versus-κ obstruction is visible there. This no-go is not non-abelian evidence. |
| S³ H⁻¹ constants 5/6 and 1/8, vMF reduction on ℝ⁴, max \|φ'\| numbers | **U(1)-false as constants** (they use S³ and SU(2) characters). The method (Beckmann / staple reduction / GRID-SUP) is U(1)-analogous with different Green-function constants and with S¹ in place of S³. |
| Slice-MC typical totals under the budget | **U(1)-true** as a phenomenon: an abelian slice can also have typical influence below the worst-case Dobrushin sum. Not evidence of a non-abelian gap. |
| SO3-BE / Z2-VORTEX (from the design note, unchanged) | SO3-BE is U(1)-false (adjoint); Z2-VORTEX is U(1)-analogous. Still the only non-abelian complement on the queue, and not advanced in this note. |

A compact-U(1) 1-link κ at u = 1/8 was not recomputed in this round. The verdict above does
not depend on that number: already the *existence* of a 1-link lower bound of order 10⁻¹,
which the aligned SU(2) integral supplies and which a U(1) theta-kernel calculation would
be expected to match in order, makes 12κ > 1 an abelian-visible obstruction.

## 7. Resources (this round)

- Box limits honoured: `prlimit --as=1073741824`, `OMP_NUM_THREADS=1`, `python3 -P`, one
  heavy job at a time. No Lean against the full repo closure. No push, no Mac.
- `small_block_w1.py`: ~23 s wall, 1-link H⁻¹ on the 46 080-point grid plus the vMF coupling
  diagnostic (the latter discarded as a uniform bound, §1.1). RSS well under 1 GiB.
- `two_link_w1.py`: 55.8 s total (30.9 s denser 1-link scan, 10.5 s 2-link quadrature, the
  rest overhead). Peak RSS modest (grids 46 080 and 1536, 2-link chunks of 256).
- No stray heavy processes were left running.

## 8. Queue implication

1. Do **not** spend Prover time on a small-block (1-link, T1 2-link, or plaquette) Dobrushin
   row-sum certificate for SLICE-AMP at u = 1/8: it is already ruled out on paper.
2. Optional, small, and useful: Lean of §5.1 (aligned 1-link lower bound + degree counts).
3. SLICE-AMP(1/2) remains a live *statement*, supported typically by the design-note MC,
   but it needs a method that can survive 12κ > 1 (cluster / polymer / SAW, a structured
   influence bound that is not a worst-case row sum, or something else). That is a new
   design task, not a GRID-SUP on a 2-link block.
4. SO3-BE, treated only as an upper bound on the infimum (+1.059 at best found, w = 1/2),
   remains a complement with Z2-VORTEX, not a substitute for a slice-response bound.
