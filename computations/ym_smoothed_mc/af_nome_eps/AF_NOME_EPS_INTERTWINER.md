# afNomeSchedule lit εⱼ under both ApproxRgIntertwiner shapes (0⁺⁺/√σ proxy)

**Literature / MC proxy only — not a proof** of intertwiner inhabitability,
RG summability, asymptotic freedom, or any Lean theorem.
Date: 2026-10-06. Repo path: `computations/ym_smoothed_mc/af_nome_eps/`.
Repro: `python3 af_nome_eps_intertwiner.py` (imports sibling `af_nome_asqrt/`
or falls back to the a10b9ea4 cited knots).

Companion Lean / audit (formulas only; this note does not discharge them):
`lean/.../BF4WilsonAllNomeRGStepComposition.lean`,
`audits/SCOPE-RG-STEP-COMPOSITION-REDUCTION-2026-10-06.md`.

## Continuum μ and lattice gap proxy

Published SU(2) continuum \(m(0^{++})/\sqrt{\sigma}\):

| source | μ | cite |
|--------|--:|------|
| **Lucini–Teper–Wenger (primary)** | **3.78(7)** | JHEP 06 (2004) 012 Table 14 [hep-lat/0404008] |
| Teper review (cross-check) | 3.74(12) | hep-th/9812187 Table 1 |

Finite-β lattice cross-checks (LTW04 Table 5, SU(2); not used in the estimator):
e.g. β=2.5115, \(a\sqrt{\sigma}=0.1768(8)\), \(am_{0^{++}}=0.658(10)\) ⇒
\(m/\sqrt{\sigma}\approx 3.72\) (near continuum). Morningstar–Peardon is SU(3);
here we stay with Teper/LTW SU(2).

**Primary estimator uses continuum μ = 3.78** (constant along the schedule;
marked continuum, not β-dependent lattice). Sensitivity with Teper 3.74 is
quoted below (Lean \(S_4\) shifts by ≲ 0.5%).

Reuse of prior \(a\sqrt{\sigma}\) table (commit **a10b9ea4**, do not reinvent):

| j | β | \(a\sqrt{\sigma}\) | source |
|--:|--:|-------------------:|--------|
| 4 | 2.016 | 0.728 | extrap FHK |
| 5 | 2.275 | 0.392 | interp FHK |
| 6 | 2.533 | 0.170 | interp FHK |
| 7 | 2.901 | 0.0554 | two-loop |
| 8 | 3.159 | 0.0287 | two-loop |

Schedule: \(1-w_j=A/(j+\kappa\lfloor\log_2(j+1)\rfloor+4)\), \(A=1.942\),
\(\kappa=51/121\); \(\beta=-1/(2\ln w)\). Primary knots FHK hep-lat/9208012,
UKQCD hep-lat/9209007; see sibling `AF_NOME_ASQRT_SCHEDULE.md`.

Define lattice gap and continuum-inspired one-step transfer eigenvalue:

\[
\Delta_j = \mu\cdot(a\sqrt{\sigma})_j,
\qquad
\lambda_j = e^{-\Delta_j}.
\]

**Explicit:** \(\lambda_j\) is a continuum-inspired **PROXY** for the Lean
VacSq one-step rate \(r_j\), not a measured VacSq / heat-kernel rate on any
of our lattices. Lit/MC only.

## Two intertwiner shapes (from Lean reduction)

κ-free Lean `RgRateRelation`:
\[
r_{\mathrm{Fine}}^2 \le r_{\mathrm{Coarse}} + \varepsilon
\quad\Rightarrow\quad
\varepsilon_{\mathrm{needed}} = \max(0,\, r_{\mathrm{Fine}}^2 - r_{\mathrm{Coarse}}).
\]
Also report the signed defect \(r_{\mathrm{Fine}}^2 - r_{\mathrm{Coarse}}\)
(even when negative).

κ-form (Lean identification \(r_F^2 = \kappa(r_C^2+\varepsilon)\) with **κ = 1**
for this lit probe):
\[
\varepsilon_{\mathrm{needed}}^{\kappa}
  = \max(0,\, r_{\mathrm{Fine}}^2 - r_{\mathrm{Coarse}}^2).
\]

### Shape A — one fine step vs one coarse (\(T_{j+1}\leftrightarrow T_j\))

\(r_{\mathrm{Fine}}=\lambda_{j+1}\), \(r_{\mathrm{Coarse}}=\lambda_j\).
Report \(\varepsilon^A_j\) from κ-free and from κ-form. Compares **unequal**
physical times (one lattice step at two different \(a\)), so typically needs
larger ε under the κ-form.

### Shape B — two fine vs one coarse (\(T_{j+1}^2\leftrightarrow T_j\))

Lean-preferred **physical-time matching** when \(a\) halves:
continuum ideal \(\lambda_{j+1}^2 \approx \lambda_j\) when \(a_{j+1}/a_j = 1/2\).
Probe: fine two-step factor \(\lambda_{j+1}^2\) vs coarse one-step \(\lambda_j\):
\[
\varepsilon^B_j = \max(0,\, \lambda_{j+1}^2 - \lambda_j)
\]
(same κ-free algebra as Shape A; interpret as \(T^2\leftrightarrow T\) when
equality holds at exact dyadic \(a\)). Also report \(|\lambda_{j+1}^2-\lambda_j|\)
and the \(a\)-ratio from the \(a\sqrt{\sigma}\) table (→ 1/2 test of a10b9ea4).

**Numerically** \(\varepsilon^A_{\kappa\mathrm{-free}} = \varepsilon^B\) on this
proxy; the distinction is interpretive. Shape B is the healthier matching;
Shape A κ-form is the stricter unequal-time budget.

## Table (μ = 3.78)

| j | β | \(a\sqrt{\sigma}\) | Δ | λ | \(\varepsilon^A_{\kappa\mathrm{f}}\) | \(\varepsilon^A_\kappa\) | \(\varepsilon^B\) | \(a_{j+1}/a_j\) |
|--:|--:|-------------------:|--:|--:|-------------------------------------:|------------------------:|-----------------:|----------------:|
| 4 | 2.016 | 0.728 | 2.753 | 0.0637 | **0** | 0.0477 | **0** | 0.538 |
| 5 | 2.275 | 0.392 | 1.481 | 0.2275 | 0.0488 | 0.2245 | 0.0488 | 0.434 |
| 6 | 2.533 | 0.170 | 0.643 | 0.5256 | 0.1322 | 0.3816 | 0.1322 | 0.326 |
| 7 | 2.901 | 0.0554 | 0.209 | 0.8111 | **0** | 0.1473 | **0** | 0.518 |
| 8 | 3.159 | 0.0287 | 0.108 | 0.8973 | — | — | — | — |

Signed defects \(\lambda_{j+1}^2-\lambda_j\) (κ-free) / \(\lambda_{j+1}^2-\lambda_j^2\) (κ):
−0.012 / +0.048; +0.049 / +0.224; +0.132 / +0.382; −0.006 / +0.147.
Negative κ-free defects at j=4,7 ⇒ \(\varepsilon=0\) there (a-ratio near 1/2).

## Weighted partial sums

Lean `weightedErrorSum` (j0 = 4, n = 4 steps 4→5 … 7→8):
\[
S_n = \sum_{k=0}^{n-1} 2^k\cdot\varepsilon(j_0+k).
\]

| shape | \(S_1\) | \(S_2\) | \(S_3\) | \(S_4\) |
|-------|--------:|--------:|--------:|--------:|
| A κ-free (= B) | 0 | 0.0975 | 0.626 | **0.626** |
| A κ-form | 0.0477 | 0.497 | 2.023 | **3.201** |

Project-status form \(\sum_{j=4}^{7} 2^j\,\varepsilon_j\) (absolute \(2^j\) weights;
**different indexing** from Lean \(S_n\)):

| shape | Σ |
|-------|-----:|
| A κ-free (= B) | **10.02** |
| A κ-form | **51.22** |

(Teper μ = 3.74: Lean \(S_4\) = 0.624 / 3.195 / 0.624 — negligible shift.)

## Verdict (one paragraph; lit/MC only)

On this continuum 0⁺⁺/√σ proxy, Shape B (and numerically identical Shape A
κ-free) needs **zero** ε at the smooth ends where \(a_{j+1}/a_j\approx 1/2\)
(j = 4→5, 7→8) and only modest mid-window ε where the a√σ ratios undershoot
1/2 (same pattern as a10b9ea4). The Lean-indexed weighted sum
\(S_4\approx 0.63\) stays **O(1)** and below the seed-margin scale ~1 — 
**summable-looking** for this lit proxy, with Shape B the healthier
physical matching. Shape A κ-form (unequal physical times, squares of rates)
inflates to \(S_4\approx 3.2\) / project-Σ ≈ 51 and is clearly the hungrier
budget. None of this constructs a Φⱼ, measures a VacSq rate, or proves
summability — **lit/MC proxy only, not a proof**.

## Bibliography

1. B. Lucini, M. Teper, U. Wenger, *Glueballs and k-strings in SU(N) gauge
   theories: calculations with improved operators*, JHEP 06 (2004) 012
   [hep-lat/0404008]. Continuum SU(2) \(m_{0^{++}}/\sqrt{\sigma}=3.78(7)\)
   (Table 14).
2. M.J. Teper, *Glueball masses and other physical properties of SU(N) gauge
   theories in D=3+1: a review of lattice results for theorists*,
   hep-th/9812187. Continuum SU(2) \(m_{0^{++}}/\sqrt{\sigma}=3.74\pm 0.12\).
3. J. Fingberg, U. Heller, F. Karsch, Nucl. Phys. B 392 (1993) 493
   [hep-lat/9208012] (FHK \(a\sqrt{\sigma}\) knots).
4. S.P. Booth et al. (UKQCD), Nucl. Phys. B 394 (1993) 509 [hep-lat/9209007].
5. Sibling note: `computations/ym_smoothed_mc/af_nome_asqrt/AF_NOME_ASQRT_SCHEDULE.md`
   (commit a10b9ea4).
6. Lean: `YMGap/Continuum/BF4WilsonAllNomeRGStepComposition.lean`
   (`RgRateRelation`, `weightedErrorSum`, `ApproxRgIntertwiner`).
7. Audit: `audits/SCOPE-RG-STEP-COMPOSITION-REDUCTION-2026-10-06.md`.

## Files

- `af_nome_eps_intertwiner.py` — regenerates tables (imports sibling or hardcoded knots)
- `af_nome_eps_table.csv` — numeric step table
- `af_nome_eps_summary.txt` — weighted-sum digests
- This note: `AF_NOME_EPS_INTERTWINER.md`
