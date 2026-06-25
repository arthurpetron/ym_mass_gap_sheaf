# Wall-1 reduction campaign — π-free, node-free (2026-06-25)

**Capstone summary of the campaign that reduced the all-order SU(2) heat-kernel
character Gram positive-semidefiniteness ("Wall-1") to three named analytic
atoms, via a π-free node-free route, plus two finite Turok-template artifacts.**

This document is a self-contained, honest record. **Wall-1 is REDUCED, not
closed.** The three atoms are genuine open analytic convergence/interchange
obligations. The Clay Yang–Mills mass-gap problem remains OPEN; the continuum
(`a → 0`) frontier is untouched here. Conventions: "axiom-clean" means
`#print axioms` reports at most `propext` and `Quot.sound` (both MLTT/HoTT-valid),
with no `Classical.*`, no `sorryAx`, no `native_decide`.

---

## 1. What Wall-1 is

Wall-1 is the all-order positive-semidefiniteness of the SU(2) heat-kernel
character Gram form. On the abstract moment data it is the predicate

    GramRed.MomentSquarePos M  :=  ∀ N c,  momentSquare M c N ≥ 0,

i.e. the GNS energy `E(q²)` of every finite character combination
`q = Σ_{μ<N} c_μ χ_μ` is nonnegative, at every order `N` simultaneously, where
`momentSquare M c N = Σ_{μ,ν<N} c_μ c_ν G_{μν}` and `G_{μν} = Σ_c N^c_{μν} m_c`
is the fusion (Clebsch–Gordan) character Gram entry built from the heat-kernel
moments `m_s = (s+1)·a^{s(s+2)}`, `a = e^{−t/4} ∈ (0,1]`.

Finite orders `N ≤ 3` were already unconditional (`MomentSquarePSD.momentSquarePos_upTo`,
the empty/diagonal cases plus the bridged 2×2/3×3 LDLᵀ certificates). The wall
is the all-`N` statement.

---

## 2. The π-free strategy

The route realizes the Gram form as a genuine integral against the semicircle
weight, using the second-kind Chebyshev basis `U_e`:

- the orthogonality matrix `∫_{−1}^1 U_c(x) U_d(x) √(1−x²) dx = semiInt·δ_{cd}`
  is the Gram of the `U`-basis w.r.t. the semicircle weight, equal to
  `semiInt·I` (manifestly PSD);
- the R-expansion `R = Σ_e r_e U_e` with `r_e = 2a·m_e` reproduces the moment
  Gram: `∫U_pU_q R √ = (semiInt·2a)·gram(p,q)`;
- summing against `c_a c_b` gives `∫(Σc_aU_a)² R √ = (semiInt·2a)·momentSquare`,
  and the integrand is `(square)·(R ≥ 0)·(√ ≥ 0) ≥ 0`, so `momentSquare ≥ 0`.

**π-free / node-free.** `semiInt := ∫_{−1}^1 √(1−x²)` is carried as an ABSTRACT
positive constant. Its exact value π/2 is deliberately NOT proved — the
Machin-π / arctan-series route is avoided. Only `semiInt ≥ 0` (and the
enclosure `≤ 2`) is needed, and that is proved. The Riemann sums use uniform
midpoints; no special quadrature nodes are required.

---

## 3. The orthogonality → moment-integral → PSD chain

Reading order and what each step proves:

1. **`SemicircleBoundClosed.semiInt`** — the unconditional constructive Riemann
   integral `∫_{−1}^1 √(1−x²)`, with hypothesis-free convergence
   (`semiInt_converges`) and enclosure `0 ≤ semiInt ≤ 2` (`semiInt_nonneg`,
   `semiInt_leRat_two`). First fully-rigorous constructive Riemann integral in
   the library.

2. **`ChebOrthoMatrix.orthMatrix`** — the orthogonality matrix
   `ConvergesTo (seqOrth2 c d) (if c = d then semiInt else czero)`, i.e.
   `[∫U_cU_d√]_{cd} = semiInt·I`, PSD via `orthMatrix_diag_nonneg`. The general
   pointwise fusion `chebU_fusion : U_c·U_d = Ufusion c d` (proved here by
   two-step induction through the Dirichlet-kernel fold) and the `ConvergesTo`
   linearity lemmas (`convergesTo_add`/`_csum`/`_congr_seq`, built from scratch)
   are UNCONDITIONAL; the matrix is CONDITIONAL only on `OffDiagClosed`.

3. **`MomentIntegralPSD.momentIntegral_entry`** — the per-entry identity
   `∫U_pU_q R √ = (semiInt·2a)·gram(p,q)`. The fusion / `r_e = 2a·m_e`
   (`RCoeffReproduction.rCoeff_eq_two_a_moment`) / gram algebra is
   UNCONDITIONAL; CONDITIONAL only on the per-edge `RProjection`.

4. **`MomentIntegralPSD.momentSquare_nonneg`** — the CAPSTONE
   `SOSIntegral M ⇒ MomentSquarePos M`, via the proved reduction
   `MomentSquarePSD.momentSquarePos_of_uniformSOS`
   (`SOSIntegral` is definitionally `UniformGramSOS`). SU(2) specialization:
   `wilson_momentSquare_nonneg`; PSD form: `wilson_gramPSD_of_sosIntegral`.

All of steps 1–4 are axiom-clean (`propext`/`Quot.sound`).

---

## 4. The three named atoms (the honest open set)

Wall-1 (`MomentSquarePos`) is reduced to EXACTLY these three, all carried as
explicit hypotheses, never hidden:

| Atom | Where | Shape | What it is |
|---|---|---|---|
| `ChebOrthoMatrix.OffDiagClosed` | `ChebOrthoMatrix.lean` (⇐ `ChebOrthoBudget.cellBoundExists`) | `Prop` | even off-diagonal √-weighted FTC: `∀ e ≥ 1, ∫U_e√ = 0` (summed midpoint-quadrature error estimate for even `e ≥ 2`) |
| `MomentIntegralPSD.RProjection a` | `MomentIntegralPSD.lean` | Type-level `structure` (carries `edgeIntegral : Nat → CReal`) | R-series sum-integral interchange `∫U_e R √ = semiInt·r_e` per edge |
| `MomentIntegralPSD.SOSIntegral M` | `MomentIntegralPSD.lean` (`= UniformGramSOS M`) | Type-level `×'` | SOS-integrand identity `(semiInt·2a)·momentSquare = ∫(Σc_aU_a)²R√` + Riemann convergence of the proved-nonnegative SOS sums |

`RProjection` and `SOSIntegral` are genuine Type-level data (a `structure` and a
`×'`-valued `Type`), per the MLTT/HoTT witnesses-as-data discipline.
`OffDiagClosed` is a `Prop` (a `ConvergesTo` statement), derived from
`cellBoundExists`/`BudgetExists`, which are `Prop`-∃ analytic obligations.

All three are analytic convergence/interchange obligations — the same flavor as
the already-proved unconditional semicircle convergence
(`semiInt_converges`). None is a `True` stub, an `eqv_refl` fake, or a hidden
axiom.

---

## 5. What is UNCONDITIONALLY proved in the chain

Beyond the structure in §3, the campaign proves outright (axiom-clean):

- `ChebOrthoOffDiag.orthInt_odd_converges` — the ODD off-diagonal vanishing
  (the odd half of the orthogonality off-diagonal needs no atom).
- `ChebUDClosure.Bderiv_identity_uncond` — the polynomial antiderivative
  identity (`Gval′ = −f_e`) feeding the even FTC.
- `ChebOrthoEvenFTC.telescope_sum` / `GvalDiff_vanishes` — the discrete
  telescope and boundary vanishing underneath the even FTC (so the only even
  residual is the summed interior+boundary error estimate `cellBoundExists`).
- `SemicircleBoundClosed.semiInt` and friends — the unconditional semicircle
  Riemann integral (§3.1).
- `ChebOrthoMatrix.chebU_fusion`, `convergesTo_add`/`_csum`/`_congr_seq`,
  `orthSum2_eq_fusion_sum` — the general pointwise fusion and the `ConvergesTo`
  linearity / fusion-sum reduction.

---

## 6. Module map

| File | Role |
|---|---|
| `SemicircleBoundClosed.lean` | unconditional `∫√(1−x²) = semiInt`, convergence + enclosure |
| `SemicircleValue.lean` / `SemicircleValueRes.lean` | semicircle value-side support |
| `ChebUDClosure.lean` | unconditional antiderivative identity `Bderiv_identity_uncond` |
| `ChebOrthoEvenFTC.lean` | even FTC telescope + boundary vanishing (proved) |
| `ChebOrthoWeightedFTC.lean` | √-weighted FTC plumbing |
| `ChebOrthoFTCEstimate.lean` | `BudgetExists`/`SumTwoSidedBound`/rate-⇒-limit bridge |
| `ChebOrthoBudget.lean` | the even residual `cellBoundExists` ⇒ `OffDiagClosed` reduction |
| `ChebOrthoOffDiag.lean` | odd off-diagonal (unconditional) + `seqOrth` substrate |
| `ChebOrthoMatrix.lean` | orthogonality matrix `[∫U_cU_d√] = semiInt·I` (cond. `OffDiagClosed`) |
| `MomentSquarePSD.lean` | `UniformGramSOS ⇒ MomentSquarePos` reduction; finite orders ≤ 3 |
| `MomentIntegralPSD.lean` | R-projection + SOS assembly + **the capstone** |

---

## 7. The two Turok-template artifacts

### Krein–OS reconstruction scaffold (`KreinOS.lean`)

`krein_os_reconstruction`: an indefinite-metric (Krein/BRST/ghost) datum with
Θκ-positivity + κ/BRST compatibilities ⇒ a positive physical sector with a
descended transfer operator, and (given a gap datum) a strictly positive
finite-volume mass gap. `kreinReconstructionExample` is a NON-VACUOUS
2-dimensional inhabitant (diagonal indefinite metric, swap involution, trivial
BRST), so the lemma is not vacuously true.

- **Scope (honest):** Stage-1 SCAFFOLDING — a structural generalization of the
  repo's GNS reconstructions to the indefinite-metric setting. **NAMED-open:**
  the projection of *pure* Yang–Mills onto this template (exhibiting the YM
  field space as a `KreinDatum` with a genuine BRST metric and verifying the YM
  gap datum) is out of scope. The positive-metric Wilson OS2 is already
  unconditional elsewhere, so this Krein layer is off the pure-YM critical path.
- Axiom-clean.

### Bakry–Émery 2nd-gap proof (`BakryEmeryGap.lean`)

`be_to_poincare`: the slacked finite-regulator Bakry–Émery hypothesis
`ρ·E[Γ(f)] − ε·E[f²] ≤ E[Γ₂(f)]` ⇒ the Poincaré/variance inequality, by the
genuine BE chain (Bochner + Dirichlet, cancelled). `be_gap`: the
strictly-positive finite-volume gap `ρ` as an `IsPositive` witness.
`beDatumExample`: a non-vacuous inhabitant (symmetric two-state walk, ρ = 2,
ε = 0).

- **Scope (honest):** a SECOND, independent proof of the **fixed-spacing**
  gap. The `−ε` slack is the finite-regulator key. The `a → 0` continuum use is
  explicitly NOT claimed — the carré-du-champ functional is the wrong form in
  the continuum limit. Corroboration of the clustering route, not a new
  continuum result.
- Axiom-clean.

---

## 8. Wall-2: m ≤ 3 done, m ≥ 4 open (`LoopyLinkIntegral.lean`)

The `m`-fold shared-link SU(2) Haar integral `L_m = ∫ ∏ χ_{r_i}` is evaluated
for `m = 2` (orthogonality kernel δ) and `m = 3`
(`tripleCharInt_eq_fusionInd : ∫χ_aχ_bχ_c = N_{abc}`, the single-6j fusion
multiplicity, by Clebsch–Gordan-then-orthogonality). The general `m ≥ 4` case
(the `(m−2)`-fold 6j network) and the per-link `LinkCollapseData` it feeds are
NAMED-open. Closing it upgrades the fixed-spacing gap from tree to general loopy
geometry with no change to the abstract Dobrushin/Kotecký–Preiss tail
(`Z_step_ratio` is geometry-independent). Axiom-clean.

---

## 9. Honest status and remaining-work list

**Real prior result, unconditional (unchanged):** the fixed-spacing tree-scoped
infinite-volume mass gap `TreeFixedSpacingGap.tree_fixed_spacing_mass_gap`
(axiom-clean; geometrically restricted to ≤ 2-shared-link geometry; the
continuum `a → 0` limit is NOT addressed).

**This campaign:**
- Wall-1 (`MomentSquarePos`) is REDUCED to the three named atoms
  {`OffDiagClosed`, `RProjection`, `SOSIntegral`} — with the entire
  orthogonality → moment-integral → PSD structure PROVED. It is NOT closed.
- The semicircle constructive Riemann integral `semiInt` is UNCONDITIONAL.
- Krein-OS and Bakry–Émery are honest-scope finite scaffolds (pure-YM
  projection / continuum use respectively out of scope).
- Wall-2 `m ≤ 3` is proved; `m ≥ 4` 6j network is open.

**Remaining work to close Wall-1 (the three analytic atoms):**
1. `cellBoundExists e` for every even `e ≥ 2` — the summed midpoint-quadrature
   error estimate (interior `C(e)·h/δ` + boundary `C(e)·δ`, balanced at
   `δ ≈ √h`) bounding the rational approximants of the even Riemann sums; feeds
   `OffDiagClosed`.
2. `RProjection` — the interchange of the integral with the infinite R-series
   `∫U_e R √ = Σ_f r_f ∫U_eU_f√ = semiInt·r_e`.
3. `SOSIntegral` — the SOS-integrand moment-integral identity together with the
   Riemann convergence of the proved-nonnegative SOS sums.

All three are the same flavor as the already-proved unconditional semicircle
convergence — analytic, but no longer structural or combinatorial.

**The whole library builds clean (289 jobs); every load-bearing declaration is
axiom-clean (`propext`/`Quot.sound` only). The Clay problem remains OPEN.**
