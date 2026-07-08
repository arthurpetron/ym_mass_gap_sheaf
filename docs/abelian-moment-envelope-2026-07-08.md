# Abelian moment envelope — extending the abelian shadow toward M1/M2 via the modular dual

**File:** `lean/YMGap/Continuum/AbelianMomentEnvelope.lean` (NEW, imported in `YMGap.lean`).
**Status:** `lake build` exit 0 (781 jobs), guard = 5 (all Clay-frontier types uninhabited),
every new theorem axiom-clean (`#print axioms ⊆ {propext, Quot.sound}`; several are axiom-free).
No `sorry` / `native_decide` / `Classical` / `Prop := True`. Nothing committed.

## What was proved (EXACT, load-bearing spine of the M1/M2 envelope)

The live residual `hlocalize` consumes is `CircleFourierPowerModel.SaddleVarianceFloor` /
`FullRangeFloor` — the `−2` curvature floor `Δ²_t⟨D²⟩ ≥ −2` on the tilted-measure variance
`⟨D²⟩_t = variance of D=t−2p under μ_t(p) ∝ coeffW(w,p)·coeffW(w,t−p)`. I built the abelian moment
objects for its abelian shadow `μ̂_t(p) ∝ abelCoeff(w,p)·abelCoeff(w,t−p)` and closed its finite,
exact structural spine:

| Theorem | Content | axioms |
|---|---|---|
| `abelAc`, `abelDmom` (+ `_nonneg`) | abelian partition sum & 2nd moment as finite `Q'` sums | — |
| `abelWeight_eq` | `abelCoeff w p·abelCoeff w (t−p) ≃ w^{p²+(t−p)²}` (exact `qpow` mult.) | propext |
| **`gauss_split_nat`** | **`2·(p²+(t−p)²) = t² + D_p²`** — the EXACT discrete-Gaussian kernel `q^{D²}` (`q=√w`) that Poisson/Jacobi acts on | propext,Quot |
| **`abelWeight_symm`** | `weight(p) ≃ weight(t−p)` — the reflection forcing `⟨D⟩_t = 0` EXACTLY (the M1 **mean**) | propext,Quot |
| `abelDmom_zero`, `abelDmom_one` | corner ties `⟨D²⟩_0 = 0`, `⟨D²⟩_1 = 1` (exact endpoints of the `−2` corner) | propext |
| **`abelFullRangeFloor_zero`** | the abelian `−2` curvature floor at the corner window `s=0`, ∀ `0≤w` (cleaner than SU(2): no Weyl factors) | propext |
| **`abelDmom_le_tsq`** | `abelDmom w t ≤ t²·abelAc w t`, i.e. `⟨D²⟩_t ≤ t²` (exact truncation envelope, `M2`-type) | propext,Quot |
| **`coeffW_prod_eq_weyl_abel`** | **the SU(2) lift:** `w²·(coeffW w p·coeffW w q) ≃ (dimQ p·dimQ q)·(abelCoeff w (p+1)·abelCoeff w (q+1))` | propext,Quot |
| `abelDmom_nonconstant` | non-vacuity: `abelDmom (1/2) 1 ≠ 0`, `abelDmom (1/2) 0 = 0` | none |
| `momentEnvelopePoissonDual_zero` | the `s=0` face of the named residual is DISCHARGED | propext |

### 1. The modular dual for the moments — what genuinely closed
The abelian tilted weight is proved to be an EXACT discrete Gaussian: `abelWeight_eq` +
`gauss_split_nat` give exponent `p²+(t−p)² = ½(t² + D²)`, i.e. weight `q^{D²}·q^{t²}` with `q=√w`,
`D=t−2p`. This is precisely the kernel `ϑ(θ,q)` on which the Jacobi transform `ϑ(1/τ)=√τ·ϑ(τ)`
operates. On this exact kernel I closed the finite moment facts the transform needs as inputs/outputs:
the **mean is exactly 0** (`abelWeight_symm`, the palindrome `p↔t−p`), the **corner ties**
`⟨D²⟩_0=0, ⟨D²⟩_1=1` (the exact source of the `−2` corner), the **`−2` curvature floor at `s=0`**
(`abelFullRangeFloor_zero`, unconditional in `w`), and the **variance envelope** `⟨D²⟩ ≤ t²`.

### 2. The Weyl perturbation on the moments — closed exactly
`coeffW_prod_eq_weyl_abel` lifts every abelian moment weight to the SU(2) moment weight EXACTLY:
the SU(2) tilted weight `coeffW w p·coeffW w q` equals the abelian shifted-charge theta weight
`abelCoeff w (p+1)·abelCoeff w (q+1)` times the Weyl-dimension product `dimQ p·dimQ q` and the overall
`w^{−2}` Casimir constant. Combined with `AbelianFusionCLT.weyl_dim_defect`
(`(dimQ(s+1))² = dimQ s·dimQ(s+2)+1`, relative parameter `1/(s+2)² ≤ 1/4`), the SU(2) moments
`acNfull`/`dmomNfull` are the exact abelian theta moments perturbed by a uniformly-controlled Weyl
factor — the "SU(2) M1/M2 = abelian M1/M2 + O(Weyl)" decomposition, now term-exact.

## The SHARP residual (named, honest)

`MomentEnvelopePoissonDual w` (Type-level, NAMED-OPEN, never `sorry`): the SHARP scaling bounds
**M1** `V(u)·(1−u) ≤ 2` and **M2** `Var(u)·(1−u)² ≤ 8`, uniform in the window, both parities. Its
`s=0` face is proved (`momentEnvelopePoissonDual_zero`); the residual is the uniform-in-`s` theta-ratio
scaling.

**Why it is genuinely transcendental (adversarially checked).** Both numerator `Σ_D D²q^{D²}` and
denominator `Σ_D q^{D²}` diverge as `w→1` (`~ε^{-3/2}`, `~ε^{-1/2}`, `ε=−ln u`); only the theta RATIO
stays `O(1/ε)`. A naive super-log-concave/geometric majorant drops the `1/√(1−u)` denominator growth
and the bound blows up — I verified this failure mode. So NO finite `Q'` majorant closes M1/M2; the
Poisson/Jacobi transform on `gauss_split_nat`'s exact kernel is required. Per the numerics
(`poisson_M1M2.md`, dual verified to ≤1e-56), after the transform the content is finite rational:
M1-even is immediate from `P₁≥0` + `(1−u)≤−ln u`; the other three close by a region split at `u=3/4`
(truncated θ-series on `[1/4,3/4]`, ε-dual rational inequality on `[3/4,1)`). The ONE step not in the
`Q'`/`CReal` core is the modular transform itself (needs `√` of general `w` and an infinite convergent
θ-series with `π`). That single bridge is the sharp residual.

## Verdict
Is the M1/M2 moment envelope closed abelian-exact + Weyl-controlled? **The finite EXACT structural
spine is closed** — discrete-Gaussian kernel, exact mean-zero, corner ties, base curvature floor,
`⟨D²⟩≤t²` envelope, and the exact SU(2) Weyl lift, all axiom-clean. **The sharp uniform scaling
bounds M1/M2 are NOT closed**: they are genuinely transcendental (proved not finite-majorable) and
require the Poisson/Jacobi modular transform, which is outside the current `Q'`/`CReal` substrate
(no `√` of general `w`, no infinite θ with `π`). That transcendental bridge — `MomentEnvelopePoissonDual`
— is what remains for `hlocalize`'s fusion local-CLT. The Clay YM mass gap remains OPEN.

**Next front:** build a `CReal`-level Jacobi θ with its modular inversion (the `√τ` transform) so the
`MomentEnvelopePoissonDual` residual becomes provable from the already-mapped finite rational atoms.
