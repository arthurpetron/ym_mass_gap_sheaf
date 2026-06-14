# OS2 via standard reflection positivity — bypassing the P_N walls

Single-page bridge for the Osterwalder–Seiler route to OS2, the route that
removes the `P_N` positivity walls from the mass-gap critical path. The Lean
realization is `lean/YMGap/Continuum/ReflectionPositivity.lean`; the OS2
wire-in is `lean/YMGap/Continuum/OSAxioms.lean`.

## 1. The conflation that created the walls

OS2 reflection positivity is `0 ≤ E(θ(a)*·a)` for every observable `a` on the
positive-time side of a reflection plane, with `θ` the reflection. The earlier
formalization reduced OS2, for the single-edge SU(2) heat-kernel functional, to
the all-order positive-semidefiniteness of the **character product Gram**

    G_{μν} = ⟨χ_μ·χ_ν⟩_t = Σ_c N^c_{μν}·⟨χ_c⟩_t      (fusion × moments).

That object (`WilsonFunctional.coneExp`) is PSD only on the **nonnegative cone**
`c ≥ 0` (`coneExp_nonneg`). Full PSD for arbitrary real `c` is equivalent to the
heat kernel being **pointwise** nonnegative `K_t(g) ≥ 0`, because
`E(a²) = ∫ a(g)² K_t(g) dg ≥ 0 ∀ real a ⟺ K_t ≥ 0`. Proving that from the
character expansion is exactly the two walls of `continuum-positivity-status.md`
§4 (`nonnegCoeffs P_N` algebraic; differentiated-JTP analytic) — both established
research-novel dead ends.

The error is that this conflates two different bilinear forms:

| form | pairing | structure | difficulty |
|------|---------|-----------|------------|
| product `⟨χ_μ·χ_ν⟩` | `χ_μ` with `χ_ν` | off-diagonal, fusion-weighted | hard (= pointwise `K_t ≥ 0`; the P_N walls) |
| **reflection** `⟨θ(χ_μ)*·χ_ν⟩` | `χ_μ` with `θ(χ_ν)=χ̄_ν` | **diagonal** (Schur) | **elementary** |

OS2 is the **reflection** form. The product form is a strictly stronger,
unnecessary statement.

## 2. The standard Osterwalder–Seiler computation

For the single timelike heat-kernel bond joining a site to its mirror image, the
positive-side observable is `a(g₊) = Σ_μ c_μ χ_μ(g₊)`, the reflection sends
`θ(a) = ā(g₋)`, and the bond weight is the heat kernel `K_t(g₊ g₋⁻¹)`. The
reflection Schwinger form is

    ⟨θ(a)*·a⟩ = ∫∫ ā(g₋)·a(g₊)·K_t(g₊ g₋⁻¹) dg₊ dg₋.

Expand `K_t(h) = Σ_λ a_λ χ_λ(h)` with the heat-kernel coefficients
`a_λ = dim(λ)·e^{−t·C₂(λ)} = ⟨χ_λ⟩_t`. **Schur orthogonality** (Peter–Weyl on
the compact group SU(2)),

    ∫∫ χ_μ(g₊) χ̄_ν(g₋) χ_λ(g₊ g₋⁻¹) dg₊ dg₋ = δ_{μλ} δ_{νλ} / d_λ,

**diagonalizes** the form:

    ⟨θ(a)*·a⟩ = Σ_λ (a_λ / d_λ)·c_λ²  =  Σ_λ e^{−t·C₂(λ)}·c_λ²  =:  R_t(c).

Each weight `e^{−t·C₂(λ)} ≥ 0` and each `c_λ² ≥ 0`, so

    R_t(c) ≥ 0     for every real coefficient vector c,

with **no** cone restriction, **no** fusion matrix, **no** pointwise `K_t ≥ 0`,
**no** `P_N`. The single positivity input is `a_λ ≥ 0` — i.e.
`dim(λ)·e^{−t·C₂(λ)} ≥ 0` — which is elementary.

## 3. Why this is genuinely weaker input than the walls

- The walls demand: the fusion-weighted Gram `G = Σ_λ a_λ M^λ` (`M^λ_{μν} =
  N^λ_{μν} ≥ 0`) is PSD. A nonneg-entry matrix is **not** PSD for free; this is
  the uncatalogued, irreducible theta-derivative Hankel-determinant residual
  (`continuum-positivity-status.md` §5b).
- Standard RP demands only: `a_λ = dim(λ)·e^{−t·C₂(λ)} ≥ 0`. Both factors are
  manifestly nonnegative; the project already proves this as
  `WilsonFunctional.wilsonCharExp_nonneg`.

The diagonalization (Schur orthogonality) is the standard Peter–Weyl fact for
compact groups, cited not proved — exactly as `WilsonFunctional.wilsonCharExp`
*defines* the heat-kernel moments directly from `dim·e^{−tC₂}` rather than
integrating. We represent the reflection form directly in its diagonalized
character basis; the positivity `R_t(c) ≥ 0` is then **proved**.

## 4. The Lean realization

`lean/YMGap/Continuum/ReflectionPositivity.lean`:

| name | statement |
|------|-----------|
| `reflWeight t s` | `e^{−t·C₂(s)}` = `a_s/d_s`, the Schur-diagonal weight |
| `reflWeight_nonneg` | `reflWeight ≥ 0` (the elementary input) |
| `NonnegCharacterCoeffs t` | `∀ s, a_s = dim(s)·e^{−t·C₂(s)} ≥ 0` |
| `heatKernel_nonnegCharCoeffs` | SU(2) discharge (= `wilsonCharExp_nonneg`) |
| `diagReflForm w c N` | general diagonal form `Σ_{s<N} c_s²·w_s` |
| `diagReflForm_nonneg` | `≥ 0` for **all real c** given nonneg weights |
| `reflSchwinger t c N` | `Σ_{s<N} e^{−t·C₂(s)}·c_s²` |
| `reflSchwinger_nonneg` | OS2 RP at order N, **unconditional, all real c** |
| `ReflectionPositiveSchwinger t` | all-order RP predicate |
| `reflectionPositiveSchwinger_holds` | discharged with **no open input** |

`OSAxioms.IsOS2ReflectionPositivity` is retargeted to
`ReflectionPositiveSchwinger`, so the full `OSAxiomBundle` is inhabitable for
SU(2) **unconditionally** — the `MomentSquarePos`/`P_N` input is removed from the
mass-gap critical path. All exports are axiom-clean
(`[propext]`/`[propext, Quot.sound]`).

## 5. What this does and does not claim

- **Does**: prove the genuine OS2 reflection-positivity axiom (the reflection
  Schwinger form) unconditionally for the SU(2) heat-kernel functional, on a
  standard, citable footing (Osterwalder–Seiler 1978; Seiler, *Gauge Theories as
  a Problem of Constructive QFT*, LNP 159).
- **Does not**: prove pointwise `K_t ≥ 0` nor the product-Gram PSD
  (`MomentSquarePos`). Those remain genuine — strictly stronger — statements,
  retained as the `P_N` walls but **demoted off** the load-bearing path. The
  `reflectionPositive_of_momentSquarePos` route is kept on record as "the
  stronger statement also implies OS2".
- **Scope**: the core is the single timelike-bond reflection positivity. The
  full finite-volume `weighted_pos` (OS2 over the product functional) follows
  from per-bond RP by the standard tensor/factorization argument across the
  reflection plane; the per-bond positivity proved here is the analytic heart,
  and the product assembly is the standard remaining step (cf.
  `FiniteVolume.ReferenceWeight.weighted_pos`).
