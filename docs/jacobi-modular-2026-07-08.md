# Jacobi modular inversion over CReal — deliverable & honest verdict

**Date:** 2026-07-08. Lean-core (`Q'`/`CReal`), axiom gate `propext`/`Quot.sound`, guard 5.

## Headline

- **BUILT (green, axiom-clean, non-vacuous):** the constructive Jacobi **ϑ₃ SERIES**
  `ϑ₃(q) = Σ_{n∈ℤ} q^{n²}` as a convergent `CReal` with an EXPLICIT geometric convergence
  modulus, for every rational nome `q ∈ (0,1)`. New file
  `lean/YMGap/Continuum/JacobiModularCReal.lean`. This is **step (1)** of the Poisson
  programme — the object the modular transform acts on. It did not previously exist: the
  repo had only the theta **product** (`ThetaConv.thetaConvCReal`, Jacobi triple-product
  form), never the **series** `Σ q^{n²}`.
- **NOT built (honest):** the modular inversion `ϑ₃(1/τ) = √τ·ϑ₃(τ)` itself (step 2), hence
  the M1/M2 closure `V·(1−w)≤2`, `Var·(1−w)²≤8` (step 3, `MomentEnvelopePoissonDual`), hence
  `hlocalize`'s fusion local-CLT (step 4). These **remain OPEN**. I did **not** fake the
  transform; no `Prop := True`, no assumed hypothesis passed off as a proof.

## What is in the Lean (all `#print axioms ⊆ {propext, Quot.sound}`, no `sorryAx`)

`namespace YMGap.Continuum.JacobiModularCReal`:

| decl | content | axioms |
|---|---|---|
| `thetaHalf q N` | `Σ_{i<N} q^{(i+1)²}` (finite `Q'` sum) | — |
| `thetaPartial q N` | `1 + 2·thetaHalf q N = Σ_{|n|≤N} q^{n²}` | — |
| `thetaPartial_succ` | `θ_{N+1} ≃ θ_N + 2·q^{(N+1)²}` (single-step increment) | `propext` |
| `q2_lt_one` | `q² < 1` for `0<q<1` | `propext,Quot.sound` |
| `q2pow_eqv` | `(q²)^l ≃ q^{2l}` | `propext,Quot.sound` |
| **`incr_le`** | **`2·q^{(l+1)²} ≤ geoIncrBase (2q) q² l`** — the geometric domination `q^{(l+1)²} ≤ q^{2l+1} = q·(q²)^l` (super-geometric decay of the discrete-Gaussian kernel; `(l+1)² ≥ 2l+1`) | `propext,Quot.sound` |
| `thetaPartial_up`/`_lo` | the two single-step bounds the limit engine consumes | `propext,Quot.sound` |
| **`thetaS q hq0 hq1 : CReal`** | **THE ϑ₃ SERIES** via `HKConvGen.crealOfGeoIncrementBase` at decay base `r=q²` | `propext,Quot.sound` |
| `thetaS_approx` | `approx N = thetaPartial q N` (genuine finite truncation) | `propext,Quot.sound` |
| **`thetaS_geRat_one`** | **`ϑ₃(q) ≥ 1`** (the `n=0` term; genuine non-vacuous bound) | `propext,Quot.sound` |
| `thetaS_geRat_zero` | `ϑ₃(q) ≥ 0` | `propext,Quot.sound` |
| `thetaPartial_nonconstant` | `θ_0(1/2)=1 ≠ 2=θ_1(1/2)` (non-constant; `n=1` term is real) | none |

The convergence modulus is genuine: `crealOfGeoIncrementBase` builds the `CReal` from the
partial sums `thetaPartial q` with the base-`q²` **telescoped geometric tail**
`geoTailBase (2q) q² n = (2q·H)·(q²)^n`, `H = 1/(1−q²)`, and the explicit
`ε ↦ δ = divPos ε (2q·H)` modulus. Not a placeholder — the same engine that realises the
project's heat-kernel and KP-limit `CReal`s.

## How far this closes M1/M2 and hlocalize

**It does not close them.** The finite/structural spine of the moment envelope was already
closed in `AbelianMomentEnvelope.lean` (exact kernel `gauss_split_nat` `q^{D²}`, reflection
`abelWeight_symm` ⇒ M1-mean = 0, the trivial `⟨D²⟩≤t²` envelope, the `−2` corner floor
`abelFullRangeFloor_zero` at `s=0`, the SU(2) Weyl lift `coeffW_prod_eq_weyl_abel`). The SOLE
remaining input is the **sharp uniform-in-window theta-ratio scaling**, which per the numerics
(`poisson_M1M2.md`, mpmath dps 40–60, 0 certificate failures) is closed by the
Poisson/Jacobi **modular inversion** applied to the exact kernel — plus finite rational
region-split algebra. This module supplies the **series object** that transform acts on, and
nothing more. `MomentEnvelopePoissonDual` and `hlocalize` are unchanged / still OPEN.

## The SHARP residual (named precisely)

The modular inversion `ϑ₃(1/τ) = √τ·ϑ₃(τ)` cannot even be **stated** as a finite `Q'`
inequality, and cannot be **proved** without genuine analysis absent from the `Q'`/`CReal`
core:

1. **Irrational dual nome.** The dual side is `ϑ₃` at `q' = e^{−π²/(−ln q)}`, which is
   irrational for rational `q`. Stating the identity as a `CReal` equality needs the theta
   series at a `CReal` (not `Q'`) nome — i.e. `CReal`-exp of a `CReal` (present `CRealExp`
   only exponentiates rationals). The `√τ` prefactor is available (`QuadraticKernel.sqrtPos`,
   `CRealSqrtCReal.csqrt`) and `π` is available (`Constructive/Pi.lean`); the missing
   substrate piece is `CReal`-exp-of-`CReal` for the dual nome.
2. **Poisson summation.** The identity `A = √(π/ε)·P₀` (and its two `ε`-derivative siblings
   `B, C` for the weighted moments) is genuine Poisson summation of `x^{2j}e^{−εx²}` /
   Jacobi imaginary transform — Fourier duality / heat-kernel uniqueness — which reduces to
   NO finite rational step. This is THE crux the numerics itself flags as "the one genuine
   piece of analysis; everything downstream is algebra."

Everything downstream (the dual tail lemmas `P₀≥1`, `|Q₁|≤2π²X`, …; the `v²`-cancellation
region split at `u=3/4`; the reduced single-variable `ε`-inequalities on `(0,7/24]` with a
~50× margin) IS finite rational and matches existing codebase toolkits (Leibniz/`theta4QuarterAnchor`,
geometric tails, `decide`) — but it is gated on the two transcendental inputs above.

## Verification (re-run this session)

- `lake build` (full): **exit 0, 782 jobs**, `Build completed successfully`.
- Frontier **guard 5**: `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited
  across YMGap.*` (M1/M2/hlocalize did NOT change reaction — correctly, since not discharged).
- `#print axioms` on the θ-series + modulus + `geRat` bounds: `[propext]` /
  `[propext, Quot.sound]` only; `thetaPartial_nonconstant` depends on no axioms. No `sorryAx`.
- `python3 scripts/lean_axiom_audit.py`: **PASS** (7493 theorems observed).
- Banned tokens (`native_decide`, `sorry`, `Prop := True`, `Classical`, custom `axiom`):
  NONE in code (only the honest-scope docstring names them as absent).

## Honest verdict

**Is the Jacobi modular transform built constructively over CReal?** No — only its **input
object** is. The ϑ₃ **series** `Σ_n q^{n²}` is now a genuine convergent `CReal` with a real
geometric modulus (step 1 done, axiom-clean, non-vacuous, `ϑ₃(q) ≥ 1`). The modular inversion
`ϑ₃(1/τ)=√τ·ϑ₃(τ)` (Poisson summation + theta-at-irrational-nome) is NOT built and is not
completable within the current `Q'`/`CReal` substrate this session.

**Does it close the M1/M2 uniform bounds / hlocalize?** No. They remain OPEN, exactly as
before — the transform is the single unbroken wall. The contribution is to **narrow** that
wall to precisely "the modular transform acting on the concrete `thetaS` object built here,"
removing the previous ambiguity about which theta object was meant.

**The Clay Yang–Mills mass gap remains OPEN.**
