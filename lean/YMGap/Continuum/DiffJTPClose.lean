/-
# The `diffJTPClose` wiring: firing `DiffJTP` / `K_t ≥ 0` from the two C¹ inputs

This module lands the **wiring** capstone of Wall 2, Route A.  Everything analytic
downstream is already proved and green:

* the **firing capstone** `DiffJTPAssembly.diffJTPAssembly` /
  `diffJTP_of_assembly` / `Kt_geRat_zero_of_assembly`, which consumes EXACTLY the
  two common-`F` finite-difference derivatives
  `Dprod : FDDerivDataC F (Rhalf …) x` and `Dser : FDDerivDataC F (dSeriesCReal …) x`;
* the **series-side producer** `ThetaSeriesFDDeriv.thetaSeriesFDDeriv`, the CLOSED
  CReal C¹-uniform-limit engine that turns the theta series C¹ inputs
  `ThetaSeriesC1Inputs = C1InputsC (chebTTrunc a) (dPartialFam a) F (dSeriesCReal) x`
  into `Dser`;
* the **product-side producer** `ThetaC1LimitEngine.fdDerivDataC_of_unif_M`, the
  CLOSED CReal-truncation C¹-limit engine that turns a product-side C¹ inputs
  bundle `C1InputsC prodTrunc F prodDeriv (Rhalf) x` into `Dprod`;
* the **per-factor producer** `JacobiFactorFDDeriv.jacobiFactorFDDeriv`, which turns
  the per-factor quadratic residual `JacobiQuadResidual` into the CReal per-factor
  `FDDerivDataC (Fk) (dk) θ`.

## What this module DELIVERS green

`Wall2Round2Residuals` bundles the ENTIRE remaining Wall-2 input over ONE common
limit `F = ϑ₃` at the working point `x`:

* `series` — the series-side C¹ inputs (the honest `ptθ`/`fdbound`/`unif` fields,
  named `Type`-level data);
* `prodTrunc` / `prodDeriv` / `prod` — the product-side truncation family, its
  derivative values, and the product-side C¹ inputs (the honest `conv`/`dconv`/
  `fdboundC` fields, named `Type`-level data).

Given the bundle, `Dser_of` / `Dprod_of` fire the two CLOSED engines to produce the
two witnesses over the SAME `F`, and `diffJTPClose` / `diffJTP_of_round2` produce
`K_t ≥ 0` and `DiffJTP` with NO further analysis.  This is a pure wiring theorem:
the two named residuals `series` and `prod` are the sole outstanding analytic input.

`jacobiFactors_of` additionally lands the per-factor sub-reduction of the product
side as a genuine producer: the family `JacobiQuadResidual (∀k)` (which reduces to
the PROVED `TrigBound.cos_second_diff_abs_le`) maps to the CReal per-factor
`FDDerivDataC` family through the CLOSED `jacobiFactorFDDeriv`.

## The honest residual (AGENTS.md Rule 6)

Nothing here is faked.  The whole wall now reduces to the two named `Type`-level
fields of `Wall2Round2Residuals`:

* `series : ThetaSeriesFDDeriv.ThetaSeriesC1Inputs …` — the series-side C¹ inputs;
* `prod   : ThetaC1LimitEngine.C1InputsC …`         — the product-side C¹ inputs.

Both are consumed by CLOSED engines; both are named `Type`-obligations, NOT `sorry`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.DiffJTPAssembly
import YMGap.Continuum.ThetaSeriesFDDeriv
import YMGap.Continuum.ThetaC1LimitEngine
import YMGap.Continuum.JacobiFactorFDDeriv
import YMGap.Continuum.JTPIdentity
import YMGap.Continuum.TsumDeriv
import YMGap.Constructive.Reals

namespace YMGap.Continuum.DiffJTPClose

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. The bundled round-2 residuals over one common `F` at `θ₀ = x` -/

/-- **The entire remaining Wall-2 input, as one named `Type`.**  Over a single common
limit `F = ϑ₃` (as a `CReal`-valued function of the rational differentiation
variable) at the working point `x`, this bundles both C¹-input residuals:

* `series` — the series-side C¹ inputs (`ThetaSeriesC1Inputs`), consumed by the
  CLOSED series producer `thetaSeriesFDDeriv`;
* `prodTrunc`, `prodDeriv`, `prod` — the product-side truncation family, its
  derivative values, and the product-side C¹ inputs (`ThetaC1LimitEngine.C1InputsC`
  at `dlim = Rhalf`), consumed by the CLOSED product producer `fdDerivDataC_of_unif_M`.

Inhabit it and `K_t ≥ 0` (and `DiffJTP`) follow with no further analysis. -/
structure Wall2Round2Residuals {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Type where
  /-- The common limit function `F = ϑ₃`, as a `CReal`-valued function of the
  rational differentiation variable.  BOTH sides differentiate this same `F`. -/
  F : Q' → CReal
  /-- The series-side C¹ inputs: the finite Chebyshev-`T` truncations
  `chebTTrunc a` converging to `F`, with termwise derivatives `dPartial a`
  converging to `dSeriesCReal`.  (Honest named residual: `ptθ`/`fdbound`/`unif`.) -/
  series : ThetaSeriesFDDeriv.ThetaSeriesC1Inputs ha0 ha1 hx hx1 F
  /-- The product-side CReal truncation family `∏_{k<M} (Jacobi factor)`. -/
  prodTrunc : Nat → Q' → CReal
  /-- The product-side truncation derivative values. -/
  prodDeriv : Nat → CReal
  /-- The product-side C¹ inputs at `dlim = Rhalf`: pointwise convergence
  `prodTrunc → F`, derivative convergence `prodDeriv → Rhalf`, and the uniform-in-`M`
  finite-difference modulus.  (Honest named residual: `conv`/`dconv`/`fdboundC`.) -/
  prod : ThetaC1LimitEngine.C1InputsC prodTrunc F prodDeriv
    (JTPIdentity.Rhalf ha0 ha1 hx hx1) x

/-! ## 2. The two producers (both CLOSED engines) -/

/-- **The series-side witness.**  Fire the CLOSED CReal C¹-uniform-limit engine on
the series-side C¹ inputs: `Dser : FDDerivDataC F (dSeriesCReal) x`. -/
def Dser_of {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2Round2Residuals ha0 ha1 hx hx1) :
    TsumDeriv.FDDerivDataC W.F (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) x :=
  ThetaSeriesFDDeriv.thetaSeriesFDDeriv ha0 ha1 hx hx1 W.F W.series

/-- **The product-side witness.**  Fire the CLOSED CReal-truncation C¹-limit engine
on the product-side C¹ inputs: `Dprod : FDDerivDataC F (Rhalf) x`. -/
def Dprod_of {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2Round2Residuals ha0 ha1 hx hx1) :
    TsumDeriv.FDDerivDataC W.F (JTPIdentity.Rhalf ha0 ha1 hx hx1) x :=
  ThetaC1LimitEngine.fdDerivDataC_of_unif_M W.prod

/-! ## 3. The firing (pure wiring; everything downstream is proved) -/

/-- **`diffJTPClose` — `K_t ≥ 0` from the round-2 residuals.**  With both witnesses
over the SAME common `F` at `x`, the firing capstone produces
`K_t = dSeriesCReal ≥ 0` unconditionally on the two named residuals `series`/`prod`. -/
theorem diffJTPClose {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2Round2Residuals ha0 ha1 hx hx1) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  DiffJTPAssembly.Kt_geRat_zero_of_assembly ha0 ha1 hx hx1
    W.F x (Dprod_of ha0 ha1 hx hx1 W) (Dser_of ha0 ha1 hx hx1 W)

/-- **`diffJTP_of_round2` — the differentiated Jacobi-triple-product identity.**  The
`DiffJTP` residual `dSeriesCReal ≈ Rhalf` itself, from the same two witnesses. -/
theorem diffJTP_of_round2 {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2Round2Residuals ha0 ha1 hx hx1) :
    JTPIdentity.DiffJTP ha0 ha1 hx hx1 :=
  DiffJTPAssembly.diffJTP_of_assembly ha0 ha1 hx hx1
    W.F x (Dprod_of ha0 ha1 hx hx1 W) (Dser_of ha0 ha1 hx hx1 W)

/-! ## 4. The per-factor sub-reduction of the product side (a genuine producer)

The product-side C¹ inputs `prod` are fed, in the intended construction, by the
per-factor Jacobi derivatives assembled through a finite-product rule.  Each factor's
CReal finite-difference derivative is produced — CLOSED — from its per-factor
quadratic residual `JacobiQuadResidual` (which itself reduces to the PROVED
`TrigBound.cos_second_diff_abs_le`).  We land that map as a genuine producer of the
per-factor `FDDerivDataC` family. -/

/-- **The per-factor `FDDerivDataC` family.**  From the per-factor quadratic residuals
`JacobiQuadResidual q k θ` for every `k`, the CReal `θ`-lifts `Fk q k` of the Jacobi
factors carry finite-difference derivatives `dk q k θ` at `θ`, via the CLOSED
`jacobiFactorFDDeriv`.  This is the per-factor input to the finite-product rule that
assembles the product-side truncations `prodTrunc`. -/
def jacobiFactors_of {q : Q'} (θ : Q')
    (res : ∀ k, JacobiFactorFDDeriv.JacobiQuadResidual q k θ) :
    ∀ k, TsumDeriv.FDDerivDataC
      (JacobiFactorFDDeriv.Fk q k) (JacobiFactorFDDeriv.dk q k θ) θ :=
  fun k => JacobiFactorFDDeriv.jacobiFactorFDDeriv k θ (res k)

end YMGap.Continuum.DiffJTPClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`Int`/`omega` helpers).  No `Classical.*`, no
`native_decide`, no `sorry`.  `Wall2Round2Residuals` (its `series`/`prod` fields),
`ThetaSeriesFDDeriv.ThetaSeriesC1Inputs`, `ThetaC1LimitEngine.C1InputsC`, and
`JacobiFactorFDDeriv.JacobiQuadResidual` are named `Type`-obligations (the outstanding
analytic inputs), NOT `sorry`. -/

#print axioms YMGap.Continuum.DiffJTPClose.Dser_of
#print axioms YMGap.Continuum.DiffJTPClose.Dprod_of
#print axioms YMGap.Continuum.DiffJTPClose.diffJTPClose
#print axioms YMGap.Continuum.DiffJTPClose.diffJTP_of_round2
#print axioms YMGap.Continuum.DiffJTPClose.jacobiFactors_of
