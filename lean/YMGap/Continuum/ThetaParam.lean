/-
# The theta parametrisation match (Wall-2, Route A): honest status of the
  series↔product common-`F` identification over `Q'`

This module records — precisely and honestly — how the finite Gauss q-binomial
identity (`GaussQBinom.gauss_qbinom_all`) relates to the CONCRETE real theta
product carried by `ThetaConvGen.Ppart` / `thetaConvCRealGen`, and what the genuine
residual is for making the SERIES side and PRODUCT side differentiate the SAME
limit function `F = ϑ₃` over the project's REAL rationals `Q'`.

## The exact correspondence (verified, sympy/mpmath; see `docs/jtp-convergence-notes.md`)

With `z = e^{iθ}`, `x = cos θ = (z + z⁻¹)/2`, the per-factor identity is

    HKPos.factor c x  =  1 + 2c·x + c²  =  (1 + c·z)(1 + c·z⁻¹).            (FAC)

So the repo's real theta partial product (the `approx N` of `thetaConvCRealGen`),
dropping the `(1 − a^{2k+1})` prefactors carried in `Ppart`'s `gFac`, is the
TWO-SIDED Gauss product

    ∏_{k<L} HKPos.factor (a^{2k+1}) x  =  qProd z a L · qProd z⁻¹ a L           (B1)

(`GaussQBinom.qProd` is the ONE-sided product `∏(1 + z·q^{2j−1})`; (B1) is the
product of the `z` and `z⁻¹` instances).  Applying the finite Gauss identity (G)
`qProd = gaussSum` to EACH one-sided factor turns (B1) into a product of two finite
Gaussian sums, whose `L → ∞` limit (times `∏(1 − a^{2j})`) is `ϑ₃` — the series side.

## The honest residual (AGENTS.md Rule 6): WHY a single `gauss_qbinom_creal_equiv`
   does NOT close the match over `Q'`

`ThetaLimit.gauss_qbinom_creal_equiv` lifts a SINGLE finite identity
`qProd z q N ≈ gaussSum z q N` to a `CReal.Equiv` of two reals whose `approx N` are
EXACTLY `qProd z q N` and `gaussSum z q N`.  But:

* the repo's product side `thetaConvCRealGen` has `approx N = Ppart a x N`, which is
  the TWO-SIDED real product `∏(1−a^{2k+1})·(1 + 2a^{2k+1}x + a^{4k+2})`, NOT a
  single one-sided `qProd z a N`;
* a single one-sided `qProd z a N` requires `z = e^{iθ}` COMPLEX, which does not
  live over the real substrate `Q'`;
* the genuine real per-`N` identity is the DIAGONAL of (B1)·(prefactor) — a product
  of two Gaussian sums collapsing to `1 + 2Σ_{n≤N} a^{n²}cos nθ` — which is NOT a
  single `qProd ≈ gaussSum` instance and so is not in the image of
  `gauss_qbinom_creal_equiv` as currently stated.

Therefore the clean single-substitution `(z, q)` parametrisation the route hoped
for is BLOCKED by the complex-vs-real / two-sided structure of the real theta
factor.  This module does NOT fake that match.  Instead it provides the genuine,
reusable REAL bridge `theta_common_F_of_approx_equal` (uniqueness of limits applied
to the real partials) and names the residual sharply as `RealThetaPerN`: the
per-`N` REAL identity `Ppart-series-partial ≈ Ppart-product-partial` that the
two-sided Gauss collapse would supply.  Supplying `RealThetaPerN` yields the
common-`F` `CReal.Equiv` the Route-A derivative-uniqueness assembly needs.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `native_decide`, no
`sorry`.  `RealThetaPerN` is a named `Type`-obligation (the sharp residual), NOT a
`sorry`.
-/

import YMGap.Constructive.CRealAbs
import YMGap.Continuum.ThetaLimit

namespace YMGap.Continuum.ThetaParam

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The reusable REAL bridge: common-`F` from per-`N` real equality

If two `CReal`s `Pser`, `Pprod` have `Equiv`-equal approximation sequences term by
term, their limits coincide.  This is the `CRealAbs` limit-of-equal-sequences engine
specialised through `Equiv_of_lifted_approx_equal`; it is what any concrete per-`N`
REAL theta identity feeds to obtain the common limit function `F = ϑ₃`. -/

/-- **The real common-`F` bridge.**  Given two `CReal`s whose `N`-th approximations
are `Q'.eqv`-equal for every `N` (`Pser.approx N ≈ Pprod.approx N`), their limits are
`CReal.Equiv`.  This is the genuine engine that turns a per-`N` REAL theta identity
(the diagonal collapse of the two-sided Gauss product) into the common limit `ϑ₃`
that the SERIES and PRODUCT finite-difference families must share for Route-A
derivative uniqueness.  Reusable, axiom-clean. -/
theorem theta_common_F_of_approx_equal {Pser Pprod : CReal}
    (hN : ∀ N : Nat, Pser.approx N ≈ Pprod.approx N) :
    CReal.Equiv Pser Pprod :=
  CReal.Equiv_of_lifted_approx_equal
    (fun N => ThetaLimit.Equiv_ofQ'_of_eqv (hN N))

/-! ## 2. The sharp residual `RealThetaPerN` (named, NOT discharged)

The remaining input is the per-`N` REAL theta identity equating the series-partial
and the product-partial (the real diagonal of the two-sided Gauss collapse).  We
name it as a `Type`-obligation carrying exactly the per-`N` `Q'.eqv` data; supplying
it yields the common limit via `theta_common_F_of_approx_equal`. -/

/-- **The per-`N` REAL theta identity (named residual).**  Carries, for two `CReal`
realisations `Pser` (theta-SERIES partials) and `Pprod` (theta-PRODUCT partials,
e.g. `thetaConvCRealGen`), the per-`N` REAL equality of their approximations.  This
is the diagonal collapse of the two-sided Gauss product (B1) — the genuine real
content that `gauss_qbinom_creal_equiv` cannot supply directly because the real
theta factor is two-sided / complex.  NOT discharged here. -/
structure RealThetaPerN (Pser Pprod : CReal) : Type where
  /-- The per-`N` real equality `Pser.approx N ≈ Pprod.approx N`. -/
  perN : ∀ N : Nat, Pser.approx N ≈ Pprod.approx N

/-- **`RealThetaPerN → CReal.Equiv`** (the common limit function `F = ϑ₃`).  Supplying
the per-`N` real theta identity yields the shared limit the Route-A
derivative-uniqueness assembly requires for its common-`F` field. -/
theorem common_F_of_realThetaPerN {Pser Pprod : CReal}
    (H : RealThetaPerN Pser Pprod) : CReal.Equiv Pser Pprod :=
  theta_common_F_of_approx_equal H.perN

end YMGap.Continuum.ThetaParam

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaParam.theta_common_F_of_approx_equal
#print axioms YMGap.Continuum.ThetaParam.common_F_of_realThetaPerN
