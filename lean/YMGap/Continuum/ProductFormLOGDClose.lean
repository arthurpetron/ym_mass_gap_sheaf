/-
# Closing the FINITE half of the product-form residual split via `(LOGD)` (defeq)

`ProductFormResidualClose.productFormResidualOfFactor` reduces the whole
`LProductFactorClose.ProductFormResidual` to TWO named residuals over a
product-form family `gFam`:

* **(A)** `ProdLogDerivFactor fk dk x gFam` — the FINITE Leibniz log-derivative
  factorization `prodDeriv fk dk x M ≈ gFam M x` (a `Q'.eqv` identity per `M`), and
* **(B)** `UnifDerivConvC gFam (c·(Θ·S')) x` — the product-form family's
  explicit-modulus `CReal` convergence.

This module closes residual **(A)** genuinely and unconditionally for the Jacobi
heat-kernel instance, by a **definitional-equality** identification with the already
axiom-clean finite doubled-Leibniz identity `CoeffChebSineClose.logDeriv_factorProd`
(`(LOGD)`).  It then wires the conditional closure: given ANY (B), fire the closed
`ProductFormResidualClose` consumers to land `ProductFormResidual` and
`HdconvReroute.LProductFactor`.

## The defeq that makes the finite half free (verified against the recursions)

Instantiate
* `fk k t := HKPos.factor (HKPos.geoAmp a k) t`
* `dk k := HKPos.two (HKPos.geoAmp a k)`
* `gFam M t := RealTheta.factorProd a t M * HKConv.Spart a t M`

Then `FiniteProductFDDeriv.prodDeriv fk dk x M` is **definitionally equal** to
`CoeffChebSineClose.factorProdDx a x M`.  Both are structural `Nat`-recursions with
matching base and step:

* `prodDeriv (M+1) = prodDeriv M · fk M x + pre (fun k => fk k x) M · dk M`
  (`FiniteProductFDDeriv.prodDeriv`), vs
* `factorProdDx (M+1) = factorProdDx M · factor(geoAmp a M, x)
      + factorProd a x M · two(geoAmp a M)` (`CoeffChebSineClose.factorProdDx`);
* the new-factor slot `fk M x = factor(geoAmp a M, x)` and the derivative-constant
  slot `dk M = two(geoAmp a M)` match by β-reduction;
* the prefix product `pre (fun k => fk k x) M` (`DiffProduct.pre`, base `1`, step
  `_ · factor(geoAmp a k, x)`) is defeq to `RealTheta.factorProd a x M` (same base,
  same step).

Hence `ProdLogDerivFactor fk dk x gFam` (`∀ M, prodDeriv fk dk x M ≈ gFam M x`)
unfolds by defeq to `∀ M, factorProdDx a x M ≈ factorProd a x M · Spart a x M`,
which is **verbatim** `logDeriv_factorProd`.  So residual (A) is discharged by
`fun M => logDeriv_factorProd … M` — no analytic content, axiom-clean.

## The honest residual ledger (AGENTS.md Rule 6 / Rule 8)

Closing (A) does NOT close the R3 product-form obligation.  What remains is the
single open datum

* **(B)** `JacobiUnifConv` — the modulus-carrying `UnifDerivConvC` of the product
  family `factorProd·Spart` to `c·(Θ·S')`.

(B) is genuinely unbuilt: `UnifDerivConvC` is a stage-modulus-plus-ε-bound structure
(not a bare `CReal.Equiv`), and its target `c·(Θ·S')` forces `S ≈ c·S'` — the C¹
double-limit / sin-fold interchange leaf quarantined as
`CoeffChebSineClose.XCoeffResidual.interchange` (the identical leaf `DiffJTP` rests
on).  This module names (B) as a `Type`-level residual and never fakes it: the
conditional closures below consume a supplied `(B)`.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  (A) closes by defeq; (B) is named data.
-/

import YMGap.Continuum.ProductFormResidualClose
import YMGap.Continuum.CoeffChebSineClose

namespace YMGap.Continuum.ProductFormLOGDClose

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. The Jacobi instances of `fk`, `dk`, and the product-form family `gFam` -/

/-- The Jacobi heat-kernel factor family `fk k t = factor(a^{2k+1}, t)`. -/
def jacFk (a : Q') : Nat → Q' → Q' :=
  fun k t => HKPos.factor (HKPos.geoAmp a k) t

/-- The Jacobi new-factor derivative constants `dk k = 2·a^{2k+1} = two(geoAmp a k)`. -/
def jacDk (a : Q') : Nat → Q' :=
  fun k => HKPos.two (HKPos.geoAmp a k)

/-- The product-form family `gFam M t = factorProd a t M · Spart a t M` — the
partial product times the `S`-partial-sum, whose natural `CReal` limit is `Θ·S`. -/
def jacGFam (a : Q') : Nat → Q' → Q' :=
  fun M t => RealTheta.factorProd a t M * HKConv.Spart a t M

/-! ## 2. Residual (A), CLOSED unconditionally by matching the recursions to `(LOGD)`

The heart of the module.  The two structural `Nat`-recursions
`FiniteProductFDDeriv.prodDeriv (jacFk a) (jacDk a) x` and
`CoeffChebSineClose.factorProdDx a x` have base `0` and STEP FUNCTIONS that agree
up to β/defeq (`jacFk a M x = factor(geoAmp a M, x)`, `jacDk a M = two(geoAmp a M)`,
and `pre (fun k => jacFk a k x) M = factorProd a x M`).  The kernel does not reduce a
recursion at a symbolic `M`, so we prove the two `=`-identities by induction — each
successor case closing by `rfl` up to defeq — and transport `(LOGD)` across them. -/

/-- The prefix product of the Jacobi factor family equals the one-sided heat-kernel
product: `pre (fun k => jacFk a k x) M = RealTheta.factorProd a x M`.  Induction; each
successor case is `rfl` up to β (`jacFk a M x = factor(geoAmp a M, x)`). -/
theorem pre_eq_factorProd (a x : Q') :
    ∀ M, DiffProduct.pre (fun k => jacFk a k x) M = RealTheta.factorProd a x M
  | 0 => rfl
  | M + 1 => by
      rw [DiffProduct.pre_succ, RealTheta.factorProd_succ, pre_eq_factorProd a x M]
      rfl

/-- The Jacobi product-rule derivative value equals the heat-kernel formal
x-derivative: `prodDeriv (jacFk a) (jacDk a) x M = CoeffChebSineClose.factorProdDx a x M`.
Induction; each successor case rewrites by the IH and `pre_eq_factorProd`, then closes
by `rfl` up to β (`jacFk a M x`, `jacDk a M`). -/
theorem prodDeriv_eq_factorProdDx (a x : Q') :
    ∀ M, FiniteProductFDDeriv.prodDeriv (jacFk a) (jacDk a) x M
          = CoeffChebSineClose.factorProdDx a x M
  | 0 => rfl
  | M + 1 => by
      rw [FiniteProductFDDeriv.prodDeriv_succ, CoeffChebSineClose.factorProdDx_succ,
          prodDeriv_eq_factorProdDx a x M, pre_eq_factorProd a x M]
      rfl

/-- **`prodLogDerivFactor_jacobi` (residual (A), CLOSED).**  For the Jacobi instances
`jacFk`, `jacDk`, `jacGFam`, the finite log-derivative factorization holds — obtained
from `CoeffChebSineClose.logDeriv_factorProd` by transporting across the
`prodDeriv = factorProdDx` recursion identity (and `jacGFam a M x = factorProd a x M ·
Spart a x M` by defeq on the RHS).  This eliminates the FINITE half of the two-residual
split with NO analytic residual. -/
theorem prodLogDerivFactor_jacobi {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) :
    ProductFormResidualClose.ProdLogDerivFactor (jacFk a) (jacDk a) x (jacGFam a) :=
  fun M => by
    rw [prodDeriv_eq_factorProdDx a x M]
    exact CoeffChebSineClose.logDeriv_factorProd ha0 ha1 hx M

/-! ## 3. Residual (B): the single remaining open datum, named as `Type`-level data

The product-form family's explicit-modulus `CReal` convergence to `c·(Θ·S')`.  This
is NOT product-of-limits: it is the modulus-carrying `UnifDerivConvC` whose target
value forces `S ≈ c·S'` — the C¹ double-limit interchange / sin-fold leaf.  Named
here (never `sorry`); the conditional closures below CONSUME it. -/

/-- **Residual (B) — the Jacobi product-form convergence (named `Type`, NOT
discharged).**  The `UnifDerivConvC` of `gFam = factorProd·Spart` to `c·(Θ·S')` at
`x`, with explicit stage modulus.  This carries the genuine analytic (differentiated
Jacobi / double-limit interchange) content of the product-form obligation. -/
def JacobiUnifConv {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (c S' : CReal) : Type :=
  ThetaSeriesFDDeriv.UnifDerivConvC (jacGFam a)
    (CReal.mul c
      (CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1) S')) x

/-! ## 4. Conditional closures: fire the closed consumers off (A) + a supplied (B) -/

/-- **`productFormResidual_jacobi` (CONDITIONAL on (B)).**  With residual (A) closed
by `prodLogDerivFactor_jacobi` and ANY (B) `hconv : JacobiUnifConv`, the closed
reduction `ProductFormResidualClose.productFormResidualOfFactor` assembles the whole
`LProductFactorClose.ProductFormResidual` for the Jacobi `jacFk`/`jacDk`.  The finite
half is FREE; the sole consumed datum is (B). -/
def productFormResidual_jacobi {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (c S' : CReal)
    (hconv : JacobiUnifConv ha0 ha1 hx hx1 c S') :
    LProductFactorClose.ProductFormResidual ha0 ha1 hx hx1 (jacFk a) (jacDk a) c S' :=
  ProductFormResidualClose.productFormResidualOfFactor ha0 ha1 hx hx1 c S'
    (jacGFam a) (prodLogDerivFactor_jacobi ha0 ha1 hx) hconv

/-- **`lProductFactor_jacobi` (CONDITIONAL on (B)).**  Downstream: from (A)+(B) fire
the closed `ProductFormResidualClose.lProductFactorOfFactor` to obtain the
`HdconvReroute.LProductFactor` for the assembled `ProdLimitConv`.  Again the FINITE
half is free; the analytic burden is exactly the supplied (B). -/
def lProductFactor_jacobi {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (c S' : CReal)
    (hconv : JacobiUnifConv ha0 ha1 hx hx1 c S') :
    HdconvReroute.LProductFactor ha0 ha1 hx hx1
      (ProductFormResidualClose.productFormResidualOfFactor ha0 ha1 hx hx1 c S'
        (jacGFam a) (prodLogDerivFactor_jacobi ha0 ha1 hx) hconv).P :=
  ProductFormResidualClose.lProductFactorOfFactor ha0 ha1 hx hx1
    (jacGFam a) (prodLogDerivFactor_jacobi ha0 ha1 hx) hconv

end YMGap.Continuum.ProductFormLOGDClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ProductFormLOGDClose.prodLogDerivFactor_jacobi
#print axioms YMGap.Continuum.ProductFormLOGDClose.productFormResidual_jacobi
#print axioms YMGap.Continuum.ProductFormLOGDClose.lProductFactor_jacobi
