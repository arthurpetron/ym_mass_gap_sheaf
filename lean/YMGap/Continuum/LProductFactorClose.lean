/-
# Closing `LProductFactor` : the product-factorisation half of the `Hdconv` reroute

`HdconvReroute.LProductFactor P` (over a `HdconvClose.ProdLimitConv fk dk x`) bundles
a coefficient CReal `A` together with the factorisation

    factor : CReal.Equiv P.L (Θ · A)          (Θ = thetaConvCRealGen …)

of the log-derivative limit through the shared differentiated-Jacobi product factor
`Θ`.  Discharging that residual — and thereby, via
`HdconvReroute.prodLimitIsRhalf_of_factor_coeff`, the identity half `ProdLimitIsRhalf`
— is what this module does, at the honest level the structure permits.

## Why `LProductFactor` is not closeable in isolation, and the sharp reduction

`LProductFactor` quantifies over a **generic** `P`, and `P.L` is an opaque structure
field of `ProdLimitConv`; `ProdLimitConv` is never constructed elsewhere in the tree.
So `LProductFactor` can only be produced **jointly** with a `ProdLimitConv` whose `L`
is in product form `c·(Θ·S')` (the log-derivative side: `c = ofQ'(−sin2θ)`, `S'` the
log-derivative sum `Σₖ 4q^{2k+1}/jFacₖ`).  This module isolates the ONE genuinely-open
datum — that product-form `ProdLimitConv` — as a named `Type`-level residual, and
proves everything downstream of it in small closed steps.

## What is GENUINELY closed here (new, axiom-clean content)

* **`regroup_factor` (CLOSED, fully generic)** — the pure `CReal` ring identity that
  moves the scalar `c` past the shared product factor `Θ`:

      c · (Θ · S')  ≈  Θ · (c · S').

  No limits or modulus — three `CRealAlg` regroupings (`cmul_assoc` twice, `cmul_comm`
  under `mul_congr_left`).  This is the exact mirror of
  `HdconvReroute.regroup_half_theta_S` for the log-derivative side.
* **`lProductFactorOfProductForm` (CLOSED reduction)** — from a `ProdLimitConv P` and
  a product-form identity `Equiv P.L (c·(Θ·S'))`, build `LProductFactor P` with
  coefficient `A = c·S'`, discharging the `factor` field by `hL.trans regroup_factor`.
  The shared `Θ` never becomes a separate obligation: it is common to both sides and
  the regroup moves the scalar past it.
* **`lProductFactorOfResidual` (CLOSED given the residual)** — packages the joint
  `ProdLimitConv`-plus-product-form datum (`ProductFormResidual`) and produces the
  `LProductFactor` for its `ProdLimitConv`.
* **`prodLimitIsRhalf_of_residual` (CLOSED capstone)** — from the product-form residual
  and the sibling coefficient identity `CoeffHalfIdentity (c·S')`, fire
  `HdconvReroute.prodLimitIsRhalf_of_factor_coeff` to conclude
  `HdconvClose.ProdLimitIsRhalf`.

## The honest residual ledger (AGENTS.md Rule 6 / Rule 8)

One `Type`-level residual, not faked:

* `ProductFormResidual … c S'` — a `HdconvClose.ProdLimitConv fk dk x` together with the
  product-form identity `Equiv P.L (c·(Θ·S'))`.  This carries the two genuinely-open
  pieces: (a) the log-derivative-sum CReal `S'` (only its rational convergence modulus,
  `ThetaDerivDriverClose.sigmaTail_le`, is in the tree); and (b) the CReal-level
  product-of-limits interchange `P_M·S_M → Θ·S'` that puts `prodDeriv`'s limit into
  product form (the `ProdLimitConv.conv` field; `ThetaDerivDriverClose.modulusOfResidual`
  yields only the rational-target `TsumDeriv.UnifDerivConvAt`, so a rational→CReal
  upgrade onto `L` is additionally required).  The coefficient `c = ofQ'(−sin2θ)` is
  likewise a parameter, since that specific driver coefficient CReal does not yet exist.

The remaining differentiated-Jacobi content is quarantined in the sibling residual
`HdconvReroute.CoeffHalfIdentity` (`c·S' ≈ ½·S`), which the reroute already isolates.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`, no
`sorry`, no custom axiom.  The residual is a named `Type`-level datum, never `sorry`.
-/

import YMGap.Continuum.HdconvReroute
import YMGap.Continuum.HdconvClose
import YMGap.Continuum.ThetaConvGen
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.LProductFactorClose

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. The pure `CReal` regroup: move the scalar `c` past the shared `Θ` -/

/-- **`regroup_factor` (CLOSED, fully generic).**  The pure `CReal` ring identity that
moves the scalar `c` past the shared product factor `Θ`:

    c · (Θ · S')  ≈  Θ · (c · S').

Three `CRealAlg` regroupings — `cmul_assoc` (reversed), `cmul_comm` under
`mul_congr_left`, then `cmul_assoc` — with no limit or modulus.  This is the mirror,
for the log-derivative side, of `HdconvReroute.regroup_half_theta_S`. -/
theorem regroup_factor (c Θ S' : CReal) :
    CReal.Equiv (CReal.mul c (CReal.mul Θ S'))
      (CReal.mul Θ (CReal.mul c S')) :=
  (CRealAlg.cmul_assoc c Θ S').symm.trans
    ((CReal.mul_congr_left (CRealAlg.cmul_comm c Θ)).trans
      (CRealAlg.cmul_assoc Θ c S'))

/-! ## 2. The reduction: a product-form `ProdLimitConv` ⟹ `LProductFactor` -/

/-- **`lProductFactorOfProductForm` (CLOSED reduction).**  From a `ProdLimitConv P` and
a product-form identity `hL : Equiv P.L (c·(Θ·S'))`, build the `LProductFactor P` with
coefficient `A = c·S'`.  The `factor` field `Equiv P.L (Θ·(c·S'))` is `hL` composed
with the regroup `regroup_factor`.  The shared `Θ` cancels here, never a separate
obligation. -/
def lProductFactorOfProductForm {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'}
    (P : HdconvClose.ProdLimitConv fk dk x)
    (c S' : CReal)
    (hL : CReal.Equiv P.L
      (CReal.mul c
        (CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1) S'))) :
    HdconvReroute.LProductFactor ha0 ha1 hx hx1 P where
  A := CReal.mul c S'
  factor :=
    hL.trans (regroup_factor c (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1) S')

/-! ## 3. The honest residual: a product-form `ProdLimitConv` -/

/-- **The product-form residual (named `Type`-level datum, NOT a theorem).**  A
`HdconvClose.ProdLimitConv fk dk x` together with the witness that its limit `L` is in
product form `c·(Θ·S')`.  This is the SOLE genuinely-open datum for `LProductFactor`:
it carries (a) the log-derivative-sum CReal `S'`, (b) the CReal-level product-of-limits
interchange (`P.conv`), and (c) the driver coefficient CReal `c = ofQ'(−sin2θ)`.  None
of these is faked; each is a parameter/field, never `sorry`. -/
structure ProductFormResidual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (fk : Nat → Q' → Q') (dk : Nat → Q') (c S' : CReal) : Type where
  /-- The genuine prod-limit convergence datum (carries the modulus / interchange). -/
  P : HdconvClose.ProdLimitConv fk dk x
  /-- The witness that `P.L` is in product form `c·(Θ·S')`. -/
  form : CReal.Equiv P.L
    (CReal.mul c
      (CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1) S'))

/-- **`lProductFactorOfResidual` (CLOSED given the residual).**  Produces the
`LProductFactor` for the residual's `ProdLimitConv`, with coefficient `A = c·S'`. -/
def lProductFactorOfResidual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'} {c S' : CReal}
    (R : ProductFormResidual ha0 ha1 hx hx1 fk dk c S') :
    HdconvReroute.LProductFactor ha0 ha1 hx hx1 R.P :=
  lProductFactorOfProductForm ha0 ha1 hx hx1 R.P c S' R.form

/-! ## 4. Capstone: `ProdLimitIsRhalf` from the product-form residual + `CoeffHalfIdentity` -/

/-- **`prodLimitIsRhalf_of_residual` (CLOSED capstone).**  From the product-form residual
`R` and the sibling coefficient identity `CoeffHalfIdentity (c·S')` (`c·S' ≈ ½·S`, the
isolated differentiated-Jacobi node), the shared `Θ` cancels and `½` regroups out —
via `HdconvReroute.prodLimitIsRhalf_of_factor_coeff` — proving
`HdconvClose.ProdLimitIsRhalf R.P`.  This is the reroute's identity half, delivered
modulo the two named residuals (`ProductFormResidual`, `CoeffHalfIdentity`). -/
theorem prodLimitIsRhalf_of_residual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'} {c S' : CReal}
    (R : ProductFormResidual ha0 ha1 hx hx1 fk dk c S')
    (hCoeff : HdconvReroute.CoeffHalfIdentity ha0 ha1 hx hx1 (CReal.mul c S')) :
    HdconvClose.ProdLimitIsRhalf ha0 ha1 hx hx1 R.P :=
  HdconvReroute.prodLimitIsRhalf_of_factor_coeff ha0 ha1 hx hx1 R.P
    (lProductFactorOfResidual ha0 ha1 hx hx1 R) hCoeff

end YMGap.Continuum.LProductFactorClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LProductFactorClose.regroup_factor
#print axioms YMGap.Continuum.LProductFactorClose.lProductFactorOfProductForm
#print axioms YMGap.Continuum.LProductFactorClose.lProductFactorOfResidual
#print axioms YMGap.Continuum.LProductFactorClose.prodLimitIsRhalf_of_residual
