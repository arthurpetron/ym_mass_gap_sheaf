/-
# Closing the `form` field of `ProductFormResidual`, and the sharp two-residual split of `P.conv`

`LProductFactorClose.ProductFormResidual` has TWO fields:

* `P    : HdconvClose.ProdLimitConv fk dk x`   (whose `L : CReal` is a *free* field), and
* `form : CReal.Equiv P.L (c·(Θ·S'))`.

The key structural observation — verified directly against the definitions — is that
`ProdLimitConv.L` is a free structure field: nothing forces it to be anything, so we are
free to **define** `P.L := c·(Θ·S')`.  With that choice the `form` field is
`CReal.Equiv (c·(Θ·S')) (c·(Θ·S'))`, i.e. reflexivity — it carries **no** analytic
content.  This corrects the two module ledgers (`LProductFactorClose`, `HdconvReroute`)
that treat `form`/the product-Equiv as an open obligation: once `L` is *defined as* the
product, `form` collapses to `refl` and every genuine datum of `ProductFormResidual` lives
in the single field `P.conv`.

## What is GENUINELY closed here (new, axiom-clean content)

* **`equivRefl` (CLOSED)** — `CReal.Equiv A A`, via `SumOfSquares.Equiv_of_approx_eqv`.
  The `refl` that discharges `form`.

* **`ofQ'_equiv_of_eqv` (CLOSED)** — a rational identity `a ≈ b` lifts to
  `CReal.Equiv (ofQ' a) (ofQ' b)` (both approximation sequences are constant).

* **`unifDerivConvC_congr_family` (CLOSED, the family-side engine)** — the mirror of
  `HdconvClose.unifDerivConvC_congr_limit`, but transporting across an identity of the
  *rational family* rather than the *CReal limit*: a `UnifDerivConvC g L θ` and a
  termwise identity `∀ M, f M θ ≈ g M θ` produce `UnifDerivConvC f L θ`, with the SAME
  stage modulus `Mg`.  The bound is carried over by
  `leRat_of_equiv ∘ abs_equiv_congr ∘ add_congr_right ∘ neg_congr ∘ ofQ'_equiv_of_eqv`.

* **`productFormResidualOfConv` (CLOSED, headline)** — from ANY explicit-modulus
  convergence `UnifDerivConvC (prodDeriv fk dk ·) (c·(Θ·S')) x` build the whole
  `ProductFormResidual`, discharging `form` by `equivRefl`.  This is the proof that
  `ProductFormResidual` collapses onto its single `conv` datum.

* **`productFormResidualOfFactor` (CLOSED reduction, the sharp split)** — reduces
  `ProductFormResidual` to TWO named residuals over a product-form family `gFam`:
  (A) the finite Leibniz factorization `ProdLogDerivFactor` (`prodDeriv ≈ gFam` termwise),
  and (B) the product-form family's CReal convergence `UnifDerivConvC gFam (c·(Θ·S')) x`.
  The glue (family transport + `form = refl`) is fully proved here.

## The honest residual ledger (AGENTS.md Rule 6 / Rule 8)

`ProductFormResidual` is reduced to exactly two named data, neither faked:

* `ProdLogDerivFactor fk dk x gFam` — the finite log-derivative factorization
  `prodDeriv fk dk x M ≈ gFam M x` (a `Q'.eqv` identity for each `M`; the single
  genuinely-open *finite* datum, provable by Leibniz induction with `jFac`-positive
  divisions).  It is a `Prop`-level identity (an equation, not choice data), so Rule 8
  does not require Type-level packaging.
* `UnifDerivConvC gFam (c·(Θ·S')) x` — the product-form family's explicit-modulus CReal
  convergence (Type-level data, the geometric-tail modulus of `Θ` and `S'` composed).

The coefficient `c` and the log-derivative sum `S'` remain parameters (the specific
driver CReals), exactly as in `LProductFactorClose`.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`, no
`sorry`, no custom axiom.  The residuals are named data, never `sorry`.
-/

import YMGap.Continuum.LProductFactorClose
import YMGap.Continuum.ThetaSeriesFDDeriv
import YMGap.Continuum.FiniteProductFDDeriv
import YMGap.Continuum.ThetaConvGen
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.ProductFormResidualClose

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. Two closed CReal helpers: reflexivity and the `ofQ'` congruence -/

/-- **`equivRefl` (CLOSED).**  `CReal.Equiv A A`, built from the termwise-`eqv`
constructor with the reflexive rational identity at every approximation index.  This is
the `refl` that discharges the `form` field once `L` is defined *as* the product. -/
theorem equivRefl (A : CReal) : CReal.Equiv A A :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_refl (A.approx n))

/-- **`ofQ'_equiv_of_eqv` (CLOSED).**  A rational identity `a ≈ b` lifts to a CReal
identity `Equiv (ofQ' a) (ofQ' b)`; both `ofQ'` approximation sequences are the
respective constants, so the termwise obligation is `a ≈ b` verbatim. -/
theorem ofQ'_equiv_of_eqv {a b : Q'} (h : Q'.eqv a b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => h)

/-! ## 2. The family-side transport engine (mirror of `unifDerivConvC_congr_limit`) -/

/-- **THE FAMILY-SIDE ENGINE (fully generic, CLOSED).**  A rational family `g` that
converges (with explicit stage modulus `Mg`) to a CReal limit `L` at `θ`, together with a
termwise identity `∀ M, f M θ ≈ g M θ`, yields a `UnifDerivConvC f L θ` — with the SAME
modulus `Mg`.

The transported convergence bound comes from the identity transfer:
`|L ⊖ ofQ'(f M θ)| ≃ |L ⊖ ofQ'(g M θ)|` (via
`abs_equiv_congr ∘ add_congr_right ∘ neg_congr ∘ ofQ'_equiv_of_eqv` on the termwise
identity), so `leRat_of_equiv` carries each `ε`-bound over verbatim.  No new modulus is
created.  This is the family-side counterpart of `HdconvClose.unifDerivConvC_congr_limit`
(which transports across a *limit* identity instead). -/
def unifDerivConvC_congr_family
    {f g : Nat → Q' → Q'} {L : CReal} {θ : Q'}
    (h : ThetaSeriesFDDeriv.UnifDerivConvC g L θ)
    (hfam : ∀ M : Nat, Q'.eqv (f M θ) (g M θ)) :
    ThetaSeriesFDDeriv.UnifDerivConvC f L θ where
  Mg := h.Mg
  conv := fun ε hε M hM =>
    CReal.leRat_of_equiv
      (CReal.abs_equiv_congr
        (CReal.add_congr_right
          (y := CReal.neg (CReal.ofQ' (f M θ)))
          (y' := CReal.neg (CReal.ofQ' (g M θ)))
          (CReal.neg_congr (ofQ'_equiv_of_eqv (hfam M)))))
      (h.conv ε hε M hM)

/-! ## 3. The headline: `ProductFormResidual` from a single product-form convergence -/

/-- **`productFormResidualOfConv` (CLOSED, headline).**  From ANY explicit-modulus
convergence `conv : UnifDerivConvC (prodDeriv fk dk ·) (c·(Θ·S')) x`, assemble the whole
`ProductFormResidual`: choose `P.L := c·(Θ·S')` and `P.conv := conv`, whereupon the
`form` field is `CReal.Equiv (c·(Θ·S')) (c·(Θ·S'))` and is discharged by `equivRefl`.
The `form`/product-Equiv obligation therefore carries no analytic content: the entire
genuine datum of `ProductFormResidual` is the single `conv`. -/
def productFormResidualOfConv {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'} (c S' : CReal)
    (conv : ThetaSeriesFDDeriv.UnifDerivConvC
              (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
              (CReal.mul c
                (CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1) S')) x) :
    LProductFactorClose.ProductFormResidual ha0 ha1 hx hx1 fk dk c S' where
  P :=
    { L := CReal.mul c
             (CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1) S')
      conv := conv }
  form := equivRefl _

/-! ## 4. The sharp split: two named residuals over a product-form family -/

/-- **The finite log-derivative factorization (named `Prop`-level residual).**  The single
genuinely-open FINITE datum: for each cutoff `M`, the Leibniz product-rule value
`prodDeriv fk dk x M` equals the product-form partial `gFam M x` (as a `Q'.eqv` identity).
For the Jacobi instance `gFam M t = (−s)·Ppart_M·S'partial_M`, this is the logarithmic
derivative factorization `prodDeriv = (∏ fk)·Σ (dk/fk)` with `dk/fk = −s·τ`, proved by
Leibniz induction with `jFac`-positive divisions.  It is an equation, not choice data, so
Rule 8 admits the `Prop` packaging. -/
def ProdLogDerivFactor (fk : Nat → Q' → Q') (dk : Nat → Q') (x : Q')
    (gFam : Nat → Q' → Q') : Prop :=
  ∀ M : Nat, Q'.eqv (FiniteProductFDDeriv.prodDeriv fk dk x M) (gFam M x)

/-- **`productFormResidualOfFactor` (CLOSED reduction, the sharp split).**  Reduces
`ProductFormResidual` to two named residuals over a product-form family `gFam`:

* `hfac : ProdLogDerivFactor fk dk x gFam` — the finite Leibniz factorization, and
* `hconv : UnifDerivConvC gFam (c·(Θ·S')) x` — the product-form family's CReal convergence.

The finite identity transports the family's convergence onto `prodDeriv` via the engine
`unifDerivConvC_congr_family`, and `productFormResidualOfConv` then packages it with the
`refl` `form`.  Both consumed data are strictly sharper than the original `conv`: the
analytic (modulus) burden is quarantined in `hconv`, the finite algebra in `hfac`. -/
def productFormResidualOfFactor {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'} (c S' : CReal)
    (gFam : Nat → Q' → Q')
    (hfac : ProdLogDerivFactor fk dk x gFam)
    (hconv : ThetaSeriesFDDeriv.UnifDerivConvC gFam
              (CReal.mul c
                (CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1) S')) x) :
    LProductFactorClose.ProductFormResidual ha0 ha1 hx hx1 fk dk c S' :=
  productFormResidualOfConv ha0 ha1 hx hx1 c S'
    (unifDerivConvC_congr_family
      (f := fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
      hconv (fun M => hfac M))

/-! ## 5. Downstream: fire the closed `LProductFactorClose` consumers off the split -/

/-- **`lProductFactorOfFactor` (CLOSED).**  From the two-residual split, produce the
`HdconvReroute.LProductFactor` for the assembled `ProdLimitConv` — the already-closed
`LProductFactorClose.lProductFactorOfResidual` fired on `productFormResidualOfFactor`. -/
def lProductFactorOfFactor {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'} {c S' : CReal}
    (gFam : Nat → Q' → Q')
    (hfac : ProdLogDerivFactor fk dk x gFam)
    (hconv : ThetaSeriesFDDeriv.UnifDerivConvC gFam
              (CReal.mul c
                (CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1) S')) x) :
    HdconvReroute.LProductFactor ha0 ha1 hx hx1
      (productFormResidualOfFactor ha0 ha1 hx hx1 c S' gFam hfac hconv).P :=
  LProductFactorClose.lProductFactorOfResidual ha0 ha1 hx hx1
    (productFormResidualOfFactor ha0 ha1 hx hx1 c S' gFam hfac hconv)

end YMGap.Continuum.ProductFormResidualClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ProductFormResidualClose.equivRefl
#print axioms YMGap.Continuum.ProductFormResidualClose.ofQ'_equiv_of_eqv
#print axioms YMGap.Continuum.ProductFormResidualClose.unifDerivConvC_congr_family
#print axioms YMGap.Continuum.ProductFormResidualClose.productFormResidualOfConv
#print axioms YMGap.Continuum.ProductFormResidualClose.productFormResidualOfFactor
#print axioms YMGap.Continuum.ProductFormResidualClose.lProductFactorOfFactor
