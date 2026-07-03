/-
# Splitting `Hdconv` : the buildable convergence half + the irreducible identity half

`Hdconv` is the CReal-target derivative-value convergence

    Hdconv : ThetaSeriesFDDeriv.UnifDerivConvC
               (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
               (JTPIdentity.Rhalf …) x

demanded by `ThetaProdDprodClose.prodC1Inputs`.  Unfolding `UnifDerivConvC`, it is
a stage modulus `Mg` together with the CReal convergence

    ofQ'(prodDeriv fk dk x M) → Rhalf     (with explicit modulus `Mg`).

## Why `Hdconv` is not product-of-limits, and the honest split

`Rhalf = (½)·Θ·S` is a **static** CReal (`JTPIdentity.Rhalf`; `Θ = thetaConvCRealGen`,
`S = sConvCReal_general`) — it carries no `prodDeriv`, no `sin`, no `fk/dk`.  Bare
product-of-limits lands `ofQ'(prodDeriv fk dk x M)` on a DIFFERENT CReal
`L = Θ·Σσ = (−sin2θ)·Θ·S'` (the log-derivative sum `S' = Σₖ 4q^{2k+1}/jFacₖ`, not
`S`).  Closing `Hdconv` therefore bundles TWO things that this module peels apart:

1. **The convergence half** (`ProdLimitConv`): a genuine prod-limit CReal `L` with an
   explicit-modulus datum `ofQ'(prodDeriv fk dk x M) → L`.  This is the
   `UnifDerivConvC (prodDeriv …) L x` assembled from the in-tree Pₘ→Θ product limit
   (`ThetaLimit`/`ThetaConvGen`), the log-derivative tail (`sigmaTail_le`), and
   `CReal.mul` continuity.  It carries the entire modulus / uniformity burden.

2. **The identity half** (`ProdLimitIsRhalf`): the ONE pure algebraic CReal equation

       CReal.Equiv L (JTPIdentity.Rhalf …)     ≡   (−sin2θ)·Θ·S' ≈ (½)·Θ·S,

   with NO remaining limits or modulus.  This is the isolated differentiated-Jacobi
   node — strictly sharper than `Hdconv` / `JTPIdentity.DiffJTP`, which additionally
   bundle the convergence and the uniformity.

## What is GENUINELY closed here

* **`unifDerivConvC_congr_limit` (CLOSED)** — THE engine lemma, fully generic: a
  `UnifDerivConvC f' L θ` and a limit-identity `Equiv L L'` produce
  `UnifDerivConvC f' L' θ`, with the SAME stage modulus `Mg`.  The convergence bound
  is transported across the identity by the reverse-triangle `leRat` transfer
  (`abs_equiv_congr` ∘ `add_congr_left` ∘ `Equiv.symm`, then `leRat_of_equiv`).  No
  new modulus is created — this is the honest statement that "peeling off the
  identity keeps the modulus intact".

* **`hdconvOfSplit` (CLOSED given the two named residuals)** — assembles `Hdconv`
  itself from `ProdLimitConv` + `ProdLimitIsRhalf` via the engine lemma.

* **`Kt_geRat_zero_of_split` (CLOSED given the same residuals + the upstream inputs)**
  — fires `K_t ≥ 0` through `ThetaProdDprodClose.Kt_geRat_zero_of_prod_close` with
  `Hdconv` supplied by the split.

## The honest residual ledger (AGENTS.md Rule 6 / Rule 8)

Two `Type`-level residuals, neither faked, both strictly sharper than `Hdconv`:

* `ProdLimitConv fk dk x` — the prod-limit CReal `L` plus its explicit-modulus
  convergence `UnifDerivConvC (prodDeriv …) L x` (the convergence/uniformity burden).
* `ProdLimitIsRhalf … P` — `CReal.Equiv P.L (Rhalf …)` (the pure identity, no modulus).

`ProdLimitIsRhalf` is the single named lemma to target next: the isolated
differentiated-Jacobi identity `(−sin2θ)·Θ·S' ≈ (½)·Θ·S`, with the double-limit
interchange / modulus already discharged into `ProdLimitConv`.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  The two residuals are named `Type`-level data, never
`sorry`.
-/

import YMGap.Continuum.ThetaProdDprodClose
import YMGap.Continuum.ThetaSeriesFDDeriv
import YMGap.Continuum.FiniteProductFDDeriv
import YMGap.Continuum.JTPIdentity
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.HdconvClose

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. The generic engine lemma : transport a `UnifDerivConvC` across a limit identity -/

/-- **THE ENGINE LEMMA (fully generic, CLOSED).**  A rational derivative family `f'`
that converges (with explicit stage modulus `Mg`) to a CReal limit `L` at `θ` also
converges — with the SAME modulus — to any CReal `L'` with `Equiv L L'`.

The transported convergence bound comes from the reverse-triangle `leRat` transfer:
`|L' ⊖ ofQ'(f' M θ)| ≃ |L ⊖ ofQ'(f' M θ)|` (via `add_congr_left`/`abs_equiv_congr` on
the identity `L' ≈ L`), so `leRat_of_equiv` carries each `ε`-bound over verbatim.  No
new modulus is created: peeling the identity off leaves the modulus intact. -/
def unifDerivConvC_congr_limit
    {f' : Nat → Q' → Q'} {L L' : CReal} {θ : Q'}
    (h : ThetaSeriesFDDeriv.UnifDerivConvC f' L θ)
    (hId : CReal.Equiv L L') :
    ThetaSeriesFDDeriv.UnifDerivConvC f' L' θ where
  Mg := h.Mg
  conv := fun ε hε M hM =>
    CReal.leRat_of_equiv
      (CReal.abs_equiv_congr
        (CReal.add_congr_left
          (y := CReal.neg (CReal.ofQ' (f' M θ)))
          (CReal.Equiv.symm hId)))
      (h.conv ε hε M hM)

/-! ## 2. The two named residuals of the split -/

/-- **The convergence half of `Hdconv` (Type-level residual).**  A genuine prod-limit
CReal `L` together with the explicit-modulus convergence
`ofQ'(prodDeriv fk dk x M) → L`.  This is exactly a `UnifDerivConvC (prodDeriv …) L x`;
it carries the entire modulus / double-limit-interchange / uniformity burden of
`Hdconv`.  Assembled from the in-tree Pₘ→Θ product limit and the log-derivative tail
(`ThetaDerivDriverClose.sigmaTail_le`) via `CReal.mul` continuity. -/
structure ProdLimitConv (fk : Nat → Q' → Q') (dk : Nat → Q') (x : Q') : Type where
  /-- The prod-limit CReal `L = Θ·Σσ` (`= (−sin2θ)·Θ·S'`), NOT the static `Rhalf`. -/
  L : CReal
  /-- The explicit-modulus convergence `ofQ'(prodDeriv fk dk x M) → L`. -/
  conv : ThetaSeriesFDDeriv.UnifDerivConvC
           (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M) L x

/-- **The identity half of `Hdconv` (irreducible residual, no modulus).**  The single
pure algebraic CReal equation `L ≈ Rhalf`, i.e. `(−sin2θ)·Θ·S' ≈ (½)·Θ·S`.  This is
the isolated differentiated-Jacobi node — strictly sharper than `Hdconv` /
`JTPIdentity.DiffJTP` (which bundle convergence + uniformity + identity).  It is the
single named lemma to target next. -/
def ProdLimitIsRhalf {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'} (P : ProdLimitConv fk dk x) : Prop :=
  CReal.Equiv P.L (JTPIdentity.Rhalf ha0 ha1 hx hx1)

/-! ## 3. Assembling `Hdconv` from the split -/

/-- **`Hdconv` from the split (CLOSED given the two residuals).**  The convergence
half `P` and the identity half `hId : Equiv P.L Rhalf` assemble — via the generic
engine lemma — into the `UnifDerivConvC (prodDeriv …) Rhalf x` that
`ThetaProdDprodClose.prodC1Inputs` consumes as `Hdconv`. -/
def hdconvOfSplit {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'}
    (P : ProdLimitConv fk dk x)
    (hId : ProdLimitIsRhalf ha0 ha1 hx hx1 P) :
    ThetaSeriesFDDeriv.UnifDerivConvC
      (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
      (JTPIdentity.Rhalf ha0 ha1 hx hx1) x :=
  unifDerivConvC_congr_limit P.conv hId

/-! ## 4. Firing `K_t ≥ 0` through the split -/

/-- **`K_t ≥ 0` through the split (CLOSED given the split residuals + upstream inputs).**
With `Hdconv` supplied by `hdconvOfSplit` (the convergence half `P` and the identity
half `hId`), the heat-kernel series `K_t = dSeriesCReal ≥ 0` fires through the
already-closed `ThetaProdDprodClose.Kt_geRat_zero_of_prod_close`.  Every non-split
input (`C`, `Huni`, `Hpt`, `Dk`, `Hser`) is the same upstream datum that route
already carries. -/
theorem Kt_geRat_zero_of_split {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (Dk : ∀ k, TsumDeriv.FDDerivData (fun t => fk k t) (dk k) x)
    (C  : FiniteProductFDDeriv.MulCombinator)
    (Hpt : ThetaProdDprodClose.PtwiseProdData F fk)
    (Huni : ThetaProdDprodClose.UniformProdModulus C fk dk Dk)
    (P : ProdLimitConv fk dk x)
    (hId : ProdLimitIsRhalf ha0 ha1 hx hx1 P)
    (Hser : ThetaSeriesFDDeriv.ThetaSeriesC1Inputs ha0 ha1 hx hx1 F) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  ThetaProdDprodClose.Kt_geRat_zero_of_prod_close ha0 ha1 hx hx1 F fk dk Dk C Hpt Huni
    (hdconvOfSplit ha0 ha1 hx hx1 P hId) Hser

end YMGap.Continuum.HdconvClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HdconvClose.unifDerivConvC_congr_limit
#print axioms YMGap.Continuum.HdconvClose.hdconvOfSplit
#print axioms YMGap.Continuum.HdconvClose.Kt_geRat_zero_of_split
