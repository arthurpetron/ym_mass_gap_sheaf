/-
# Closing the product-side witness `Dprod` (Wall-2, Route A, CReal-derivative layer)

This module fires the CReal-truncation C¹-limit engine
`ThetaC1LimitEngine.fdDerivDataC_of_unif_M` on the **finite-product** truncation
family to produce the product-side witness

    Dprod : TsumDeriv.FDDerivDataC F (JTPIdentity.Rhalf …) x

that `DiffJTPAssembly.diffJTPAssembly` / `DiffJTPAssembly.Wall2CRealWitnesses`
consume.  Paired with the already-built series-side witness
`ThetaSeriesFDDeriv.thetaSeriesFDDeriv` over the SAME common `F = ϑ₃`, this fires
`K_t ≥ 0` with no further analysis (`DiffJTPAssembly.Kt_geRat_zero_of_assembly`).

## The engine instantiation (all four engine free-variables pinned)

* `F_M M t := CReal.ofQ' (DiffProduct.pre (fun k => fk k t) M)` — the lifted finite
  product truncations;
* `Flim := F` — the genuine common CReal ϑ₃ (identified across sides by
  `ThetaLimit.gauss_qbinom_creal_equiv`, supplied to us as the single `F`);
* `dfam M := CReal.ofQ' (FiniteProductFDDeriv.prodDeriv fk dk x M)` — the lifted
  finite Leibniz derivative values;
* `dlim := JTPIdentity.Rhalf …`, `θ := x`.

The single reused object is the lifted finite-product finite-difference derivative

    Dfin  M := FiniteProductFDDeriv.finiteProductFDDeriv C Dk M
    DfinC M := ThetaFDDerivAssembly.ofQ'FDDerivDataC (Dfin M)

whose modulus `(DfinC M).δ = (Dfin M).δ` and whose `bound` is index-wise the `Q'`
finite-product remainder bound.

## The three `C1InputsC` field-groups, and the honest residuals

1. **`Ncut` / `conv`** — pointwise, uniform-in-point CReal convergence of the
   lifted product truncations to `F`.  Carried as `PtwiseProdData` (the finite
   product Cauchy self-modulus transported to `F`).

2. **`delStar` / `delStar_pos` / `mStar` / `fdboundC`** — the per-`M` cleared
   CReal finite-difference bound.  `ofQ'FDDerivDataC` makes the lifted `fdRemC`
   index-wise equal to the rational `fdRem`, so `(DfinC M).bound` supplies the
   bound **for the per-`M` modulus `(Dfin M).δ`**.  The engine field `fdboundC`
   demands ONE `delStar` valid for ALL `M ≥ mStar ε'`; the per-`M` moduli
   `(Dfin M).δ` (built by `MulCombinator.mul`'s `min …`) are NOT automatically
   uniform in `M`.  This uniform-in-`M` finite-difference modulus is the genuine
   extra obligation, carried as `UniformProdModulus` (`huni`), and `fdboundC` is
   `(DfinC M).bound` after `Q'.le_trans'` on `|h| ≤ delStar ε' ≤ (Dfin M).δ ε'`.

3. **`Mg` / `dconv`** — the CReal-target derivative-value convergence
   `ofQ'(prodDeriv …) → Rhalf`.  This is the CReal-target datum
   `ThetaSeriesFDDeriv.UnifDerivConvC (prodDeriv …) Rhalf x`, content-equal to
   `JTPIdentity.DiffJTP` — the single hard node (the `(DIFF)` double-limit
   interchange).  Carried as `Hdconv`; folded into `dconv` by the engine's own
   sign-flip primitive `ThetaC1LimitEngine.leRat_abs_sub_comm`.

## Net residual ledger for `Dprod` (three carried inputs, none faked)

1. `FiniteProductFDDeriv.MulCombinator` — the binary product-rule combinator;
2. `UniformProdModulus` — the uniform-in-`M` finite-difference modulus;
3. `Hdconv : UnifDerivConvC (prodDeriv …) Rhalf x` — the CReal-target derivative
   convergence, content-equal to `JTPIdentity.DiffJTP`.

Everything else — the four-piece telescope, the `q/4` bookkeeping, the index-wise
lift, the sign flip, and the capstone firing — is already CLOSED upstream.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  The three residuals are named `Type`-level data
(fields/parameters), never `sorry`.
-/

import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.DiffProduct
import YMGap.Continuum.JTPIdentity
import YMGap.Continuum.FiniteProductFDDeriv
import YMGap.Continuum.ThetaFDDerivAssembly
import YMGap.Continuum.ThetaSeriesFDDeriv
import YMGap.Continuum.ThetaC1LimitEngine
import YMGap.Continuum.DiffJTPAssembly
import YMGap.Constructive.Reals

namespace YMGap.Continuum.ThetaProdDprodClose

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. Field-group 1 : the pointwise (uniform-in-point) convergence datum

The lifted finite product truncations `ofQ'(pre (fun k => fk k p) M)` converge to
the common CReal limit `F p`, uniformly in the evaluation point `p` (the finite
product Cauchy self-modulus, `|cos| ≤ 1` making it uniform in `p`).  This is
exactly the `Ncut`/`conv` pair of `C1InputsC`. -/

/-- **The pointwise product-convergence datum** (Field-group 1, carried).  Past
stage `Ncut ε`, the lifted finite product truncation `ofQ'(pre (fun k => fk k p) M)`
is within `ε` of `F p`, at EVERY point `p`. -/
structure PtwiseProdData (F : Q' → CReal) (fk : Nat → Q' → Q') : Type where
  /-- The uniform-in-point pointwise-convergence stage modulus. -/
  Ncut : Q' → Nat
  /-- Past `Ncut ε`, `F p ⊖ ofQ'(pre (fun k => fk k p) M)` has limit `≤ ε`, at
  every point `p`. -/
  conv : ∀ ε : Q', (0 : Q') < ε → ∀ M : Nat, Ncut ε ≤ M → ∀ p : Q',
    CReal.leRat
      (CReal.abs (CReal.add (F p)
        (CReal.neg (CReal.ofQ' (DiffProduct.pre (fun k => fk k p) M))))) ε

/-! ## 2. Field-group 2 : the uniform-in-`M` finite-difference modulus

The per-`M` finite-product derivative `Dfin M := finiteProductFDDeriv C Dk M`
carries its own modulus `(Dfin M).δ` (from `MulCombinator.mul`'s `min …`).  The
engine needs ONE `delStar` below ALL of them past a stage `mStar`.  This
equicontinuity-at-`x` datum `huni` is the honest extra obligation, and it is all
`fdboundC` needs (via `Q'.le_trans'` and `(DfinC M).bound`). -/

/-- **The uniform-in-`M` finite-difference modulus datum** (Field-group 2, carried).
A single positive `delStar` that, past stage `mStar ε'`, lies below every per-`M`
finite-product modulus `(finiteProductFDDeriv C Dk M).δ ε'`. -/
structure UniformProdModulus {x : Q'} (C : FiniteProductFDDeriv.MulCombinator)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (Dk : ∀ k, TsumDeriv.FDDerivData (fun t => fk k t) (dk k) x) : Type where
  /-- The common finite-difference modulus (family equicontinuity at `x`). -/
  delStar : Q' → Q'
  /-- `delStar` is positive for positive tolerance. -/
  delStar_pos : ∀ ε : Q', (0 : Q') < ε → (0 : Q') < delStar ε
  /-- The stage past which the common modulus is valid. -/
  mStar : Q' → Nat
  /-- Past `mStar ε'`, `delStar ε'` is below the per-`M` finite-product modulus. -/
  huni : ∀ ε' : Q', ∀ M : Nat, mStar ε' ≤ M →
    delStar ε' ≤ (FiniteProductFDDeriv.finiteProductFDDeriv C Dk M).δ ε'

/-! ## 3. The engine call : assembling `C1InputsC` and firing the capstone -/

/-- **The bundled product-side `C1InputsC`.**  Assembles the three carried
field-groups into the engine's input record over the lifted finite-product family
`F_M M t = ofQ'(pre (fun k => fk k t) M)`, limit `F`, derivative family
`dfam M = ofQ'(prodDeriv fk dk x M)`, and limit derivative `Rhalf`, at `θ = x`. -/
def prodC1Inputs {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (Dk : ∀ k, TsumDeriv.FDDerivData (fun t => fk k t) (dk k) x)
    (C  : FiniteProductFDDeriv.MulCombinator)
    (Hpt : PtwiseProdData F fk)
    (Huni : UniformProdModulus C fk dk Dk)
    (Hdconv : ThetaSeriesFDDeriv.UnifDerivConvC
                (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
                (JTPIdentity.Rhalf ha0 ha1 hx hx1) x) :
    ThetaC1LimitEngine.C1InputsC
      (fun M t => CReal.ofQ' (DiffProduct.pre (fun k => fk k t) M))
      F
      (fun M => CReal.ofQ' (FiniteProductFDDeriv.prodDeriv fk dk x M))
      (JTPIdentity.Rhalf ha0 ha1 hx hx1) x where
  Ncut := Hpt.Ncut
  conv := Hpt.conv
  Mg := Hdconv.Mg
  dconv := fun ε hε M hM =>
    ThetaC1LimitEngine.leRat_abs_sub_comm (Hdconv.conv ε hε M hM)
  delStar := Huni.delStar
  delStar_pos := Huni.delStar_pos
  mStar := Huni.mStar
  fdboundC := fun ε' hε' M hM h hpos hle =>
    (ThetaFDDerivAssembly.ofQ'FDDerivDataC
        (FiniteProductFDDeriv.finiteProductFDDeriv C Dk M)).bound
      ε' hε' h hpos
      (Q'.le_trans' (Q'.abs h) (Huni.delStar ε')
        ((FiniteProductFDDeriv.finiteProductFDDeriv C Dk M).δ ε')
        hle (Huni.huni ε' M hM))

/-- **THE PRODUCT-SIDE WITNESS `Dprod`.**  Firing the CReal-truncation C¹-limit
engine `ThetaC1LimitEngine.fdDerivDataC_of_unif_M` on the finite-product family
produces the `FDDerivDataC F (Rhalf …) x` that `DiffJTPAssembly.diffJTPAssembly`
consumes as `Dprod`.  Everything past the three carried residuals
(`C`, `Huni`, `Hdconv`, plus the per-factor `Dk` and pointwise `Hpt`) is the
already-closed engine. -/
def thetaProdDprod {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (Dk : ∀ k, TsumDeriv.FDDerivData (fun t => fk k t) (dk k) x)
    (C  : FiniteProductFDDeriv.MulCombinator)
    (Hpt : PtwiseProdData F fk)
    (Huni : UniformProdModulus C fk dk Dk)
    (Hdconv : ThetaSeriesFDDeriv.UnifDerivConvC
                (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
                (JTPIdentity.Rhalf ha0 ha1 hx hx1) x) :
    TsumDeriv.FDDerivDataC F (JTPIdentity.Rhalf ha0 ha1 hx hx1) x :=
  ThetaC1LimitEngine.fdDerivDataC_of_unif_M
    (prodC1Inputs ha0 ha1 hx hx1 F fk dk Dk C Hpt Huni Hdconv)

/-! ## 4. Firing `K_t ≥ 0` : the product witness paired with the series witness -/

/-- **`Dprod` + `Dser` ⟹ `K_t ≥ 0`.**  With the product-side witness built here and
the series-side witness `ThetaSeriesFDDeriv.thetaSeriesFDDeriv` over the SAME common
`F`, the heat-kernel series `K_t = dSeriesCReal ≥ 0` fires through the already-closed
capstone `DiffJTPAssembly.Kt_geRat_zero_of_assembly` — no further analysis. -/
theorem Kt_geRat_zero_of_prod_close {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (Dk : ∀ k, TsumDeriv.FDDerivData (fun t => fk k t) (dk k) x)
    (C  : FiniteProductFDDeriv.MulCombinator)
    (Hpt : PtwiseProdData F fk)
    (Huni : UniformProdModulus C fk dk Dk)
    (Hdconv : ThetaSeriesFDDeriv.UnifDerivConvC
                (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
                (JTPIdentity.Rhalf ha0 ha1 hx hx1) x)
    (Hser : ThetaSeriesFDDeriv.ThetaSeriesC1Inputs ha0 ha1 hx hx1 F) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  DiffJTPAssembly.Kt_geRat_zero_of_assembly ha0 ha1 hx hx1 F x
    (thetaProdDprod ha0 ha1 hx hx1 F fk dk Dk C Hpt Huni Hdconv)
    (ThetaSeriesFDDeriv.thetaSeriesFDDeriv ha0 ha1 hx hx1 F Hser)

end YMGap.Continuum.ThetaProdDprodClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaProdDprodClose.prodC1Inputs
#print axioms YMGap.Continuum.ThetaProdDprodClose.thetaProdDprod
#print axioms YMGap.Continuum.ThetaProdDprodClose.Kt_geRat_zero_of_prod_close
