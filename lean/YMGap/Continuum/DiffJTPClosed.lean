/-
# The corrected Wall-2 capstone: `final_Kt` / `diffJTPClosed` over the FLAT modulus

This module lands the corrected structural wiring of Wall 2, Route A, fixing the
flat-modulus plumbing bug in `DiffJTPFinal.Wall2FinalResiduals` and collapsing the
remaining wall to a fixed, honest, named `Type`-level open-core bundle.

## The bug this module fixes

`DiffJTPFinal.Wall2FinalResiduals.Huni` demands the RECURSIVE modulus
`ThetaProdDprodClose.UniformProdModulus mulCombinator fk dk Dk`.  For the as-built
combinator `C = MulCombinatorClose.mulCombinator`, that recursive per-`M` modulus
`(finiteProductFDDeriv C Dk M).δ` contracts geometrically in `M` (each `mulEta`
step rescales the tolerance), so its infimum over `M` is `0` and NO positive
`delStar` clears every `M`: the recursive `huni` is UNSATISFIABLE (proved in
`ProdUnifModulusClose`'s header).  The correct object is the FLAT, non-recursive
family `ProdUnifModulusClose.prodFlatModulus`, whose modulus `δ ε = min(1, ε/B)` is
manifestly `M`-independent, so `huni` becomes `le_refl`.  But the flat tower was
orphaned from `prodC1Inputs`/`final_Kt`.  This module re-plumbs the product-side
`C1InputsC` through the flat modulus (`prodC1InputsFlat`), then rebuilds the
capstone over it.

## What this module DELIVERS

* **`prodC1InputsFlat`** (Part B, the bug fix) — the product-side `C1InputsC`
  assembled through the FLAT `prodFlatModulus` (from a single
  `ProdSecondDiffResidual`), replacing the unsatisfiable recursive modulus.  The
  `fdboundC` field is `(ofQ'FDDerivDataC (prodFlatModulus H M)).bound` after one
  `le_trans'` on `|h| ≤ delStar ε' ≤ (prodFlatModulus H M).δ ε'` (with `huni`
  = `le_refl`).  Genuine content: closes the plumbing hole.
* **`thetaProdDprodFlat`** — the product-side witness `FDDerivDataC F Rhalf x`
  fired from `prodC1InputsFlat` through the CLOSED
  `ThetaC1LimitEngine.fdDerivDataC_of_unif_M`.
* **`Wall2OpenCores`** (Part C, the corrected residual bundle) — the entire
  remaining Wall-2 input, flat-typed, over one common `F = ϑ₃` at `x`.  Leaf 5 is
  carried as `ProdSecondDiffClose.ProdSecondDiffInputs` (the per-step Leibniz
  recursion + supersolution budget), which `prodSecondDiffOfFactors` turns into the
  `ProdSecondDiffResidual` the flat modulus consumes.  Leaf 6 is carried SPLIT as
  `HdconvClose.ProdLimitConv` + `HdconvReroute.LProductFactor` +
  `HdconvReroute.CoeffHalfIdentity`, isolating `CoeffHalfIdentity` (`A ≈ ½·S`) as
  the single frontier obligation.
* **`wall2Round2_of_cores`** — collapses `Wall2OpenCores` to the upstream
  `DiffJTPClose.Wall2Round2Residuals`, using the FLAT product side, the series
  residual via `thetaSeriesC1Inputs_of_residual`, and the leaf-6 split via
  `HdconvReroute.hdconv_of_factor_coeff`.
* **`final_Kt`** — `K_t = dSeriesCReal ≥ 0`, fired from `Wall2OpenCores` through the
  CLOSED `DiffJTPClose.diffJTPClose`.  The honest analytic payload.
* **`diffJTPClosed`** — `DiffJTP`, from the same bundle.  HONESTY (Rule 6):
  `CoeffHalfIdentity` is content-equal to `DiffJTP`-minus-interchange, so this
  RE-EXPRESSES the interchange rather than discharging it; `CoeffHalfIdentity`
  is the irreducible crux.

## The honest residual ledger (AGENTS.md Rule 6) — the OPEN cores

`Wall2OpenCores` carries exactly these outstanding inputs, none faked:

1. `F : Q' → CReal` — the common `CReal` ϑ₃ limit.
2. `resSer : ThetaSeriesFieldsClose.ThetaSeriesResidual …` — the series-side
   `ptθ`/`ptθh` theta limits + the Chebyshev-`T` `fdbound` (`unif` is CLOSED by
   `seriesUnif`, NOT carried).
3. `Hpt : PtwiseProdData F fk` — uniform-in-point product convergence.
4. `Hin : ProdSecondDiffClose.ProdSecondDiffInputs fk dk x B` — the per-step Leibniz
   recursion `hstep` + supersolution `hsuper` (leaf 5, reduced to the M-uniform head
   `Θ` / derivative `Δ` / geometric summability inputs; the per-factor second
   difference is CLOSED by `DkProducerClose.jacFdRem_vanishes`).
5. `P : HdconvClose.ProdLimitConv fk dk x` — the log-derivative convergence half.
6. `Lfac : HdconvReroute.LProductFactor … P` — the `A = (−sin2θ)·S'` factorisation.
7. `hCoeff : HdconvReroute.CoeffHalfIdentity … Lfac.A` — `A ≈ ½·S`, THE FRONTIER
   (= `DiffJTP`-minus-interchange).

## Honesty flags (AGENTS.md Rule 6)

* This capstone is CONDITIONAL on `Wall2OpenCores`; it is NOT unconditional.  No
  declaration here asserts `final_Kt`/`diffJTPClosed` free of the open cores.
* Leaf 5 is carried as `ProdSecondDiffInputs` (its `hstep`/`hsuper` fields ARE the
  named residual); the further `ProdSecondDiffInputs`-from-Θ/Δ/geometric producer
  needs the Leibniz product expansion and is NOT built here.
* `final_Kt` is the honest analytic payload; `diffJTPClosed` re-expresses the
  interchange (leaf 7 is content-equal to `DiffJTP`).

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  All cores are `Type`/`Prop`-level fields, never `sorry`.
-/

import YMGap.Continuum.DiffJTPClose
import YMGap.Continuum.ProdUnifModulusClose
import YMGap.Continuum.ProdSecondDiffClose
import YMGap.Continuum.ThetaProdDprodClose
import YMGap.Continuum.ThetaSeriesFieldsClose
import YMGap.Continuum.HdconvClose
import YMGap.Continuum.HdconvReroute
import YMGap.Continuum.ThetaC1LimitEngine
import YMGap.Continuum.ThetaFDDerivAssembly
import YMGap.Continuum.FiniteProductFDDeriv
import YMGap.Continuum.DiffProduct
import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.JTPIdentity
import YMGap.Constructive.Reals

namespace YMGap.Continuum.DiffJTPClosed

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. Part B — the product-side `C1InputsC` through the FLAT modulus (bug fix)

The single structural correction: build the product-side engine input over the FLAT,
`M`-independent family `ProdUnifModulusClose.prodFlatModulus H` (with `huni = le_refl`)
instead of the recursive `finiteProductFDDeriv C Dk M` whose modulus provably tends
to `0` in `M`.  The truncation family `F_M t = ofQ'(pre (fun k => fk k t) M)` and the
derivative family `d_M = ofQ'(prodDeriv fk dk x M)` are UNCHANGED, so the resulting
`C1InputsC` has exactly the type `Wall2Round2Residuals.prod` demands. -/

/-- **`prodC1InputsFlat` — the corrected product-side C¹ inputs.**  Assembles the
engine input `C1InputsC` over the lifted finite-product truncations and the FLAT
modulus from the single quadratic residual `H : ProdSecondDiffResidual`.  The
`fdboundC` field is the lifted flat modulus's own bound after one `le_trans'` on
`|h| ≤ delStar ε' ≤ (prodFlatModulus H M).δ ε'`, with `huni` supplied by the CLOSED
`prodUnifModulus` (`= le_refl`, `mStar = 0`). -/
def prodC1InputsFlat {a x B : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (H : ProdUnifModulusClose.ProdSecondDiffResidual fk dk x B)
    (Hpt : ThetaProdDprodClose.PtwiseProdData F fk)
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
  delStar := (ProdUnifModulusClose.prodUnifModulus H).delStar
  delStar_pos := (ProdUnifModulusClose.prodUnifModulus H).delStar_pos
  mStar := (ProdUnifModulusClose.prodUnifModulus H).mStar
  fdboundC := fun ε' hε' M hM h hpos hle =>
    (ThetaFDDerivAssembly.ofQ'FDDerivDataC (ProdUnifModulusClose.prodFlatModulus H M)).bound
      ε' hε' h hpos
      (Q'.le_trans' (Q'.abs h)
        ((ProdUnifModulusClose.prodUnifModulus H).delStar ε')
        ((ProdUnifModulusClose.prodFlatModulus H M).δ ε')
        hle ((ProdUnifModulusClose.prodUnifModulus H).huni ε' M hM))

/-- **`thetaProdDprodFlat` — the product-side witness through the flat modulus.**
Fire the CLOSED CReal-truncation C¹-limit engine on `prodC1InputsFlat` to produce
`Dprod : FDDerivDataC F (Rhalf …) x`. -/
def thetaProdDprodFlat {a x B : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (H : ProdUnifModulusClose.ProdSecondDiffResidual fk dk x B)
    (Hpt : ThetaProdDprodClose.PtwiseProdData F fk)
    (Hdconv : ThetaSeriesFDDeriv.UnifDerivConvC
                (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
                (JTPIdentity.Rhalf ha0 ha1 hx hx1) x) :
    TsumDeriv.FDDerivDataC F (JTPIdentity.Rhalf ha0 ha1 hx hx1) x :=
  ThetaC1LimitEngine.fdDerivDataC_of_unif_M
    (prodC1InputsFlat ha0 ha1 hx hx1 F fk dk H Hpt Hdconv)

/-! ## 2. Part C — the corrected open-core bundle (flat-typed) -/

/-- **`Wall2OpenCores` — the entire remaining Wall-2 input, flat-typed.**  Over one
common `F = ϑ₃` at `x`, this bundles the outstanding leaves, with the flat-modulus
correction (leaf 5 via `ProdSecondDiffInputs`) and the fully SPLIT leaf 6 (isolating
`CoeffHalfIdentity` as the frontier).  Inhabit it and `K_t ≥ 0` (`final_Kt`) and
`DiffJTP` (`diffJTPClosed`) follow with no further analysis. -/
structure Wall2OpenCores {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Type where
  /-- Leaf 1: the common `CReal` ϑ₃ limit. -/
  F : Q' → CReal
  /-- Leaf 2: the `F`-entangled series-side residual (`ptθ`/`ptθh`/`fdbound`; `unif`
  is CLOSED, not carried). -/
  resSer : ThetaSeriesFieldsClose.ThetaSeriesResidual ha0 ha1 hx hx1 F
  /-- The `Q'`-level per-factor Jacobi factor family. -/
  fk : Nat → Q' → Q'
  /-- The `Q'`-level per-factor Jacobi derivative-value family. -/
  dk : Nat → Q'
  /-- The `M`-independent quadratic prefactor. -/
  B : Q'
  /-- Leaf 3: uniform-in-point convergence of the lifted finite products to `F`. -/
  Hpt : ThetaProdDprodClose.PtwiseProdData F fk
  /-- Leaf 5 (flat, corrected): the per-step Leibniz recursion + supersolution
  budget, from which `prodSecondDiffOfFactors` produces the quadratic residual the
  FLAT modulus consumes.  (The per-factor second difference is CLOSED by
  `DkProducerClose.jacFdRem_vanishes`.) -/
  Hin : ProdSecondDiffClose.ProdSecondDiffInputs fk dk x B
  /-- Leaf 6, convergence half: the log-derivative prod-limit CReal `L` with its
  explicit-modulus convergence. -/
  P : HdconvClose.ProdLimitConv fk dk x
  /-- Leaf 6a: the factorisation `P.L ≈ Θ·A`, `A = (−sin2θ)·S'`. -/
  Lfac : HdconvReroute.LProductFactor ha0 ha1 hx hx1 P
  /-- Leaf 6b — THE FRONTIER: the coefficient identity `A ≈ ½·S`
  (= `DiffJTP`-minus-interchange). -/
  hCoeff : HdconvReroute.CoeffHalfIdentity ha0 ha1 hx hx1 Lfac.A

/-- **The flat-modulus quadratic residual, from the per-step Leibniz inputs.**  The
CLOSED discrete-Grönwall induction `prodSecondDiffOfFactors` turns the carried
`ProdSecondDiffInputs` into the `ProdSecondDiffResidual` the flat modulus consumes. -/
def residual_of_cores {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2OpenCores ha0 ha1 hx hx1) :
    ProdUnifModulusClose.ProdSecondDiffResidual W.fk W.dk x W.B :=
  ProdSecondDiffClose.prodSecondDiffOfFactors W.Hin

/-- **The product-side `Hdconv`, from the SPLIT leaf 6.**  The convergence half `P`,
the factorisation `Lfac`, and the frontier identity `hCoeff` assemble — via the
CLOSED `HdconvReroute.hdconv_of_factor_coeff` (`Θ`-cancellation + `regroup_half_theta_S`)
— into the `UnifDerivConvC (prodDeriv …) Rhalf x` the flat product side consumes. -/
def hdconv_of_cores {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2OpenCores ha0 ha1 hx hx1) :
    ThetaSeriesFDDeriv.UnifDerivConvC
      (fun M t => FiniteProductFDDeriv.prodDeriv W.fk W.dk t M)
      (JTPIdentity.Rhalf ha0 ha1 hx hx1) x :=
  HdconvReroute.hdconv_of_factor_coeff ha0 ha1 hx hx1 W.P W.Lfac W.hCoeff

/-- **The single wiring theorem.**  Collapse `Wall2OpenCores` to the upstream
`DiffJTPClose.Wall2Round2Residuals`: the series side via
`thetaSeriesC1Inputs_of_residual` (CLOSED `seriesUnif` for `unif`), the product side
via `prodC1InputsFlat` (the FLAT modulus), and the leaf-6 split via
`hdconv_of_factor_coeff`. -/
def wall2Round2_of_cores {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2OpenCores ha0 ha1 hx hx1) :
    DiffJTPClose.Wall2Round2Residuals ha0 ha1 hx hx1 where
  F := W.F
  series := ThetaSeriesFieldsClose.thetaSeriesC1Inputs_of_residual ha0 ha1 hx hx1 W.F W.resSer
  prodTrunc := fun M t => CReal.ofQ' (DiffProduct.pre (fun k => W.fk k t) M)
  prodDeriv := fun M => CReal.ofQ' (FiniteProductFDDeriv.prodDeriv W.fk W.dk x M)
  prod := prodC1InputsFlat ha0 ha1 hx hx1 W.F W.fk W.dk
    (residual_of_cores ha0 ha1 hx hx1 W) W.Hpt (hdconv_of_cores ha0 ha1 hx hx1 W)

/-! ## 3. The firings (pure wiring over the two CLOSED engines) -/

/-- **`final_Kt` — the honest analytic capstone `K_t ≥ 0`.**  From the corrected
open-core bundle, the heat-kernel series `K_t = dSeriesCReal ≥ 0` fires through the
CLOSED `DiffJTPClose.diffJTPClose` with no further analysis. -/
theorem final_Kt {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2OpenCores ha0 ha1 hx hx1) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  DiffJTPClose.diffJTPClose ha0 ha1 hx hx1 (wall2Round2_of_cores ha0 ha1 hx hx1 W)

/-- **`diffJTPClosed` — the differentiated Jacobi-triple-product identity `DiffJTP`.**
Fired from the SAME open-core bundle via the CLOSED `DiffJTPClose.diffJTP_of_round2`.

HONESTY (Rule 6): leaf 7 `hCoeff : CoeffHalfIdentity` is content-equal to
`DiffJTP`-minus-interchange, so this theorem RE-EXPRESSES the interchange through the
C¹-limit engines rather than discharging it.  `final_Kt` is the honest payload;
`CoeffHalfIdentity` is the irreducible frontier. -/
theorem diffJTPClosed {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2OpenCores ha0 ha1 hx hx1) :
    JTPIdentity.DiffJTP ha0 ha1 hx hx1 :=
  DiffJTPClose.diffJTP_of_round2 ha0 ha1 hx hx1 (wall2Round2_of_cores ha0 ha1 hx hx1 W)

end YMGap.Continuum.DiffJTPClosed

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `native_decide`, no `sorry`, no custom axiom.  The fields of
`Wall2OpenCores` are named `Type`/`Prop`-obligations (the outstanding analytic
inputs), NOT `sorry`. -/

#print axioms YMGap.Continuum.DiffJTPClosed.prodC1InputsFlat
#print axioms YMGap.Continuum.DiffJTPClosed.thetaProdDprodFlat
#print axioms YMGap.Continuum.DiffJTPClosed.residual_of_cores
#print axioms YMGap.Continuum.DiffJTPClosed.hdconv_of_cores
#print axioms YMGap.Continuum.DiffJTPClosed.wall2Round2_of_cores
#print axioms YMGap.Continuum.DiffJTPClosed.final_Kt
#print axioms YMGap.Continuum.DiffJTPClosed.diffJTPClosed
