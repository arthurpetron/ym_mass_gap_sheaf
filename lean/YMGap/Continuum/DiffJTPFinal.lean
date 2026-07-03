/-
# The Wall-2 conditional capstone: collapsing `DiffJTP` / `K_t ≥ 0` to six named leaves

This module lands the LAST structural wiring gap of Wall 2, Route A.  It exposes a
SINGLE entry point that collapses the entire wall to a fixed, named `Type`-level
leaf set, then fires the two already-green capstones (`DiffJTPClose.diffJTPClose`
for `K_t ≥ 0` and `DiffJTPClose.diffJTP_of_round2` for `DiffJTP`).

## What is CLOSED upstream (consumed here, not re-proved)

* `DiffJTPClose.Wall2Round2Residuals` + `diffJTPClose` / `diffJTP_of_round2` — the
  firing capstones over the two common-`F` finite-difference derivatives.
* `ThetaSeriesFieldsClose.thetaSeriesC1Inputs_of_residual` — assembles the
  series-side C¹ inputs from the proved `seriesUnif` (the `unif` field) plus the
  `F`-entangled residual `ThetaSeriesResidual`.
* `ThetaProdDprodClose.prodC1Inputs` — assembles the product-side C¹ inputs from
  the CLOSED product-rule combinator `MulCombinatorClose.mulCombinator`, plus the
  per-factor `Q'`-level derivatives, the pointwise datum, the uniform-in-`M`
  modulus, and the derivative-value convergence.
* `MulCombinatorClose.mulCombinator` — the binary finite-difference product rule
  (`C`), CLOSED; NOT a residual.

## What this module DELIVERS

`Wall2FinalResiduals` bundles the ENTIRE remaining Wall-2 input as ONE named
`Type` over a single common limit `F = ϑ₃` at the working point `x`.  Given the
bundle, `wall2Residuals_of` produces the upstream `Wall2Round2Residuals` with NO
further analysis, and `final_Kt` / `diffJTPFinal` fire the two capstones.

## The honest residual ledger (AGENTS.md Rule 6) — SIX named leaves, none faked

The `Wall2FinalResiduals` bundle carries exactly these outstanding inputs:

1. `F : Q' → CReal` — the common `CReal` ϑ₃ limit (with the `(z,q) ↦ (a,θ)` theta
   parametrization match packaged into `F` itself);
2. `resSer : ThetaSeriesFieldsClose.ThetaSeriesResidual …` — the series-side
   `F`-entangled `ptθ`/`ptθh` limits + the Chebyshev-`T` second-difference
   `fdbound`.  (The `unif` field is CLOSED by `seriesUnif`, NOT carried.)
3. `Dk : ∀ k, FDDerivData (fun t => fk k t) (dk k) x` — the `Q'`-level per-factor
   Jacobi finite-difference derivatives;
4. `Hpt : PtwiseProdData F fk` — uniform-in-point convergence of the lifted finite
   products to `F`;
5. `Huni : UniformProdModulus mulCombinator fk dk Dk` — the uniform-in-`M`
   finite-difference modulus;
6. `Hdconv : UnifDerivConvC (fun M t => prodDeriv fk dk t M) Rhalf x` — the
   product-derivative-value convergence (content-equal to `JTPIdentity.DiffJTP`,
   the single irreducible `(DIFF)` double-limit-interchange crux).

## Honesty flags (AGENTS.md Rule 6)

* This capstone is **conditional** on the six leaves; it is NOT unconditional.
* `final_Kt` (`K_t ≥ 0`) is the honest analytic payload.  `diffJTPFinal` produces
  `DiffJTP` from the SAME bundle, but `Hdconv` is content-equal to `DiffJTP`, so
  `diffJTPFinal` RE-EXPRESSES rather than discharges the interchange; `Hdconv` is
  the irreducible crux leaf.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  All six leaves are `Type`-level fields, never `sorry`.
-/

import YMGap.Continuum.DiffJTPClose
import YMGap.Continuum.ThetaProdDprodClose
import YMGap.Continuum.ThetaSeriesFieldsClose
import YMGap.Continuum.MulCombinatorClose
import YMGap.Continuum.ThetaSeriesFDDeriv
import YMGap.Continuum.FiniteProductFDDeriv
import YMGap.Continuum.DiffProduct
import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.JTPIdentity
import YMGap.Constructive.Reals

namespace YMGap.Continuum.DiffJTPFinal

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. The six-leaf residual bundle over one common `F` at `θ₀ = x` -/

/-- **The entire remaining Wall-2 input, as ONE named `Type`.**  Over a single
common limit `F = ϑ₃` at the working point `x`, this bundles the six outstanding
leaves that the two CLOSED C¹-limit engines (series and product) still consume.

Inhabit it and `K_t ≥ 0` (via `final_Kt`) and `DiffJTP` (via `diffJTPFinal`) follow
with no further analysis.  The product-rule combinator `MulCombinatorClose.mulCombinator`
and the series-side `unif` field are CLOSED and are NOT carried here. -/
structure Wall2FinalResiduals {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Type where
  /-- Leaf 1: the common `CReal` ϑ₃ limit (theta parametrization packaged in). -/
  F : Q' → CReal
  /-- Leaf 2: the `F`-entangled series-side residual (`ptθ`/`ptθh`/`fdbound`). -/
  resSer : ThetaSeriesFieldsClose.ThetaSeriesResidual ha0 ha1 hx hx1 F
  /-- The `Q'`-level per-factor Jacobi factor family. -/
  fk : Nat → Q' → Q'
  /-- The `Q'`-level per-factor Jacobi derivative-value family. -/
  dk : Nat → Q'
  /-- Leaf 3: the `Q'`-level per-factor Jacobi finite-difference derivatives. -/
  Dk : ∀ k, TsumDeriv.FDDerivData (fun t => fk k t) (dk k) x
  /-- Leaf 4: uniform-in-point convergence of the lifted finite products to `F`. -/
  Hpt : ThetaProdDprodClose.PtwiseProdData F fk
  /-- Leaf 5: the uniform-in-`M` finite-difference modulus. -/
  Huni : ThetaProdDprodClose.UniformProdModulus MulCombinatorClose.mulCombinator fk dk Dk
  /-- Leaf 6: product-derivative-value convergence (the `(DIFF)` interchange crux). -/
  Hdconv : ThetaSeriesFDDeriv.UnifDerivConvC
             (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
             (JTPIdentity.Rhalf ha0 ha1 hx hx1) x

/-! ## 2. The wiring: bundle ⟹ upstream `Wall2Round2Residuals`

Every field unifies definitionally with the upstream record: `prodTrunc`/`prodDeriv`
are exactly the lifted finite-product forms `prodC1Inputs` is stated over, and
`series` is exactly what `thetaSeriesC1Inputs_of_residual` returns. -/

/-- **The single wiring theorem.**  Collapse the six-leaf bundle to the upstream
`DiffJTPClose.Wall2Round2Residuals`: the series side via
`thetaSeriesC1Inputs_of_residual` (using the CLOSED `seriesUnif` for `unif`), the
product side via `prodC1Inputs` (using the CLOSED `mulCombinator` for `C`). -/
def wall2Residuals_of {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2FinalResiduals ha0 ha1 hx hx1) :
    DiffJTPClose.Wall2Round2Residuals ha0 ha1 hx hx1 where
  F := W.F
  series := ThetaSeriesFieldsClose.thetaSeriesC1Inputs_of_residual ha0 ha1 hx hx1 W.F W.resSer
  prodTrunc := fun M t => CReal.ofQ' (DiffProduct.pre (fun k => W.fk k t) M)
  prodDeriv := fun M => CReal.ofQ' (FiniteProductFDDeriv.prodDeriv W.fk W.dk x M)
  prod := ThetaProdDprodClose.prodC1Inputs ha0 ha1 hx hx1 W.F W.fk W.dk W.Dk
    MulCombinatorClose.mulCombinator W.Hpt W.Huni W.Hdconv

/-! ## 3. The firings (pure wiring over the two CLOSED engines) -/

/-- **`final_Kt` — the honest analytic capstone `K_t ≥ 0`.**  From the six-leaf
bundle, the heat-kernel series `K_t = dSeriesCReal ≥ 0` fires through the CLOSED
`DiffJTPClose.diffJTPClose` with no further analysis. -/
theorem final_Kt {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2FinalResiduals ha0 ha1 hx hx1) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  DiffJTPClose.diffJTPClose ha0 ha1 hx hx1 (wall2Residuals_of ha0 ha1 hx hx1 W)

/-- **`diffJTPFinal` — the differentiated Jacobi-triple-product identity `DiffJTP`.**
Fired from the SAME six-leaf bundle via the CLOSED `DiffJTPClose.diffJTP_of_round2`.

HONESTY (Rule 6): leaf 6 `Hdconv` is content-equal to `DiffJTP` itself (the
`(DIFF)` double-limit interchange), so this theorem RE-EXPRESSES the interchange
through the C¹-limit engines rather than discharging it.  `final_Kt` is the honest
payload; `Hdconv` is the irreducible crux. -/
theorem diffJTPFinal {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2FinalResiduals ha0 ha1 hx hx1) :
    JTPIdentity.DiffJTP ha0 ha1 hx hx1 :=
  DiffJTPClose.diffJTP_of_round2 ha0 ha1 hx hx1 (wall2Residuals_of ha0 ha1 hx hx1 W)

end YMGap.Continuum.DiffJTPFinal

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `native_decide`, no `sorry`, no custom axiom.  The six fields
of `Wall2FinalResiduals` are named `Type`-obligations (the outstanding analytic
inputs), NOT `sorry`. -/

#print axioms YMGap.Continuum.DiffJTPFinal.wall2Residuals_of
#print axioms YMGap.Continuum.DiffJTPFinal.final_Kt
#print axioms YMGap.Continuum.DiffJTPFinal.diffJTPFinal
