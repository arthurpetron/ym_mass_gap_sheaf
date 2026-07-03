/-
# `DiffJTPWireFinal` — supplying the series side of the Wall-2 capstone unconditionally

`DiffJTPClosed.Wall2OpenCores` carries seven outstanding leaves; the round-5/6
closures make the FIRST TWO (the common `CReal` ϑ₃ limit `F` and the entire
series-side residual `resSer`) into UNCONDITIONAL concrete objects.  This module
*supplies* them, so the mass-gap capstone `final_Kt` (`K_t ≥ 0`) / `diffJTPClosed`
(`DiffJTP`) rests on only the four genuinely-open PRODUCT-side leaves.

## What is supplied unconditionally (drops out of the ledger)

* **`thetaF`** (leaf 1) — the common `CReal` ϑ₃ limit, realised as the
  Chebyshev-`T` limit `ThetaPtwiseTotalizerClose.chebTConv` over the UNCONDITIONAL
  total per-point geometric majorant `TotalMajorantClose.totalMajorant` (on- AND
  off-box, Gauss-beats-exp).

* **`seriesResidual`** (leaf 2) — the `F`-entangled series-side residual
  `ThetaSeriesFieldsClose.ThetaSeriesResidual`, assembled from:
    - `pt := TotalMajorantClose.thetaPtwiseData` (the two `F`-entangled pointwise
      theta limits `ptθ`/`ptθh`, UNCONDITIONAL);
    - `d  := ChebTFwdRatioClose.chebTFwdRatioData` (Chain-A forward-`T` Taylor
      engine + base-5 ratio cap, UNCONDITIONAL on the box);
    - `sm := ChebTFwdBoundClose.fwdSummable_of_data` (Chain-B Gaussian-beats-poly
      summability, UNCONDITIONAL);
  with the cleared finite-difference `fdbound` fired through the CLOSED
  `ThetaSeriesC1Close.fdbound_holds` (`delStar ε' = min(½, ε'/Csum)`, `mStar = 0`).

## What remains OPEN — the four product-side leaves (`Wall2ProductCores`)

Carried against the concrete `F = thetaF`, `fk = jFac a`, `dk = amp+amp`:

1. `Hpt : PtwiseProdData (thetaF …) fk` — undifferentiated JTP (finite Jacobi
   products → `F`, uniform in point).  No producer.
2. `Hin : ProdSecondDiffInputs fk dk x B` — the `M`-uniform Leibniz recursion
   `hstep` + supersolution `hsuper` (per-factor second difference is CLOSED by
   `DkProducerClose.jacFdRem_vanishes`; the `M`-uniform head is not produced).
3. `P : ProdLimitConv fk dk x` + `Lfac : LProductFactor … P` — the driver
   interchange/modulus half + the product-form factorisation.
4. `hCoeff : CoeffHalfIdentity … Lfac.A` — THE FRONTIER (`A ≈ ½·S`, content-equal
   to `DiffJTP`-minus-interchange).

`diffJTPWireFinal` repackages the supplied series side with the four carried
product leaves into `DiffJTPClosed.Wall2OpenCores`; `final_Kt'`/`diffJTPClosed'`
then fire the already-green downstream verbatim.

## Honesty (AGENTS.md Rule 6)

* The series side is FULLY discharged and off the ledger.  The capstone here is
  CONDITIONAL on `Wall2ProductCores` (the four product leaves); it is NOT
  unconditional.  No declaration asserts `final_Kt`/`diffJTPClosed` free of them.
* `final_Kt'` is the honest analytic payload; `diffJTPClosed'` RE-EXPRESSES the
  interchange (leaf `hCoeff` is content-equal to `DiffJTP`).
* All fields of `Wall2ProductCores` are named `Type`/`Prop`-obligations, never
  `sorry`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.
-/

import YMGap.Continuum.DiffJTPClosed
import YMGap.Continuum.TotalMajorantClose
import YMGap.Continuum.ThetaPtwiseTotalizerClose
import YMGap.Continuum.ChebTFwdRatioClose
import YMGap.Continuum.ChebTFwdBoundClose
import YMGap.Continuum.ThetaSeriesC1Close
import YMGap.Continuum.ThetaSeriesFieldsClose
import YMGap.Continuum.ProdSecondDiffClose
import YMGap.Continuum.HdconvClose
import YMGap.Continuum.HdconvReroute
import YMGap.Continuum.ThetaProdDprodClose

namespace YMGap.Continuum.DiffJTPWireFinal

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. The series side, supplied unconditionally -/

/-- **`thetaF` — the common `CReal` ϑ₃ limit (leaf 1), UNCONDITIONAL.**  The
Chebyshev-`T` convergent limit over the total per-point geometric majorant
`TotalMajorantClose.totalMajorant` (valid on AND off the box `[−1,1]`). -/
def thetaF {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) : Q' → CReal :=
  ThetaPtwiseTotalizerClose.chebTConv ha0 ha1 (TotalMajorantClose.totalMajorant ha0 ha1)

/-- **`seriesResidual` — the series-side residual (leaf 2), UNCONDITIONAL.**  The
`F`-entangled `ThetaSeriesResidual` over `F = thetaF`, with `ptθ`/`ptθh` from the
assembled `thetaPtwiseData`, and the cleared `fdbound` from `fdbound_holds` fed by
the Chain-A forward-`T` engine (`chebTFwdRatioData`) and the Chain-B summability
(`fwdSummable_of_data`).  All three inputs are UNCONDITIONAL. -/
def seriesResidual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    ThetaSeriesFieldsClose.ThetaSeriesResidual ha0 ha1 hx hx1 (thetaF ha0 ha1) :=
  let pt := TotalMajorantClose.thetaPtwiseData (x := x) ha0 ha1
  let d  := ChebTFwdRatioClose.chebTFwdRatioData x hx1 hx
  let sm := ChebTFwdBoundClose.fwdSummable_of_data ha0 ha1 d
  { ptθ := pt.ptθ
    ptθh := pt.ptθh
    delStar := fun ε' => Q'.min' HalfPow.half (HKConv.divPos ε' sm.Csum)
    delStar_pos := fun _ε' hε' =>
      ThetaSeriesC1Close.min'_pos ThetaSeriesC1Close.half_pos
        (HKConv.divPos_pos (CReal.num_pos_of_pos hε'))
    mStar := fun _ => 0
    fdbound := fun ε' hε' M _ h hpos hle =>
      ThetaSeriesC1Close.fdbound_holds ha0 d.fb sm ε' hε' M (Nat.zero_le M) h hpos hle }

/-! ## 2. The slimmed product-cores bundle (the four genuinely-open leaves) -/

/-- **`Wall2ProductCores` — the four remaining PRODUCT-side leaves.**  Stated
against the concrete supplied `F := thetaF`.  Inhabit it and `K_t ≥ 0`
(`final_Kt'`) and `DiffJTP` (`diffJTPClosed'`) follow with no further analysis. -/
structure Wall2ProductCores {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Type where
  /-- The `Q'`-level per-factor Jacobi factor family (`jFac a`). -/
  fk : Nat → Q' → Q'
  /-- The `Q'`-level per-factor Jacobi derivative-value family (`amp a + amp a`). -/
  dk : Nat → Q'
  /-- The `M`-independent quadratic prefactor. -/
  B : Q'
  /-- R1: uniform-in-point convergence of the lifted finite products to `thetaF`. -/
  Hpt : ThetaProdDprodClose.PtwiseProdData (thetaF ha0 ha1) fk
  /-- R2: the per-step Leibniz recursion + supersolution budget (the per-factor
  second difference is CLOSED by `DkProducerClose.jacFdRem_vanishes`). -/
  Hin : ProdSecondDiffClose.ProdSecondDiffInputs fk dk x B
  /-- R3a: the log-derivative prod-limit CReal `L` with its explicit-modulus
  convergence (the driver interchange half). -/
  P : HdconvClose.ProdLimitConv fk dk x
  /-- R3b: the factorisation `P.L ≈ Θ·A`, `A = (−sin2θ)·S'`. -/
  Lfac : HdconvReroute.LProductFactor ha0 ha1 hx hx1 P
  /-- R4 — THE FRONTIER: the coefficient identity `A ≈ ½·S`
  (= `DiffJTP`-minus-interchange). -/
  hCoeff : HdconvReroute.CoeffHalfIdentity ha0 ha1 hx hx1 Lfac.A

/-! ## 3. The wire: supply the series side, forward the product leaves -/

/-- **`diffJTPWireFinal` — the capstone bundle with the series side supplied.**
Repackages `Wall2ProductCores` into `DiffJTPClosed.Wall2OpenCores` with the two
series-side leaves (`F`, `resSer`) discharged unconditionally, forwarding the eight
remaining product fields verbatim. -/
def diffJTPWireFinal {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2ProductCores ha0 ha1 hx hx1) :
    DiffJTPClosed.Wall2OpenCores ha0 ha1 hx hx1 :=
  { F := thetaF ha0 ha1
    resSer := seriesResidual ha0 ha1 hx hx1
    fk := W.fk
    dk := W.dk
    B := W.B
    Hpt := W.Hpt
    Hin := W.Hin
    P := W.P
    Lfac := W.Lfac
    hCoeff := W.hCoeff }

/-! ## 4. The firings (pure wiring over the already-green downstream) -/

/-- **`final_Kt'` — the honest analytic capstone `K_t ≥ 0`.**  From the four
product-side leaves (the series side supplied), the heat-kernel series
`K_t = dSeriesCReal ≥ 0` fires through the CLOSED `DiffJTPClosed.final_Kt`. -/
theorem final_Kt' {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2ProductCores ha0 ha1 hx hx1) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  DiffJTPClosed.final_Kt ha0 ha1 hx hx1 (diffJTPWireFinal ha0 ha1 hx hx1 W)

/-- **`diffJTPClosed'` — the differentiated Jacobi-triple-product identity
`DiffJTP`.**  Fired from the SAME product-cores bundle via the CLOSED
`DiffJTPClosed.diffJTPClosed`.

HONESTY (Rule 6): `W.hCoeff : CoeffHalfIdentity` is content-equal to
`DiffJTP`-minus-interchange, so this RE-EXPRESSES the interchange rather than
discharging it.  `final_Kt'` is the honest payload; `hCoeff` is the frontier. -/
theorem diffJTPClosed' {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2ProductCores ha0 ha1 hx hx1) :
    JTPIdentity.DiffJTP ha0 ha1 hx hx1 :=
  DiffJTPClosed.diffJTPClosed ha0 ha1 hx hx1 (diffJTPWireFinal ha0 ha1 hx hx1 W)

end YMGap.Continuum.DiffJTPWireFinal

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `native_decide`, no `sorry`, no custom axiom.  The fields of
`Wall2ProductCores` are named `Type`/`Prop`-obligations, NOT `sorry`. -/

#print axioms YMGap.Continuum.DiffJTPWireFinal.thetaF
#print axioms YMGap.Continuum.DiffJTPWireFinal.seriesResidual
#print axioms YMGap.Continuum.DiffJTPWireFinal.diffJTPWireFinal
#print axioms YMGap.Continuum.DiffJTPWireFinal.final_Kt'
#print axioms YMGap.Continuum.DiffJTPWireFinal.diffJTPClosed'
