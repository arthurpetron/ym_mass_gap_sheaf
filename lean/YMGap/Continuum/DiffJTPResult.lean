/-
# `DiffJTPResult` — the honest consolidated Wall-2 verdict, with the R2 type-bug REPAIRED

This module is the final-assembly consolidation of the Wall-2 (`DiffJTP` / `K_t ≥ 0`)
capstone.  It does two things, both honest:

1. **Repairs the blocking R2 type bug WITHOUT editing the upstream files.**
   `DiffJTPClosed.Wall2ProductCores.Hin` (and `Wall2OpenCores.Hin`) is typed
   `ProdSecondDiffClose.ProdSecondDiffInputs fk dk x B`, whose flat supersolution
   field `hsuper` (`g_M·(B·h²) + F_M h ≤ B·h²`) is **provably unsatisfiable** for the
   Jacobi head `g_M = |fk M x| + |dk M| ≥ 1` (forces `c_M ≤ (1−g_M)·B < 0 ≤ c_M`).
   The satisfiable object is `ProdSecondDiffInputsClose.ProdSecondDiffRunningInputs`
   (a monotone RUNNING cap `B_M`, no upper bound on `g_M`), consumed by the CLOSED
   `prodSecondDiffOfRunning : ProdSecondDiffRunningInputs → ProdSecondDiffResidual`.
   We re-type the R2 leaf to `ProdSecondDiffRunningInputs` and rewire the residual
   producer from `prodSecondDiffOfFactors` (which demanded the unsatisfiable type) to
   `prodSecondDiffOfRunning`.  Everything downstream (`prodC1InputsFlat`, the flat
   modulus, the two C¹-limit engines, the `K_t ≥ 0` firing) is untouched and reused
   verbatim.

2. **States the capstone over the repaired, now-inhabitable bundle**, conditional on
   the honest remaining residual set, and reports the axiom gate clean.

## The repaired open-core bundle (`Wall2ProductRunningCores`)

Over the concrete series side supplied unconditionally by `DiffJTPWireFinal`
(`thetaF` = the common ϑ₃ `CReal` limit, `seriesResidual` = the discharged series
residual), the remaining PRODUCT-side leaves are, with the R2 fix:

* `Hpt`  (R1) — uniform-in-point convergence of the lifted finite products to `thetaF`
  (`PtwiseProdData`).  Genuine open value-level input.
* `Hin`  (R2, **REPAIRED**) — the running-cap per-step Leibniz bundle
  `ProdSecondDiffRunningInputs`.  Now inhabitable: its two residual fields are `hstep`
  (dischargeable by `ProdSecondDiffInputsClose.hstep_of_vanishing` ←
  `DkProducerClose.jacFdRem_vanishes`) and `hBrun_le` (the elementary geometric-`q²`
  running-cap finiteness).  No unsatisfiable `hsuper`.
* `P` + `Lfac` (R3) — the log-derivative prod-limit `CReal` `P.L` with its
  explicit-modulus convergence, and the factorisation `P.L ≈ Θ·A`.
* `hCoeff` (R4) — THE FRONTIER: the coefficient identity `A ≈ ½·S`
  (`CoeffHalfIdentity`), content-equal to `DiffJTP`-minus-interchange.

## What is DELIVERED (genuine content)

* `Wall2ProductRunningCores` — the R2-repaired cores structure (Hin re-typed to the
  satisfiable running-cap bundle).
* `runningResidual_of_cores` — fires the CLOSED `prodSecondDiffOfRunning` to turn the
  running-cap Hin into the `ProdSecondDiffResidual` the flat modulus consumes.  THIS
  is the concrete R2 repair: it typechecks (the old `prodSecondDiffOfFactors` path
  could never be applied because its argument type had no inhabitant).
* `wall2Round2_of_runningCores` — collapses the repaired bundle to the upstream
  `DiffJTPClose.Wall2Round2Residuals`, reusing `DiffJTPClosed.prodC1InputsFlat` and
  `HdconvReroute.hdconv_of_factor_coeff` verbatim.
* `final_Kt_running` / `diffJTPClosed_running` — `K_t ≥ 0` and `DiffJTP`, fired from
  the repaired bundle through the CLOSED `DiffJTPClose.diffJTPClose` /
  `diffJTP_of_round2`.

## HONESTY (AGENTS.md Rule 6) — this does NOT close `DiffJTP`

`final_Kt_running` / `diffJTPClosed_running` are CONDITIONAL on
`Wall2ProductRunningCores`; that bundle is NOT inhabited in-tree.  The residual set is

    { R1 `Hpt` (value-level JTP), R2 `Hin.hstep` + `Hin.hBrun_le`,
      R3 `P` + `Lfac`, R4 `hCoeff` (the C¹ interchange frontier) },

which is NON-EMPTY.  `K_t ≥ 0` is NOT unconditional here.  The genuine advance over
`DiffJTPWireFinal` is strictly the R2 repair: the capstone now rests on a bundle whose
R2 leaf is TYPE-SATISFIABLE (the running cap), removing the blocking type bug that made
`Wall2ProductCores` uninhabitable.  `hCoeff` remains the single irreducible frontier.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  The fields of `Wall2ProductRunningCores` are named
`Type`/`Prop`-obligations, never `sorry`.
-/

import YMGap.Continuum.DiffJTPWireFinal
import YMGap.Continuum.DiffJTPClose
import YMGap.Continuum.ProdSecondDiffInputsClose
import YMGap.Continuum.ThetaSeriesFieldsClose
import YMGap.Continuum.HdconvClose
import YMGap.Continuum.HdconvReroute
import YMGap.Continuum.DiffProduct
import YMGap.Continuum.FiniteProductFDDeriv

namespace YMGap.Continuum.DiffJTPResult

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. The R2-repaired open-core bundle -/

/-- **`Wall2ProductRunningCores` — the four remaining PRODUCT-side leaves, with R2
REPAIRED.**  Identical to `DiffJTPWireFinal.Wall2ProductCores` except the R2 leaf
`Hin` is re-typed from the UNSATISFIABLE `ProdSecondDiffClose.ProdSecondDiffInputs`
(flat supersolution `hsuper` forces `c_M < 0 ≤ c_M` for the Jacobi head `g_M ≥ 1`) to
the SATISFIABLE `ProdSecondDiffInputsClose.ProdSecondDiffRunningInputs` (monotone
running cap, no upper bound on `g_M`).  Stated against the concrete supplied
`F := thetaF`.  Inhabit it and `K_t ≥ 0` / `DiffJTP` follow with no further analysis. -/
structure Wall2ProductRunningCores {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Type where
  /-- The `Q'`-level per-factor Jacobi factor family (`jFac a`). -/
  fk : Nat → Q' → Q'
  /-- The `Q'`-level per-factor Jacobi derivative-value family (`amp a + amp a`). -/
  dk : Nat → Q'
  /-- The `M`-independent quadratic prefactor. -/
  B : Q'
  /-- R1: uniform-in-point convergence of the lifted finite products to `thetaF`. -/
  Hpt : ThetaProdDprodClose.PtwiseProdData (DiffJTPWireFinal.thetaF ha0 ha1) fk
  /-- R2 (**REPAIRED**): the per-step Leibniz recursion + RUNNING-cap budget.  Its two
  residual fields are `hstep` (dischargeable by `hstep_of_vanishing`) and `hBrun_le`
  (geometric running-cap finiteness).  No unsatisfiable flat `hsuper`. -/
  Hin : ProdSecondDiffInputsClose.ProdSecondDiffRunningInputs fk dk x B
  /-- R3a: the log-derivative prod-limit CReal `L` with its explicit-modulus
  convergence (the driver interchange half). -/
  P : HdconvClose.ProdLimitConv fk dk x
  /-- R3b: the factorisation `P.L ≈ Θ·A`, `A = (−sin2θ)·S'`. -/
  Lfac : HdconvReroute.LProductFactor ha0 ha1 hx hx1 P
  /-- R4 — THE FRONTIER: the coefficient identity `A ≈ ½·S`
  (= `DiffJTP`-minus-interchange). -/
  hCoeff : HdconvReroute.CoeffHalfIdentity ha0 ha1 hx hx1 Lfac.A

/-! ## 2. The R2 repair, concretely: the running cap produces the quadratic residual -/

/-- **`runningResidual_of_cores` — the R2 repair.**  Fires the CLOSED running-cap
discrete-Grönwall induction `prodSecondDiffOfRunning` to turn the SATISFIABLE running
Hin into the `ProdSecondDiffResidual` the flat modulus consumes.

This is the concrete fix: the upstream `DiffJTPClosed.residual_of_cores` calls
`prodSecondDiffOfFactors W.Hin` on the unsatisfiable `ProdSecondDiffInputs`, so it can
never be applied to any in-tree term.  The running-cap producer here has a satisfiable
argument type. -/
def runningResidual_of_cores {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2ProductRunningCores ha0 ha1 hx hx1) :
    ProdUnifModulusClose.ProdSecondDiffResidual W.fk W.dk x W.B :=
  ProdSecondDiffInputsClose.prodSecondDiffOfRunning W.Hin

/-! ## 3. Collapse to the upstream round-2 residual bundle (reuses closed engines) -/

/-- **`wall2Round2_of_runningCores` — the repaired bundle → `Wall2Round2Residuals`.**
The series side is `DiffJTPWireFinal.seriesResidual` (supplied unconditionally); the
product side reuses `DiffJTPClosed.prodC1InputsFlat` verbatim, fed the R2-repaired
quadratic residual `runningResidual_of_cores` and the leaf-6 split
`hdconv_of_factor_coeff`.  The ONLY change from `DiffJTPClosed.wall2Round2_of_cores`
is the residual producer (running cap instead of the unsatisfiable flat inputs). -/
def wall2Round2_of_runningCores {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2ProductRunningCores ha0 ha1 hx hx1) :
    DiffJTPClose.Wall2Round2Residuals ha0 ha1 hx hx1 where
  F := DiffJTPWireFinal.thetaF ha0 ha1
  series := ThetaSeriesFieldsClose.thetaSeriesC1Inputs_of_residual ha0 ha1 hx hx1
    (DiffJTPWireFinal.thetaF ha0 ha1) (DiffJTPWireFinal.seriesResidual ha0 ha1 hx hx1)
  prodTrunc := fun M t => CReal.ofQ' (DiffProduct.pre (fun k => W.fk k t) M)
  prodDeriv := fun M => CReal.ofQ' (FiniteProductFDDeriv.prodDeriv W.fk W.dk x M)
  prod := DiffJTPClosed.prodC1InputsFlat ha0 ha1 hx hx1
    (DiffJTPWireFinal.thetaF ha0 ha1) W.fk W.dk
    (runningResidual_of_cores ha0 ha1 hx hx1 W)
    W.Hpt
    (HdconvReroute.hdconv_of_factor_coeff ha0 ha1 hx hx1 W.P W.Lfac W.hCoeff)

/-! ## 4. The firings (pure wiring over the already-green downstream) -/

/-- **`final_Kt_running` — the honest analytic capstone `K_t ≥ 0`.**  From the
R2-repaired product-side bundle (series side supplied), the heat-kernel series
`K_t = dSeriesCReal ≥ 0` fires through the CLOSED `DiffJTPClose.diffJTPClose`.

HONESTY (Rule 6): CONDITIONAL on `Wall2ProductRunningCores`, which is NOT inhabited
in-tree (residual set {Hpt, Hin.hstep+hBrun_le, P+Lfac, hCoeff} is non-empty).  This
is NOT an unconditional `K_t ≥ 0`. -/
theorem final_Kt_running {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2ProductRunningCores ha0 ha1 hx hx1) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  DiffJTPClose.diffJTPClose ha0 ha1 hx hx1 (wall2Round2_of_runningCores ha0 ha1 hx hx1 W)

/-- **`diffJTPClosed_running` — the differentiated Jacobi-triple-product identity
`DiffJTP`.**  Fired from the SAME R2-repaired bundle via the CLOSED
`DiffJTPClose.diffJTP_of_round2`.

HONESTY (Rule 6): `W.hCoeff : CoeffHalfIdentity` is content-equal to
`DiffJTP`-minus-interchange, so this RE-EXPRESSES the interchange rather than
discharging it.  `final_Kt_running` is the honest payload; `hCoeff` is the frontier. -/
theorem diffJTPClosed_running {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (W : Wall2ProductRunningCores ha0 ha1 hx hx1) :
    JTPIdentity.DiffJTP ha0 ha1 hx hx1 :=
  DiffJTPClose.diffJTP_of_round2 ha0 ha1 hx hx1 (wall2Round2_of_runningCores ha0 ha1 hx hx1 W)

end YMGap.Continuum.DiffJTPResult

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `native_decide`, no `sorry`, no custom axiom.  The fields of
`Wall2ProductRunningCores` are named `Type`/`Prop`-obligations (the honest remaining
residual set), NOT `sorry`. -/

#print axioms YMGap.Continuum.DiffJTPResult.runningResidual_of_cores
#print axioms YMGap.Continuum.DiffJTPResult.wall2Round2_of_runningCores
#print axioms YMGap.Continuum.DiffJTPResult.final_Kt_running
#print axioms YMGap.Continuum.DiffJTPResult.diffJTPClosed_running
