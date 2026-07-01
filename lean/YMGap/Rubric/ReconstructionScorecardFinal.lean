/-
The FINAL RECONSTRUCTION / OS SCORECARD — one honest status record that CONSUMES
every newly-discharged reconstruction witness (never re-postulates it) and names,
in one place, EXACTLY the cores that remain open.

# What this module is (read first)

Over several rounds the continuum program discharged a family of witnesses about
the concrete excited-tower transfer object and the OS reconstruction data.  This
module is the single downstream CONSUMER that assembles them into ONE record,
`ReconstructionStatus`, whose every field is an ACTUAL discharge term (never
`True`, never a vacuous predicate), and then names the residual frontier as a
handful of deliberately-uninhabited `Type`-level tokens.

## PROVED-UNCONDITIONAL green fields (each a re-export of a real theorem)

  * `provedLine` — the six-field `ReconstructionProvedLine` bundle: the strictly
    positive mass gap `Δ = −log sep > 0` UNCONDITIONAL in the separator
    (`mass_gap_hamiltonian_all`); the completion vector-space + scalar action
    `cSmul` (`SmulGNSData.vectorScalingResidual`); the located spectrum-infimum
    residual (`spectrumInfResidual`) and its LOWER bound made unconditional by
    feeding the genuine `ArtanhMonotone` witnesses `yOfMonotone` /
    `artanhMonotoneWindow`; the invertible order-4 `O(4)` rotation automorphism
    `rot4` (two-sided inverse, order exactly 4); the uniform-in-coupling survival
    surrogate floor.
  * `rcScaleClosed` — the `RC`-by-`Q'` scaling residual is CLOSED
    (`RCScaleClose.rcScaleResidualPlus`): `RCscale s = ofQ' s · (·)` with
    nonnegative-scalar monotonicity and the scale-over-finite-sum law.
  * `o4Restored` — the physical-model `O(4)` rotation-breaking coefficient
    genuinely CONVERGES to `0` (`O4BetaSign.o4_restored_of_tauModel`), fired from
    the reciprocal asymptotic-freedom trajectory with NO posited `betaDrop`.
  * `betaDropDerived` — the `CouplingRunning` whose `betaDrop` is DERIVED from
    trajectory antitonicity via `couplingRunningOfTrajectory` (the posited sign
    field replaced by a proved consequence).
  * `loopyRealLineDecay` — a GENUINE inhabitant of `LoopyCorrelatorResidual` for
    the single-cycle geometry (`CycleMayer.loopyResidual_singleCycle`): the REAL
    cyclic Wilson correlator obeys geometric real-line decay
    `cycleG ≤ (ofNat M)·ρ^L`, `ρ = 2·gw³ < 1`, PROVED.

## OPEN cores (NAMED, uninhabited `Type`-level tokens)

  * `OpenNode1FiniteSMargin` — node ①, the finite-`s` truncated theta-floor
    margin (`AcNReserveAnalytic.FiniteSMargin`), a uniform steepest-descent
    saddle remainder `≥ 0`.
  * `OpenTrueMargin` — the genuine dimensionless physical margin recursion
    `Δ_k = m_lat(a_k)/a_k` (`UniformCouplingFromAF.TrueMarginRecursion`),
    DISTINCT from the survival-product surrogate.
  * `OpenPhysicalWilsonBridge` — the PHYSICAL Wilson double-Haar / Peter–Weyl
    character-diagonalization inside the physical `cinner`
    (`WilsonSpectralBridge.CharacterDiagResolution`); the concrete char-diagonal
    instance is discharged (`WilsonSchurIdentities.wilsonSchurFormGap`), but the
    interacting finite-volume moment functional is NOT that instance.
  * `OpenBoundedHamiltonian` — the bounded self-adjoint additive `H` with
    `e^{−H} = T` (`BoundedFunctionalCalculusResidual`), the single irreducibly
    hard operator-theoretic node.
  * `OpenContinuumMinlos` — the cited-classical `a → 0` Minlos σ-additive lift
    (`ClayScorecard.ClayContinuumExistence`).

# Honesty (AGENTS.md Rules 1, 6, 8)

Every green field is a genuine discharge term of an already-proved theorem; NO
field is `True` or a vacuous predicate.  Every open token is `Type`-level data
with NO inhabitant here and is NOT trivially provable.  The combined frontier
`ReconstructionOpenFrontier` is provided with NO inhabitant — inhabiting it
WITHOUT `sorry` / `axiom` / `Prop := True` is exactly the open continuum
Yang–Mills reconstruction problem.  This module only WIRES already-proved terms;
its axiom footprint is `[propext]` / `[propext, Quot.sound]`.  Underclaim: the
Clay problem remains OPEN.
-/

import YMGap.Rubric.ReconstructionScorecard
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.O4BetaSign
import YMGap.Continuum.CycleMayer
import YMGap.Continuum.AcNReserveAnalytic

namespace YMGap.Rubric.ReconstructionScorecardFinal

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.HamiltonianSpectrumInf
open YMGap.Continuum.WilsonSpectralBridge
open YMGap.Rubric

/-! ## 1. `ReconstructionStatus` — the single PROVED-UNCONDITIONAL record

CONCRETE about the named excited-tower transfer object `excG op w hw0 hw1 N`.
Every field is an actual discharge term of an already-proved theorem, consuming
the newly-discharged witnesses rather than re-postulating them. -/

/-- **The single honest reconstruction/OS status record.**  All fields are
PROVED-UNCONDITIONAL (at fixed lattice spacing); each is a re-export of a genuine
theorem. -/
structure ReconstructionStatus
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w)
    (N : Nat) : Type where
  /-- (1–6) the six-field proved-unconditional line: mass gap `Δ = −log sep > 0`
  (unconditional in sep), GNS vector-space + scalar action, located spectrum-inf
  and its unconditional lower bound (`ArtanhMonotone` witnesses fed), invertible
  order-4 `O(4)` automorphism, uniform-in-coupling surrogate floor. -/
  provedLine : ReconstructionScorecard.ReconstructionProvedLine D op w hw0 hw1 hwpos N
  /-- (7) the `RC`-by-`Q'` scaling residual, CLOSED (`rcScaleResidualPlus`). -/
  rcScaleClosed : RCScaleResidualPlus
  /-- (8) the physical-model `O(4)` rotation-breaking coefficient CONVERGES to 0,
  fired from the reciprocal AF trajectory with no posited `betaDrop`. -/
  o4Restored :
    O4RestorationAF.RotationRestored
      (O4RestorationProgress.scalingDimensionDecay_of_flow
        (O4RestorationProgress.flowOfCoupling O4BetaSign.tauModelRunning))
  /-- (9) the `CouplingRunning` whose `betaDrop` is DERIVED (not posited), via
  `couplingRunningOfTrajectory` from trajectory antitonicity. -/
  betaDropDerived : O4RestorationProgress.CouplingRunning
  /-- (10) genuine geometric real-line decay of the REAL cyclic Wilson correlator
  (`loopyResidual_singleCycle`). -/
  loopyRealLineDecay : MultiPlaquetteMayer.LoopyCorrelatorResidual GenuineKP.gw

/-- **The status record, INHABITED** for ANY excited-tower transfer object.  Every
field consumes an already-proved witness; nothing is re-proved. -/
def reconstruction_status
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w)
    (N : Nat) :
    ReconstructionStatus D op w hw0 hw1 hwpos N where
  provedLine := ReconstructionScorecard.reconstruction_proved_line D op w hw0 hw1 hwpos N
  rcScaleClosed := RCScaleClose.rcScaleResidualPlus
  o4Restored := O4BetaSign.o4_restored_of_tauModel
  betaDropDerived := O4BetaSign.tauModelRunning
  loopyRealLineDecay := CycleMayer.loopyResidual_singleCycle 0

/-! ## 2. The OPEN residual tokens (uninhabited here — NO inhabitant provided) -/

/-- **OPEN — node ①.**  The finite-`s` truncated theta-floor margin (a uniform
steepest-descent saddle remainder `≥ 0`). -/
abbrev OpenNode1FiniteSMargin (w : Q') : Type := AcNReserveAnalytic.FiniteSMargin w

/-- **OPEN.**  The genuine dimensionless physical margin recursion
`Δ_k = m_lat(a_k)/a_k` — DISTINCT from the survival-product surrogate. -/
abbrev OpenTrueMargin : Type := ReconstructionScorecard.OpenTrueMargin

/-- **OPEN.**  The PHYSICAL Wilson double-Haar / Peter–Weyl character
diagonalization inside the physical inner product (the concrete char-diagonal
instance is discharged; the interacting functional is not that instance). -/
abbrev OpenPhysicalWilsonBridge
    (D : SmulGNSData) (op : TransferOperator D.toGNSData.gnsComplete)
    (w : Q') (N : Nat) : Type :=
  WilsonSpectralBridge.CharacterDiagResolution op RCScaleClose.rcScaleResidualPlus w N

/-- **OPEN.**  The bounded self-adjoint additive Hamiltonian `H` with `e^{−H}=T`
— the single irreducibly hard operator-theoretic node. -/
abbrev OpenBoundedHamiltonian
    (D : SmulGNSData) (op : TransferOperator D.toGNSData.gnsComplete)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (L : AdditiveTransferOperator D.toGNSData) : Type :=
  BoundedFunctionalCalculusResidual (excG op w hw0 hw1 N) L

/-- **OPEN.**  The cited-classical `a → 0` Minlos σ-additive continuum-measure
lift (OS reconstruction with tightness). -/
abbrev OpenContinuumMinlos : Type := ReconstructionScorecard.OpenContinuumMeasure

/-! ## 3. `ReconstructionOpenFrontier` — DELIBERATELY UNINHABITED

Bundles the PROVED status with the five remaining OPEN cores.  A
`reconstruction_status` term IS provided (above); NO `ReconstructionOpenFrontier`
term is.  Inhabiting this WITHOUT `sorry` / `axiom` / a vacuous `Prop := True`
field requires genuine inhabitants of all five open tokens, none of which this
development possesses. -/
structure ReconstructionOpenFrontier
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (L : AdditiveTransferOperator D.toGNSData)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w)
    (N : Nat) : Type where
  /-- the PROVED-UNCONDITIONAL status. -/
  status : ReconstructionStatus D op w hw0 hw1 hwpos N
  /-- OPEN node ①. -/
  node1 : OpenNode1FiniteSMargin w
  /-- OPEN: the genuine dimensionless physical margin. -/
  trueMargin : OpenTrueMargin
  /-- OPEN: the physical Wilson double-Haar bridge. -/
  physicalWilsonBridge : OpenPhysicalWilsonBridge D op w N
  /-- OPEN: the bounded functional-calculus Hamiltonian `H = −log T`. -/
  boundedH : OpenBoundedHamiltonian D op w hw0 hw1 N L
  /-- OPEN: the cited-classical continuum Minlos measure. -/
  continuumMinlos : OpenContinuumMinlos

/-! ## 4. The capstone — a fully concrete inhabited status (unconditional fields only)

`statusW = gw = 1/6` (the strong-coupling heat weight); the transfer object is the
identity additive transfer on the weighted GNS completion.  The capstone bundles
ONLY the PROVED-UNCONDITIONAL fields — no open token appears. -/

/-- The concrete weight `gw = 1/6`. -/
def statusW : Q' := GenuineKP.gw

theorem statusW_nonneg : (0 : Q') ≤ statusW := by decide
theorem statusW_lt_one : statusW < (1 : Q') := by decide
theorem statusW_pos : (0 : Q') < statusW := by decide

/-- **CAPSTONE — the reconstruction/OS status is INHABITED, unconditionally.**
A fully concrete `ReconstructionStatus` over the weighted GNS completion at
`w = gw`, bundling only the PROVED-UNCONDITIONAL fields (mass gap `Δ = −log sep`,
GNS scalar action, located spectrum-inf, invertible `O(4)` automorphism + physical
`O(4)` convergence with derived `betaDrop`, uniform-in-coupling surrogate, closed
`RC`-scaling, real-line loopy decay).  No open token is consumed. -/
def all_fixed_spacing_reconstruction_proved :
    ReconstructionStatus (qSmulGNS statusW statusW_nonneg)
      ((qSmulGNS statusW statusW_nonneg).toGNSData.idTransfer)
      statusW statusW_nonneg statusW_lt_one statusW_pos 1 :=
  reconstruction_status (qSmulGNS statusW statusW_nonneg)
    ((qSmulGNS statusW statusW_nonneg).toGNSData.idTransfer)
    statusW statusW_nonneg statusW_lt_one statusW_pos 1

/-! ## 5. Documentation: PROVED-UNCONDITIONAL vs OPEN (AGENTS.md Rule 6)

PROVED-UNCONDITIONAL (green fields of `ReconstructionStatus`, each a real theorem):

  * `provedLine`         ⟸ `ReconstructionScorecard.reconstruction_proved_line`
      (mass gap `Δ = −log sep > 0`, GNS vector-space + scalar action, located
      spectrum-inf + unconditional lower bound, invertible order-4 `O(4)`
      automorphism, uniform-in-coupling surrogate);
  * `rcScaleClosed`      ⟸ `RCScaleClose.rcScaleResidualPlus`;
  * `o4Restored`         ⟸ `O4BetaSign.o4_restored_of_tauModel`;
  * `betaDropDerived`    ⟸ `O4BetaSign.tauModelRunning`
      (`couplingRunningOfTrajectory`, derived `betaDrop`);
  * `loopyRealLineDecay` ⟸ `CycleMayer.loopyResidual_singleCycle`.

  ⟹ `all_fixed_spacing_reconstruction_proved : ReconstructionStatus …`  [INHABITED].

OPEN (NAMED, NO inhabitant here):

  * `OpenNode1FiniteSMargin` — node ①, the finite-`s` theta-floor saddle margin;
  * `OpenTrueMargin` — the genuine dimensionless physical margin recursion;
  * `OpenPhysicalWilsonBridge` — the physical Wilson double-Haar / Peter–Weyl bridge;
  * `OpenBoundedHamiltonian` — the bounded self-adjoint `H` with `e^{−H}=T`;
  * `OpenContinuumMinlos` — the cited-classical `a → 0` Minlos lift.

  ⟹ `ReconstructionOpenFrontier`  [DELIBERATELY UNINHABITED — the open frontier].

The fixed-spacing reconstruction/OS status is PROVED and consolidated into ONE
inhabited record; the continuum reconstruction target reduces to exactly the five
named open cores.  Inhabiting them is the open Yang–Mills problem; nothing here
claims to have done so. -/

end YMGap.Rubric.ReconstructionScorecardFinal

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Rubric.ReconstructionScorecardFinal.reconstruction_status
#print axioms YMGap.Rubric.ReconstructionScorecardFinal.all_fixed_spacing_reconstruction_proved
