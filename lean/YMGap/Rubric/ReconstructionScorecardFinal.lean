/-
The LEGACY RECONSTRUCTION-STATUS SCORECARD.

This module assembles previously proved algebraic, fixed-spacing, and
finite-model witnesses into `ReconstructionStatus`.  Its fields are genuine Lean
terms at their declared types, but the record is not the canonical physical OS
reconstruction.  In particular it does not supply one two-parameter continuum
Wilson functional, its reflected positive-time quotient, a full strongly
continuous time action, the resulting `C0` semigroup, an unbounded generator, or
an identification of that generator's spectral edge.

The five tokens grouped in `ReconstructionOpenFrontier` are a historical
surrogate census, not an exhaustive Clay frontier.  Two qualifications are
especially important:

  * `OpenBoundedHamiltonian` is the older bounded-log auxiliary.  A generic
    continuum transfer operator may have spectrum accumulating at zero, so
    `-log T` need not be bounded; the physical Hamiltonian is normally treated as
    an unbounded self-adjoint generator of the full time semigroup.  Thus this
    token is not the canonical operator-theoretic target.
  * `OpenContinuumMinlos` is optional sigma-additive measure packaging.  It is not
    required to formulate a Schwinger functional or its reflected OS root.

Other fields, including the encoded `-log sep` margin, model rotation, and
single-cycle decay, retain only the scope of their named surrogate structures.
No theorem here constructs the Yang--Mills continuum mass gap.  The axiom gates
at the end check the declarations actually exported by this legacy scorecard.
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

/-! ## 1. `ReconstructionStatus` — a proved legacy status record

This record is about the named excited-tower transfer surrogate
`excG op w hw0 hw1 N`.  Each field consumes an already-proved witness at its
literal type; the collection is not a canonical reflected-OS construction. -/

/-- A legacy reconstruction-status record.  All fields are proved at the stated
fixed-spacing surrogate types; none by itself pins the model to the continuum
Yang--Mills functional or Hamiltonian. -/
structure ReconstructionStatus
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w)
    (N : Nat) : Type where
  /-- (1–6) the six-field legacy line: the encoded margin
  `Delta = -log sep > 0`, GNS vector-space/scalar-action data, a located
  spectrum-infimum surrogate and lower bound, an invertible order-four model
  automorphism, and a uniform-in-coupling survival floor. -/
  provedLine : ReconstructionScorecard.ReconstructionProvedLine D op w hw0 hw1 hwpos N
  /-- (7) the `RC`-by-`Q'` scaling residual, CLOSED (`rcScaleResidualPlus`). -/
  rcScaleClosed : RCScaleResidualPlus
  /-- (8) the legacy Cauchy predicate for the model rotation-breaking
  coefficient, fired from the reciprocal AF trajectory with no posited
  `betaDrop`.  This field alone does not identify the limit with zero. -/
  o4Restored :
    O4RestorationAF.RotationRestored
      (O4RestorationProgress.scalingDimensionDecay_of_flow
        (O4RestorationProgress.flowOfCoupling O4BetaSign.tauModelRunning))
  /-- (9) the `CouplingRunning` whose `betaDrop` is DERIVED (not posited), via
  `couplingRunningOfTrajectory` from trajectory antitonicity. -/
  betaDropDerived : O4RestorationProgress.CouplingRunning
  /-- (10) geometric real-line decay for the named single-cycle correlator model
  (`loopyResidual_singleCycle`), without a pin to the continuum functional. -/
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

/-! ## 2. Historical residual tokens (uninhabited here) -/

/-- **OPEN — node ①.**  The finite-`s` truncated theta-floor margin (a uniform
steepest-descent saddle remainder `≥ 0`). -/
abbrev OpenNode1FiniteSMargin (w : Q') : Type := AcNReserveAnalytic.FiniteSMargin w

/-- **HISTORICAL OPEN TOKEN.**  The older route's intended dimensionless margin
recursion `Delta_k = m_lat(a_k)/a_k`, distinct from its survival-product
surrogate.  This type is not itself a pin to the canonical generator spectrum. -/
abbrev OpenTrueMargin : Type := ReconstructionScorecard.OpenTrueMargin

/-- **HISTORICAL OPEN TOKEN.**  The older route's proposed Wilson double-Haar /
Peter--Weyl character diagonalization inside its named inner product.  The
concrete character-diagonal instance is detached from the interacting continuum
functional, so this token is not a canonical Wilson-functional bridge. -/
abbrev OpenPhysicalWilsonBridge
    (D : SmulGNSData) (op : TransferOperator D.toGNSData.gnsComplete)
    (w : Q') (N : Nat) : Type :=
  WilsonSpectralBridge.CharacterDiagResolution op RCScaleClose.rcScaleResidualPlus w N

/-- **LEGACY OPEN AUXILIARY.**  A bounded self-adjoint logarithm with
`exp(-H) = T`.  This is not the canonical physical Hamiltonian target: for a
generic continuum transfer operator the spectrum may accumulate at zero, so the
generator `-log T` may be unbounded and must instead be constructed from the
full strongly continuous semigroup. -/
abbrev OpenBoundedHamiltonian
    (D : SmulGNSData) (op : TransferOperator D.toGNSData.gnsComplete)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (L : AdditiveTransferOperator D.toGNSData) : Type :=
  BoundedFunctionalCalculusResidual (excG op w hw0 hw1 N) L

/-- **OPTIONAL LEGACY PACKAGING.**  A sigma-additive Minlos-style continuum
measure lift.  The canonical Schwinger-functional and reflected-OS formulation
does not require this extra measure representation. -/
abbrev OpenContinuumMinlos : Type := ReconstructionScorecard.OpenContinuumMeasure

/-! ## 3. `ReconstructionOpenFrontier` — a historical uninhabited bundle

Bundles the proved status with five residual tokens selected by the older route.
A `reconstruction_status` term is provided above; no
`ReconstructionOpenFrontier` term is provided.  Even an inhabitant would close
only these five encoded obligations: the canonical two-parameter limit,
reflected quotient, full time semigroup, unbounded generator, and spectral pin
are not fields of this structure. -/
structure ReconstructionOpenFrontier
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (L : AdditiveTransferOperator D.toGNSData)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w)
    (N : Nat) : Type where
  /-- The proved legacy status record. -/
  status : ReconstructionStatus D op w hw0 hw1 hwpos N
  /-- OPEN node ①. -/
  node1 : OpenNode1FiniteSMargin w
  /-- Historical dimensionless-margin token. -/
  trueMargin : OpenTrueMargin
  /-- Historical Wilson character-diagonalization bridge token. -/
  physicalWilsonBridge : OpenPhysicalWilsonBridge D op w N
  /-- Legacy bounded-log auxiliary, not the canonical unbounded generator. -/
  boundedH : OpenBoundedHamiltonian D op w hw0 hw1 N L
  /-- Optional sigma-additive Minlos-style measure packaging. -/
  continuumMinlos : OpenContinuumMinlos

/-! ## 4. Legacy surrogate capstone (unconditional fields only)

`statusW = gw = 1/6` (the strong-coupling heat weight); the transfer object is the
identity additive transfer on the ordinary weighted GNS completion.  Thus this
is an inhabited algebraic/status surrogate, not a physical positive-time OS
reconstruction or mass-gap theorem.  It bundles only its stated proved legacy
fields; no open token appears. -/

/-- The concrete weight `gw = 1/6`. -/
def statusW : Q' := GenuineKP.gw

theorem statusW_nonneg : (0 : Q') ≤ statusW := by decide
theorem statusW_lt_one : statusW < (1 : Q') := by decide
theorem statusW_pos : (0 : Q') < statusW := by decide

/-- **LEGACY SURROGATE — the algebraic status is INHABITED, unconditionally.**
A concrete `ReconstructionStatus` over the weighted GNS completion at
`w = gw`, bundling only the stated fields (encoded margin `Delta = -log sep`,
GNS scalar action, located spectrum-inf, an invertible order-four model
automorphism plus the legacy anisotropy-Cauchy predicate with derived `betaDrop`,
uniform-in-coupling surrogate, closed
`RC`-scaling, real-line loopy decay).  Its identity transfer and detached finite
status fields must not be projected into the canonical Clay target.  No open
token is consumed. -/
def all_fixed_spacing_reconstruction_proved :
    ReconstructionStatus (qSmulGNS statusW statusW_nonneg)
      ((qSmulGNS statusW statusW_nonneg).toGNSData.idTransfer)
      statusW statusW_nonneg statusW_lt_one statusW_pos 1 :=
  reconstruction_status (qSmulGNS statusW statusW_nonneg)
    ((qSmulGNS statusW statusW_nonneg).toGNSData.idTransfer)
    statusW statusW_nonneg statusW_lt_one statusW_pos 1

/-! ## 5. Documentation: proved legacy fields and historical residuals

PROVED (fields of `ReconstructionStatus`, at their literal surrogate types):

  * `provedLine`         ⟸ `ReconstructionScorecard.reconstruction_proved_line`
      (encoded `Delta = -log sep > 0`, GNS vector-space/scalar action, located
      spectrum-infimum surrogate and lower bound, invertible order-four model
      automorphism, uniform-in-coupling survival surrogate);
  * `rcScaleClosed`      ⟸ `RCScaleClose.rcScaleResidualPlus`;
  * `o4Restored`         ⟸ `O4BetaSign.o4_restored_of_tauModel`;
  * `betaDropDerived`    ⟸ `O4BetaSign.tauModelRunning`
      (`couplingRunningOfTrajectory`, derived `betaDrop`);
  * `loopyRealLineDecay` ⟸ `CycleMayer.loopyResidual_singleCycle`.

  ⟹ `all_fixed_spacing_reconstruction_proved : ReconstructionStatus …`  [INHABITED].

HISTORICAL RESIDUAL TOKENS (no inhabitant here):

  * `OpenNode1FiniteSMargin` — node ①, the finite-`s` theta-floor saddle margin;
  * `OpenTrueMargin` — the older dimensionless-margin recursion token;
  * `OpenPhysicalWilsonBridge` — the older Wilson character-diagonalization bridge;
  * `OpenBoundedHamiltonian` — the rejected bounded-log auxiliary, not the
    canonical possibly-unbounded semigroup generator;
  * `OpenContinuumMinlos` — optional sigma-additive measure packaging.

  ⟹ `ReconstructionOpenFrontier`  [UNINHABITED — a non-exhaustive legacy bundle].

The fixed-spacing legacy status surrogate is proved and consolidated into one
inhabited record.  It does not construct the standard reflected positive-time
OS carrier.  The five historical open cores listed above are therefore not an
exhaustive Clay frontier: the canonical two-parameter Schwinger limit,
half-space reconstruction, `C0` semigroup, unbounded generator, and spectral
identification are independent prerequisites recorded in the revised work
plan.  Nothing here claims the continuum Yang--Mills result. -/

end YMGap.Rubric.ReconstructionScorecardFinal

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Rubric.ReconstructionScorecardFinal.reconstruction_status
#print axioms YMGap.Rubric.ReconstructionScorecardFinal.all_fixed_spacing_reconstruction_proved
