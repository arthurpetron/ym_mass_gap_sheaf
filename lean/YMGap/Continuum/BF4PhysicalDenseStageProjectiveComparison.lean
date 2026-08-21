/-
# Projective-functional compiler for dense physical BF4 stages

The measure-level expectation frontier still presents its conclusion as one
diagonal estimate.  This module factors that estimate through the projective
OS functional already selected by the continuum datum.

A rational refinement supplies explicit stage expectation values, identifies
their embeddings with the existing stage functional on the same `mu.pick`
thread, and gives a Type-level convergence modulus for each fixed observable.
The BF4 realization then has two remaining duties: identify its finite
stationary expectation with that rational stage evaluator and provide a
diagonal schedule large enough for the modulus of each sampled reflected
square.

These are still analytic inputs.  The module proves only their constructive
composition into the completed Wilson operator gap.
-/

import YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison

namespace YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. A rational, modulus-carrying refinement of the projective functional -/

/-- Constructive rational semantics for the already-selected projective OS
functional.

`stageFunctionalPinned` keeps the rational evaluator on exactly the same
finite-measure thread as `D.measureLinked.projectiveFunctional`; `rate` and
`bound` refine its propositional convergence by retaining a Type-level stage
modulus. -/
structure ProjectiveOSRationalModulus
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 2 where
  stageExpectationQ : (stage : Nat) -> M stage ->
    H.os_axioms.A.carrier -> Q'
  stageFunctionalPinned : forall (stage : Nat) (measure : M stage)
    (observable : H.os_axioms.A.carrier),
      CReal.Equiv
        (D.measureLinked.stageFunctional.expectationFromStage
          stage measure observable)
        (CReal.ofQ' (stageExpectationQ stage measure observable))
  rate : H.os_axioms.A.carrier -> Q' -> Nat
  bound : forall (observable : H.os_axioms.A.carrier)
    (epsilon : Q'), (0 : Q') < epsilon ->
      forall stage : Nat, rate observable epsilon <= stage ->
        stageExpectationQ stage (mu.pick stage) observable <=
            H.os_axioms.E.E observable + epsilon /\
        H.os_axioms.E.E observable <=
            stageExpectationQ stage (mu.pick stage) observable + epsilon

namespace ProjectiveOSRationalModulus

variable
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : ProjectiveOSRationalModulus D)

/-- The retained rational modulus directly proves convergence of the embedded
rational evaluator to the selected continuum OS expectation. -/
theorem stageExpectationQ_converges
    (observable : H.os_axioms.A.carrier) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        (data.stageExpectationQ stage (mu.pick stage) observable))
      (CReal.ofQ' (H.os_axioms.E.E observable)) := by
  intro epsilon hepsilon
  refine ⟨data.rate observable epsilon, fun stage hstage => ?_⟩
  refine ⟨0, fun k _ => ?_⟩
  simpa using data.bound observable epsilon hepsilon stage hstage

end ProjectiveOSRationalModulus

/-! ## 2. Diagonal realization of the finite BF4 expectation -/

/-- Dense BF4 stage maps linked to the rational refinement of the same
projective continuum functional.

The `diagonal_admissible` field isolates the nontrivial uniformity issue:
pointwise convergence for every fixed observable is not by itself convergence
along a varying diagonal.  The chosen cutoff/sample schedule must eventually
dominate the modulus of its sampled reflected square. -/
structure BF4WilsonDenseStageProjectiveComparison
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    extends BF4WilsonDenseStageMapData producer D where
  sampleRate : Nat -> Nat
  sampleIndex_cofinal : forall threshold scale : Nat,
    sampleRate threshold <= scale -> threshold <= sampleIndex scale
  rationalFunctional : ProjectiveOSRationalModulus D
  /-- Exact identification of the literal finite BF4 stationary expectation
  with the rational evaluator on the selected finite measure. -/
  finiteSquarePinned : forall (X : SelectedWilsonCauchy D) (scale : Nat),
    (finiteDenseSquareExpectation D sampleIndex stageObservable X scale).eqv
      (rationalFunctional.stageExpectationQ scale (mu.pick scale)
        (continuumDenseSquareObservable D sampleIndex X scale))
  diagonalRate : SelectedWilsonCauchy D -> Q' -> Nat
  /-- The diagonal cutoff is large enough for the pointwise projective modulus
  of the reflected square sampled at that same cutoff. -/
  diagonal_admissible : forall (X : SelectedWilsonCauchy D)
    (epsilon : Q'), (0 : Q') < epsilon ->
      forall scale : Nat, diagonalRate X epsilon <= scale ->
        rationalFunctional.rate
          (continuumDenseSquareObservable D sampleIndex X scale) epsilon <=
          scale

namespace BF4WilsonDenseStageProjectiveComparison

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : BF4WilsonDenseStageProjectiveComparison producer D)

/-- The projective modulus, finite-evaluator pin, and admissible diagonal
construct the measure-level expectation comparison. -/
def toExpectationComparison :
    BF4WilsonDenseStageExpectationComparison producer D where
  toBF4WilsonDenseStageMapData := data.toBF4WilsonDenseStageMapData
  sampleRate := data.sampleRate
  sampleIndex_cofinal := data.sampleIndex_cofinal
  expectationComparisonRate := data.diagonalRate
  expectationComparison := by
    intro X epsilon hepsilon scale hscale
    have hbound := data.rationalFunctional.bound
      (continuumDenseSquareObservable D data.sampleIndex X scale)
      epsilon hepsilon scale
      (data.diagonal_admissible X epsilon hepsilon scale hscale)
    constructor
    · exact le_of_eqv_le (data.finiteSquarePinned X scale) hbound.1
    · exact le_of_le_eqv hbound.2
        (Q'.add_eqv_congr_right _ _ epsilon
          (Q'.eqv_symm (data.finiteSquarePinned X scale)))

/-- Projective-functional data and an admissible BF4 diagonal construct the
linear graph-norm limit. -/
def toLinearGraphNormLimitApproximation :
    BF4WilsonLinearGraphNormLimitApproximation producer D :=
  data.toExpectationComparison.toLinearGraphNormLimitApproximation

/-- Projective-functional data and an admissible BF4 diagonal construct the
selected continuum Wilson operator norm gap. -/
def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  data.toExpectationComparison.toWilsonOperatorNormGapPin

end BF4WilsonDenseStageProjectiveComparison

end YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison

#print axioms YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison.ProjectiveOSRationalModulus.stageExpectationQ_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison.BF4WilsonDenseStageProjectiveComparison.toExpectationComparison
#print axioms YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison.BF4WilsonDenseStageProjectiveComparison.toLinearGraphNormLimitApproximation
#print axioms YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison.BF4WilsonDenseStageProjectiveComparison.toWilsonOperatorNormGapPin
