/-
# Measure-level expectation comparison for dense physical BF4 stages

The rational diagonal compiler isolates a two-sided comparison of GNS
quadratic forms.  Those forms are themselves expectations of reflected
squares.  On the finite side this is the literal stationary-marginal weighted
sum defining the physical BF4 carrier.  On the continuum side it is the
expectation in the selected OS axiom bundle; `expectationPinned` identifies it
with the Wilson GNS expectation on the same continuum object.

This module proves that convergence of those same-observable expectation
values supplies the rational form comparison and hence every downstream
graph-norm and operator-gap conclusion.  It does not prove expectation
convergence or construct the continuum measure.
-/

import YMGap.Continuum.BF4PhysicalDenseStageRationalComparison

namespace YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalDenseStageRationalComparison
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. The same reflected-square expectation at finite and continuum scale -/

/-- The literal finite physical expectation of the square of the mapped dense
observable.  This is the stationary-marginal sum, not a completed norm. -/
def finiteDenseSquareExpectation
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : Nat -> Nat)
    (stageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (X : SelectedWilsonCauchy D) (scale : Nat) : Q' :=
  centralPhysicalWeightedInner
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (stageObservable scale (X.seq (sampleIndex scale)))
    (stageObservable scale (X.seq (sampleIndex scale)))

/-- The selected continuum OS expectation of the reflected square of the
sampled dense Wilson observable. -/
def continuumDenseSquareExpectation
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : Nat -> Nat)
    (X : SelectedWilsonCauchy D) (scale : Nat) : Q' :=
  H.os_axioms.E.E
    (H.os_axioms.A.mul
      (H.os_axioms.A.star (X.seq (sampleIndex scale)))
      (X.seq (sampleIndex scale)))

/-- The finite rational dense-stage norm is definitionally the finite
stationary-marginal expectation. -/
theorem denseStageNormQ_eq_finiteDenseSquareExpectation
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : Nat -> Nat)
    (stageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (X : SelectedWilsonCauchy D) (scale : Nat) :
    denseStageNormQ D sampleIndex stageObservable X scale =
      finiteDenseSquareExpectation D sampleIndex stageObservable X scale := by
  rfl

/-- The continuum rational dense form is the expectation in the same OS
bundle, using the selected Wilson expectation pin. -/
theorem continuumDenseForm_eq_continuumDenseSquareExpectation
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : Nat -> Nat)
    (X : SelectedWilsonCauchy D) (scale : Nat) :
    D.wilson.toGNSData.B
        (X.seq (sampleIndex scale)) (X.seq (sampleIndex scale)) =
      continuumDenseSquareExpectation D sampleIndex X scale := by
  change D.wilson.E
      (H.os_axioms.A.mul
        (H.os_axioms.A.star (X.seq (sampleIndex scale)))
        (X.seq (sampleIndex scale))) = _
  rw [D.expectationPinned]
  rfl

/-! ## 2. Expectation comparison compiles to the rational frontier -/

/-- Dense-stage data whose analytic limit input is precisely convergence of
the finite stationary-marginal expectation to the same sampled continuum OS
expectation. -/
structure BF4WilsonDenseStageExpectationComparison
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
  expectationComparisonRate : SelectedWilsonCauchy D -> Q' -> Nat
  expectationComparison : forall (X : SelectedWilsonCauchy D)
    (epsilon : Q'), (0 : Q') < epsilon ->
      forall scale : Nat, expectationComparisonRate X epsilon <= scale ->
        finiteDenseSquareExpectation D sampleIndex stageObservable X scale <=
            continuumDenseSquareExpectation D sampleIndex X scale + epsilon /\
        continuumDenseSquareExpectation D sampleIndex X scale <=
            finiteDenseSquareExpectation D sampleIndex stageObservable X scale +
              epsilon

namespace BF4WilsonDenseStageExpectationComparison

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
    (data : BF4WilsonDenseStageExpectationComparison producer D)

/-- The same-object expectation comparison is exactly the rational quadratic-
form comparison required by the preceding compiler. -/
def toRationalComparison :
    BF4WilsonDenseStageRationalComparison producer D where
  toBF4WilsonDenseStageMapData := data.toBF4WilsonDenseStageMapData
  sampleRate := data.sampleRate
  sampleIndex_cofinal := data.sampleIndex_cofinal
  formComparisonRate := data.expectationComparisonRate
  formComparison := by
    intro X epsilon hepsilon scale hscale
    rw [denseStageNormQ_eq_finiteDenseSquareExpectation,
      continuumDenseForm_eq_continuumDenseSquareExpectation]
    exact data.expectationComparison X epsilon hepsilon scale hscale

/-- Measure-level expectation convergence constructs the graph-norm limit. -/
def toLinearGraphNormLimitApproximation :
    BF4WilsonLinearGraphNormLimitApproximation producer D :=
  data.toRationalComparison.toLinearGraphNormLimitApproximation

/-- Measure-level expectation convergence constructs the selected continuum
Wilson operator norm gap. -/
def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  data.toRationalComparison.toWilsonOperatorNormGapPin

end BF4WilsonDenseStageExpectationComparison

end YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison

#print axioms YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison.denseStageNormQ_eq_finiteDenseSquareExpectation
#print axioms YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison.continuumDenseForm_eq_continuumDenseSquareExpectation
#print axioms YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison.BF4WilsonDenseStageExpectationComparison.toRationalComparison
#print axioms YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison.BF4WilsonDenseStageExpectationComparison.toLinearGraphNormLimitApproximation
#print axioms YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison.BF4WilsonDenseStageExpectationComparison.toWilsonOperatorNormGapPin
