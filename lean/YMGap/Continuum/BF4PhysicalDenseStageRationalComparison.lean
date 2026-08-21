/-
# Rational finite-to-continuum comparison for dense physical BF4 stages

The cofinal diagonal compiler asks for eventual closeness between two
`CReal`-valued norm streams.  Both streams at a fixed stage are, however,
generated from literal rational quadratic forms: the finite BF4 form of the
mapped observable and the continuum dense form of the sampled observable.

This module exposes those two rational quantities and proves that an eventual
two-sided rational comparison constructs the complete `CRealEventuallyClose`
record, with inner approximation modulus zero.  It therefore moves the open
analytic frontier from completed-real convergence to the same-observable
rational estimate naturally stated by finite lattice measure arguments.

No such estimate, continuum measure, or dense-stage map is constructed here.
-/

import YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison

namespace YMGap.Continuum.BF4PhysicalDenseStageRationalComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. The rational forms underlying the two norm streams -/

/-- The literal finite BF4 quadratic form of the continuum dense observable
mapped into stage `scale`. -/
def denseStageNormQ
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
  (MatchedPhysicalStageGNSData family coupling scale).B
    (stageObservable scale (X.seq (sampleIndex scale)))
    (stageObservable scale (X.seq (sampleIndex scale)))

/-- Every approximation of the finite completed norm of a constant dense-stage
representative is definitionally its rational finite quadratic form. -/
theorem denseStageNormSequence_approx
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : Nat -> Nat)
    (stageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (X : SelectedWilsonCauchy D) (scale k : Nat) :
    (denseStageNormSequence D sampleIndex stageObservable X scale).approx k =
      denseStageNormQ D sampleIndex stageObservable X scale := by
  rfl

/-- Every approximation of the sampled continuum dense norm is definitionally
the rational continuum quadratic form at the sampled representative. -/
theorem continuumDenseNormSequence_approx
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : Nat -> Nat)
    (X : SelectedWilsonCauchy D) (scale k : Nat) :
    (continuumDenseNormSequence D sampleIndex X scale).approx k =
      D.wilson.toGNSData.B
        (X.seq (sampleIndex scale)) (X.seq (sampleIndex scale)) := by
  rfl

/-! ## 2. Rational diagonal comparison -/

/-- Dense-stage data whose only norm-limit hypothesis is an eventual
same-observable comparison between two rational quadratic forms.

The outer modulus may depend on the continuum representative and tolerance.
There is no inner modulus: both fixed-stage `CReal` norm streams are constant
rational embeddings. -/
structure BF4WilsonDenseStageRationalComparison
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
  formComparisonRate : SelectedWilsonCauchy D -> Q' -> Nat
  formComparison : forall (X : SelectedWilsonCauchy D)
    (epsilon : Q'), (0 : Q') < epsilon ->
      forall scale : Nat, formComparisonRate X epsilon <= scale ->
        denseStageNormQ D sampleIndex stageObservable X scale <=
            D.wilson.toGNSData.B
              (X.seq (sampleIndex scale)) (X.seq (sampleIndex scale)) +
              epsilon /\
        D.wilson.toGNSData.B
              (X.seq (sampleIndex scale)) (X.seq (sampleIndex scale)) <=
            denseStageNormQ D sampleIndex stageObservable X scale + epsilon

namespace BF4WilsonDenseStageRationalComparison

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
    (data : BF4WilsonDenseStageRationalComparison producer D)

/-- A rational same-observable comparison has a zero-cost inner lift to
eventual closeness of the corresponding constructive-real norm streams. -/
def normClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose
      (denseStageNormSequence D data.sampleIndex data.stageObservable X)
      (continuumDenseNormSequence D data.sampleIndex X) where
  stageRate := data.formComparisonRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale k _
    rw [denseStageNormSequence_approx,
      continuumDenseNormSequence_approx]
    exact data.formComparison X epsilon hepsilon scale hscale

/-- Package the rational comparison as the completed-real diagonal comparison
used by the graph-norm compiler. -/
def toDiagonalComparison :
    BF4WilsonDenseStageDiagonalComparison producer D where
  toBF4WilsonDenseStageMapData := data.toBF4WilsonDenseStageMapData
  sampleRate := data.sampleRate
  sampleIndex_cofinal := data.sampleIndex_cofinal
  normClose := data.normClose

/-- Rational finite-to-continuum form comparison constructs the full linear
graph-norm approximation. -/
def toLinearGraphNormLimitApproximation :
    BF4WilsonLinearGraphNormLimitApproximation producer D :=
  data.toDiagonalComparison.toLinearGraphNormLimitApproximation

/-- Rational finite-to-continuum form comparison therefore constructs the
selected continuum Wilson operator norm gap. -/
def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  data.toDiagonalComparison.toWilsonOperatorNormGapPin

end BF4WilsonDenseStageRationalComparison

end YMGap.Continuum.BF4PhysicalDenseStageRationalComparison

#print axioms YMGap.Continuum.BF4PhysicalDenseStageRationalComparison.denseStageNormSequence_approx
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRationalComparison.continuumDenseNormSequence_approx
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRationalComparison.BF4WilsonDenseStageRationalComparison.normClose
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRationalComparison.BF4WilsonDenseStageRationalComparison.toDiagonalComparison
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRationalComparison.BF4WilsonDenseStageRationalComparison.toLinearGraphNormLimitApproximation
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRationalComparison.BF4WilsonDenseStageRationalComparison.toWilsonOperatorNormGapPin
