/-
# Vector-adaptive projective comparison for dense physical BF4 stages

The first projective compiler used one global cofinal sampler for every
completed vector.  That unnecessarily turns a diagonal argument into a
uniformity demand over the entire completion.  Here each `CauchyGNS`
representative carries its own cofinal stage sampler.

The transferred graph-norm leg is proved directly along the sampler belonging
to the original vector.  Hence no choice coherence between the samplers of
`X` and `T X` is needed.  Finite transfer intertwining modulo the physical GNS
radical and the pointwise continuum lift identify the finite transferred norm with the sampled
continuum representative of `T X` at that same index.

The remaining analytic input is now a vectorwise admissible diagonal for the
projective expectation modulus, simultaneously for the sampled observable and
its one-step translate.  No continuum construction or convergence estimate is
asserted by this module.
-/

import YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison

namespace YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageRationalComparison
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovModulusCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.SummableCRealEventualStepVariation
open YMGap.Continuum.WilsonLinearTimeTranslationHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. Vector-adaptive finite and continuum norm streams -/

/-- A finite dense-stage representative using the sampler attached to `X`. -/
def adaptiveDenseStageApproximant
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : SelectedWilsonCauchy D -> Nat -> Nat)
    (stageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (X : SelectedWilsonCauchy D) (scale : Nat) :
    MatchedPhysicalStageCauchy family coupling scale :=
  denseStageApproximant D (sampleIndex X) stageObservable X scale

/-- The finite squared-norm stream along the sampler attached to `X`. -/
def adaptiveDenseStageNormSequence
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : SelectedWilsonCauchy D -> Nat -> Nat)
    (stageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale => matchedPhysicalStageNorm family coupling scale
    (adaptiveDenseStageApproximant D sampleIndex stageObservable X scale)

/-- The finite stationary expectation of the square of one explicitly given
continuum dense observable after realization at `scale`. -/
def finiteStageSquareExpectation
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (stageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (scale : Nat) (observable : D.wilson.toGNSData.V) : Q' :=
  centralPhysicalWeightedInner
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (stageObservable scale observable) (stageObservable scale observable)

/-- The reflected square of one continuum dense Wilson observable. -/
def continuumSquareObservable
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (observable : D.wilson.toGNSData.V) : H.os_axioms.A.carrier :=
  H.os_axioms.A.mul (H.os_axioms.A.star observable) observable

/-- The selected continuum OS expectation of one reflected square. -/
def continuumSquareExpectation
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (observable : D.wilson.toGNSData.V) : Q' :=
  H.os_axioms.E.E (continuumSquareObservable D observable)

/-- Every approximation of an adaptive finite norm is its literal rational
stationary expectation. -/
theorem adaptiveDenseStageNormSequence_approx
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : SelectedWilsonCauchy D -> Nat -> Nat)
    (stageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (X : SelectedWilsonCauchy D) (scale k : Nat) :
    (adaptiveDenseStageNormSequence D sampleIndex stageObservable X scale).approx k =
      finiteStageSquareExpectation D stageObservable scale
        (X.seq (sampleIndex X scale)) := by
  rfl

/-- The continuum GNS diagonal form is the same selected OS reflected-square
expectation. -/
theorem continuumForm_eq_continuumSquareExpectation
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (observable : D.wilson.toGNSData.V) :
    D.wilson.toGNSData.B observable observable =
      continuumSquareExpectation D observable := by
  change D.wilson.E
      (H.os_axioms.A.mul (H.os_axioms.A.star observable) observable) = _
  rw [D.expectationPinned]
  rfl

/-! ## 2. Adaptive projective realization data -/

/-- Dense-stage realization with a separate constructive cofinal diagonal for
each completed representative.

The finite evaluator pin is pointwise in every dense observable.  The single
diagonal-admissibility field controls both that observable and its one-step
translate, which is exactly what graph-norm convergence needs. -/
structure BF4WilsonDenseStageAdaptiveProjectiveComparison
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 3 where
  separatorPinned : D.selectedSpectralData.gap.sep = bf4MacroNormRate
  pointwiseTimeTranslation :
    WilsonPointwiseLinearTimeTranslationPin D.timeTranslation
  sampleIndex : SelectedWilsonCauchy D -> Nat -> Nat
  sampleRate : SelectedWilsonCauchy D -> Nat -> Nat
  sampleIndex_cofinal : forall (X : SelectedWilsonCauchy D)
    (threshold scale : Nat),
      sampleRate X threshold <= scale -> threshold <= sampleIndex X scale
  stageObservable : forall scale : Nat,
    D.wilson.toGNSData.V ->
      (MatchedPhysicalStageGNSData family coupling scale).V
  stageObservable_congr : forall scale : Nat,
    forall {a b : D.wilson.toGNSData.V}, D.wilson.toGNSData.veq a b ->
      (MatchedPhysicalStageGNSData family coupling scale).veq
        (stageObservable scale a) (stageObservable scale b)
  stageTransfer_intertwines : forall (scale : Nat)
    (a : D.wilson.toGNSData.V),
      (MatchedPhysicalStageGNSData family coupling scale).rad
        (centralPhysicalMarkovApply
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (stageObservable scale a))
        (stageObservable scale (D.timeTranslation.tau a))
  stage_vacuumOrthogonal : forall (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      forall scale : Nat,
        CentralPhysicalModulatedVacuumOrthogonal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (matchedPhysicalStagePoint family coupling scale
            (adaptiveDenseStageApproximant D sampleIndex stageObservable X scale))
  rationalFunctional : ProjectiveOSRationalModulus D
  finiteSquarePinned : forall (scale : Nat)
    (observable : D.wilson.toGNSData.V),
      (finiteStageSquareExpectation D stageObservable scale observable).eqv
        (rationalFunctional.stageExpectationQ scale (mu.pick scale)
          (continuumSquareObservable D observable))
  diagonalRate : SelectedWilsonCauchy D -> Q' -> Nat
  diagonal_admissible : forall (X : SelectedWilsonCauchy D)
    (epsilon : Q'), (0 : Q') < epsilon ->
      forall scale : Nat, diagonalRate X epsilon <= scale ->
        let a := X.seq (sampleIndex X scale)
        rationalFunctional.rate (continuumSquareObservable D a) epsilon <= scale /\
        rationalFunctional.rate
          (continuumSquareObservable D (D.timeTranslation.tau a)) epsilon <= scale

namespace BF4WilsonDenseStageAdaptiveProjectiveComparison

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
    (data : BF4WilsonDenseStageAdaptiveProjectiveComparison producer D)

/-- The adaptive finite norm stream is eventually close to the continuum
dense norm sampled along the same vectorwise diagonal. -/
def normClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose
      (adaptiveDenseStageNormSequence D data.sampleIndex data.stageObservable X)
      (continuumDenseNormSequence D (data.sampleIndex X) X) where
  stageRate := data.diagonalRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale k _
    rw [adaptiveDenseStageNormSequence_approx,
      continuumDenseNormSequence_approx]
    let a := X.seq (data.sampleIndex X scale)
    have hadmissible :=
      (data.diagonal_admissible X epsilon hepsilon scale hscale).1
    have hbound := data.rationalFunctional.bound
      (continuumSquareObservable D a) epsilon hepsilon scale hadmissible
    have hleft := data.finiteSquarePinned scale a
    have hright : D.wilson.toGNSData.B a a =
        continuumSquareExpectation D a :=
      continuumForm_eq_continuumSquareExpectation D a
    rw [hright]
    constructor
    · exact le_of_eqv_le hleft hbound.1
    · exact le_of_le_eqv hbound.2
        (Q'.add_eqv_congr_right _ _ epsilon (Q'.eqv_symm hleft))

/-- The adaptive finite norm stream converges to the selected completed norm. -/
theorem norm_converges (X : SelectedWilsonCauchy D) :
    CReal.ConvergesTo
      (adaptiveDenseStageNormSequence D data.sampleIndex data.stageObservable X)
      (D.wilson.toGNSData.cinnerRep X X) :=
  convergesTo_of_eventuallyClose (data.normClose X)
    (continuumDenseNormSequence_converges D
      (data.sampleIndex X) (data.sampleRate X)
      (data.sampleIndex_cofinal X) X)

/-- Every approximation of the transferred adaptive finite norm is the finite
quadratic form of the literal macro-transferred observable. -/
theorem transferredNorm_approx
    (X : SelectedWilsonCauchy D) (scale k : Nat) :
    (matchedPhysicalStageTransferredNorm family coupling scale
      (adaptiveDenseStageApproximant D data.sampleIndex data.stageObservable X scale)).approx k =
      (MatchedPhysicalStageGNSData family coupling scale).B
        (centralPhysicalMarkovApply
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (data.stageObservable scale
            (X.seq (data.sampleIndex X scale))))
        (centralPhysicalMarkovApply
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (data.stageObservable scale
            (X.seq (data.sampleIndex X scale)))) := by
  rfl

/-- The transferred finite stream is eventually close to the continuum norm
of `T X`, sampled along `X`'s own cofinal diagonal. -/
def transferredNormClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose
      (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
        (adaptiveDenseStageApproximant D data.sampleIndex data.stageObservable X scale))
      (continuumDenseNormSequence D (data.sampleIndex X)
        (data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)) where
  stageRate := data.diagonalRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale k _
    rw [data.transferredNorm_approx X scale k,
      continuumDenseNormSequence_approx]
    let a := X.seq (data.sampleIndex X scale)
    let Ta := D.timeTranslation.tau a
    let TX := data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X
    have hadmissible :=
      (data.diagonal_admissible X epsilon hepsilon scale hscale).2
    have hbound := data.rationalFunctional.bound
      (continuumSquareObservable D Ta) epsilon hepsilon scale hadmissible
    have hfiniteTransfer :
        ((MatchedPhysicalStageGNSData family coupling scale).B
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0
            (data.stageObservable scale a))
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0
            (data.stageObservable scale a))).eqv
          (finiteStageSquareExpectation D data.stageObservable scale Ta) := by
      exact Q'.eqv_trans _ _ _
        ((MatchedPhysicalStageGNSData family coupling scale).B_welldef
          (data.stageTransfer_intertwines scale a)
          (data.stageTransfer_intertwines scale a))
        (Q'.eqv_refl _)
    have hleft := Q'.eqv_trans _ _ _ hfiniteTransfer
      (data.finiteSquarePinned scale Ta)
    have hpointwise : D.wilson.toGNSData.veq
        (TX.seq (data.sampleIndex X scale)) Ta :=
      data.pointwiseTimeTranslation.pointwise X (data.sampleIndex X scale)
    have hcontinuumForm :
        (D.wilson.toGNSData.B
          (TX.seq (data.sampleIndex X scale))
          (TX.seq (data.sampleIndex X scale))).eqv
          (continuumSquareExpectation D Ta) :=
      Q'.eqv_trans _ _ _
        (D.wilson.toGNSData.B_diag_congr hpointwise)
        (Q'.eqv_of_eq
          (continuumForm_eq_continuumSquareExpectation D Ta))
    constructor
    · exact le_of_eqv_le hleft
        (le_of_le_eqv hbound.1
          (Q'.add_eqv_congr_right _ _ epsilon
            (Q'.eqv_symm hcontinuumForm)))
    · exact le_of_eqv_le hcontinuumForm
        (le_of_le_eqv hbound.2
          (Q'.add_eqv_congr_right _ _ epsilon
            (Q'.eqv_symm hleft)))

/-- Direct transferred convergence along the original vector's adaptive
diagonal; no equality between the samplers of `X` and `T X` is required. -/
theorem transferredNorm_converges (X : SelectedWilsonCauchy D) :
    CReal.ConvergesTo
      (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
        (adaptiveDenseStageApproximant D data.sampleIndex data.stageObservable X scale))
      (D.wilson.toGNSData.cinnerRep
        (data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)
        (data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)) :=
  convergesTo_of_eventuallyClose (data.transferredNormClose X)
    (continuumDenseNormSequence_converges D
      (data.sampleIndex X) (data.sampleRate X)
      (data.sampleIndex_cofinal X)
      (data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X))

/-- Adaptive projective convergence constructs the graph-norm approximation. -/
def toLinearGraphNormLimitApproximation :
    BF4WilsonLinearGraphNormLimitApproximation producer D where
  separatorPinned := data.separatorPinned
  linearTimeTranslation := data.pointwiseTimeTranslation.linear
  approximant := adaptiveDenseStageApproximant D data.sampleIndex data.stageObservable
  approximant_vacuumOrthogonal := data.stage_vacuumOrthogonal
  norm_converges := data.norm_converges
  transferredNorm_converges := data.transferredNorm_converges

/-- Adaptive projective convergence constructs the selected continuum Wilson
operator norm gap. -/
def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  data.toLinearGraphNormLimitApproximation.toWilsonOperatorNormGapPin

end BF4WilsonDenseStageAdaptiveProjectiveComparison

end YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison

#print axioms YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison.adaptiveDenseStageNormSequence_approx
#print axioms YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison.continuumForm_eq_continuumSquareExpectation
#print axioms YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison.BF4WilsonDenseStageAdaptiveProjectiveComparison.norm_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison.BF4WilsonDenseStageAdaptiveProjectiveComparison.transferredNorm_approx
#print axioms YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison.BF4WilsonDenseStageAdaptiveProjectiveComparison.transferredNormClose
#print axioms YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison.BF4WilsonDenseStageAdaptiveProjectiveComparison.transferredNorm_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison.BF4WilsonDenseStageAdaptiveProjectiveComparison.toLinearGraphNormLimitApproximation
#print axioms YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison.BF4WilsonDenseStageAdaptiveProjectiveComparison.toWilsonOperatorNormGapPin
