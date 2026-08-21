/-
# Qualitative vacuum compiler for the physical BF4 slow diagonal

The raw-square/raw-mean compiler previously paid an explicit Type-level rate
for the representative vacuum pairing in order to manufacture one uniform
centered-comparison modulus.  The final graph-norm convergence statement is a
proposition, however, so it may use the existential stage supplied by ordinary
constructive-real convergence without choosing a rate globally.

This module proves that direct route.  Raw square convergence is composed from
the two explicit finite/projective comparison legs.  Raw mean convergence is
composed from those legs and the already-proved qualitative convergence of the
sampled dense vacuum pairing.  Continuity of multiplication and the exact
identity `centered square = raw square - mean^2` then give both graph-norm
limits.  The exact-semantic adapter below constructs the required slow diagonal
from the four projective rates and carries only `WilsonDenseUnitVacuumPin`;
no representative pairing modulus is present in that public route.
-/

import YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison

namespace YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison
open YMGap.Continuum.BF4PhysicalDenseStageRawMomentModulus
open YMGap.Continuum.BF4PhysicalDenseStageRationalComparison
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4PhysicalVacuumGraphNormLimitStability
open YMGap.Continuum.BF4PhysicalVacuumPairingModulus
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

/-- The exact data actually used by the qualitative-vacuum convergence
compiler.  In particular, it carries only the dense-unit vacuum pin and no
representative pairing rate. -/
structure BF4WilsonDenseStageQualitativeBase
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
  rawStageObservable : forall scale : Nat,
    D.wilson.toGNSData.V ->
      (MatchedPhysicalStageGNSData family coupling scale).V
  rawStageTransfer_intertwines : forall (scale : Nat)
    (a : D.wilson.toGNSData.V),
      (MatchedPhysicalStageGNSData family coupling scale).rad
        (centralPhysicalMarkovApply
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (rawStageObservable scale a))
        (rawStageObservable scale (D.timeTranslation.tau a))
  rationalFunctional : ProjectiveOSRationalModulus D
  vacuumPin : WilsonDenseUnitVacuumPin D
  sampleRate : SelectedWilsonCauchy D -> Nat -> Nat
  sampleIndex : SelectedWilsonCauchy D -> Nat -> Nat
  sampleIndex_cofinal : forall (X : SelectedWilsonCauchy D)
    (threshold scale : Nat),
      sampleRate X threshold <= scale -> threshold <= sampleIndex X scale
  projectiveDiagonalRate : SelectedWilsonCauchy D -> Q' -> Nat
  projective_diagonal_admissible : forall (X : SelectedWilsonCauchy D)
    (epsilon : Q'), (0 : Q') < epsilon ->
      forall scale : Nat, projectiveDiagonalRate X epsilon <= scale ->
        let a := X.seq (sampleIndex X scale)
        rationalFunctional.rate (continuumSquareObservable D a) epsilon <=
            scale /\
          rationalFunctional.rate
            (continuumSquareObservable D (D.timeTranslation.tau a)) epsilon <=
              scale
  projective_pairing_diagonal_admissible :
    forall (X : SelectedWilsonCauchy D)
      (epsilon : Q'), (0 : Q') < epsilon ->
        forall scale : Nat, projectiveDiagonalRate X epsilon <= scale ->
          let a := X.seq (sampleIndex X scale)
          rationalFunctional.rate
              (continuumVacuumPairingObservable D a) epsilon <= scale /\
            rationalFunctional.rate
              (continuumVacuumPairingObservable D
                (D.timeTranslation.tau a)) epsilon <= scale

namespace BF4WilsonDenseStageQualitativeBase

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
    (base : BF4WilsonDenseStageQualitativeBase producer D)

def centeredStageObservable (scale : Nat)
    (observable : D.wilson.toGNSData.V) :
    (MatchedPhysicalStageGNSData family coupling scale).V :=
  matchedCenteredStageObservable D base.rawStageObservable scale observable

theorem centeredStageTransfer_intertwines (scale : Nat)
    (a : D.wilson.toGNSData.V) :
    (MatchedPhysicalStageGNSData family coupling scale).rad
      (centralPhysicalMarkovApply
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (base.centeredStageObservable scale a))
      (base.centeredStageObservable scale (D.timeTranslation.tau a)) :=
  centralPhysicalCenteredTransfer_rad_of_raw
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (base.rawStageObservable scale a)
    (base.rawStageObservable scale (D.timeTranslation.tau a))
    (base.rawStageTransfer_intertwines scale a)

end BF4WilsonDenseStageQualitativeBase

/-- Raw square and mean comparisons over precisely the qualitative base used
by the direct convergence proof. -/
structure BF4WilsonDenseStageRawMeanQualitativeComparison
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
  base : BF4WilsonDenseStageQualitativeBase producer D
  rawSquareComparisonRate : SelectedWilsonCauchy D -> Q' -> Nat
  rawSquareComparison : forall (X : SelectedWilsonCauchy D)
    (epsilon : Q'), (0 : Q') < epsilon ->
      forall scale : Nat, rawSquareComparisonRate X epsilon <= scale ->
        let a := X.seq (base.sampleIndex X scale)
        let Ta := D.timeTranslation.tau a
        let finiteA := finiteStageSquareExpectation D
          base.rawStageObservable scale a
        let finiteTa := finiteStageSquareExpectation D
          base.rawStageObservable scale Ta
        let rationalA := base.rationalFunctional.stageExpectationQ
          scale (mu.pick scale) (continuumSquareObservable D a)
        let rationalTa := base.rationalFunctional.stageExpectationQ
          scale (mu.pick scale) (continuumSquareObservable D Ta)
        (finiteA <= rationalA + epsilon /\
            rationalA <= finiteA + epsilon) /\
          (finiteTa <= rationalTa + epsilon /\
            rationalTa <= finiteTa + epsilon)
  rawMeanComparisonRate : SelectedWilsonCauchy D -> Q' -> Nat
  rawMeanComparison : forall (X : SelectedWilsonCauchy D)
    (epsilon : Q'), (0 : Q') < epsilon ->
      forall scale : Nat, rawMeanComparisonRate X epsilon <= scale ->
        let a := X.seq (base.sampleIndex X scale)
        let Ta := D.timeTranslation.tau a
        let finiteA := finiteStageRawMean D base.rawStageObservable scale a
        let finiteTa := finiteStageRawMean D base.rawStageObservable scale Ta
        let rationalA := base.rationalFunctional.stageExpectationQ
          scale (mu.pick scale) (continuumVacuumPairingObservable D a)
        let rationalTa := base.rationalFunctional.stageExpectationQ
          scale (mu.pick scale) (continuumVacuumPairingObservable D Ta)
        (finiteA <= rationalA + epsilon /\
            rationalA <= finiteA + epsilon) /\
          (finiteTa <= rationalTa + epsilon /\
            rationalTa <= finiteTa + epsilon)

namespace BF4WilsonDenseStageRawMeanQualitativeComparison

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
    (data : BF4WilsonDenseStageRawMeanQualitativeComparison producer D)

/-- Forget the unused representative pairing rates from the earlier raw-mean
comparison interface. -/
def ofRateComparison
    (legacy : BF4WilsonDenseStageRawMeanSlowComparison producer D) :
    BF4WilsonDenseStageRawMeanQualitativeComparison producer D where
  base := {
    separatorPinned := legacy.base.separatorPinned
    pointwiseTimeTranslation := legacy.base.pointwiseTimeTranslation
    rawStageObservable := legacy.base.rawStageObservable
    rawStageTransfer_intertwines := legacy.base.rawStageTransfer_intertwines
    rationalFunctional := legacy.base.regularizedFunctional
    vacuumPin := legacy.base.vacuumPairing.vacuumPin
    sampleRate := legacy.base.sampleRate
    sampleIndex := legacy.base.sampleIndex
    sampleIndex_cofinal := legacy.base.sampleIndex_cofinal
    projectiveDiagonalRate := legacy.base.projectiveDiagonalRate
    projective_diagonal_admissible := legacy.base.projective_diagonal_admissible
    projective_pairing_diagonal_admissible :=
      legacy.base.projective_pairing_diagonal_admissible
  }
  rawSquareComparisonRate := legacy.rawSquareComparisonRate
  rawSquareComparison := legacy.rawSquareComparison
  rawMeanComparisonRate := legacy.rawMeanComparisonRate
  rawMeanComparison := legacy.rawMeanComparison

/-! ## The six rational streams -/

def rawSquareSequence (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (data.base.sampleIndex X scale)
    CReal.ofQ'
      (finiteStageSquareExpectation D data.base.rawStageObservable scale a)

def translatedRawSquareSequence (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (data.base.sampleIndex X scale)
    CReal.ofQ' (finiteStageSquareExpectation D data.base.rawStageObservable
      scale (D.timeTranslation.tau a))

def projectiveSquareSequence (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (data.base.sampleIndex X scale)
    CReal.ofQ' (data.base.rationalFunctional.stageExpectationQ
      scale (mu.pick scale) (continuumSquareObservable D a))

def translatedProjectiveSquareSequence
    (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (data.base.sampleIndex X scale)
    CReal.ofQ' (data.base.rationalFunctional.stageExpectationQ
      scale (mu.pick scale)
        (continuumSquareObservable D (D.timeTranslation.tau a)))

def rawMeanSequence (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (data.base.sampleIndex X scale)
    CReal.ofQ'
      (finiteStageRawMean D data.base.rawStageObservable scale a)

def translatedRawMeanSequence (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (data.base.sampleIndex X scale)
    CReal.ofQ' (finiteStageRawMean D data.base.rawStageObservable scale
      (D.timeTranslation.tau a))

def projectiveMeanSequence (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (data.base.sampleIndex X scale)
    CReal.ofQ' (data.base.rationalFunctional.stageExpectationQ
      scale (mu.pick scale) (continuumVacuumPairingObservable D a))

def translatedProjectiveMeanSequence
    (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (data.base.sampleIndex X scale)
    CReal.ofQ' (data.base.rationalFunctional.stageExpectationQ
      scale (mu.pick scale)
        (continuumVacuumPairingObservable D (D.timeTranslation.tau a)))

/-! ## Explicit comparison legs -/

def rawSquareProjectiveClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose (data.rawSquareSequence X)
      (data.projectiveSquareSequence X) where
  stageRate := data.rawSquareComparisonRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale _ _
    exact (data.rawSquareComparison X epsilon hepsilon scale hscale).1

def translatedRawSquareProjectiveClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose (data.translatedRawSquareSequence X)
      (data.translatedProjectiveSquareSequence X) where
  stageRate := data.rawSquareComparisonRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale _ _
    exact (data.rawSquareComparison X epsilon hepsilon scale hscale).2

def projectiveSquareContinuumClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose (data.projectiveSquareSequence X)
      (continuumDenseNormSequence D (data.base.sampleIndex X) X) where
  stageRate := data.base.projectiveDiagonalRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale k _
    rw [continuumDenseNormSequence_approx]
    let a := X.seq (data.base.sampleIndex X scale)
    have hadmissible :=
      (data.base.projective_diagonal_admissible X epsilon hepsilon
        scale hscale).1
    have hbound := data.base.rationalFunctional.bound
      (continuumSquareObservable D a) epsilon hepsilon scale hadmissible
    rw [continuumForm_eq_continuumSquareExpectation D a]
    exact hbound

def translatedProjectiveSquareContinuumClose
    (X : SelectedWilsonCauchy D) :
    let TX := data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X
    CRealEventuallyClose (data.translatedProjectiveSquareSequence X)
      (continuumDenseNormSequence D (data.base.sampleIndex X) TX) := by
  let TX := data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X
  exact {
    stageRate := data.base.projectiveDiagonalRate X
    approxRate := fun _ _ => 0
    close := by
      intro epsilon hepsilon scale hscale k _
      rw [continuumDenseNormSequence_approx]
      let a := X.seq (data.base.sampleIndex X scale)
      let Ta := D.timeTranslation.tau a
      have hadmissible :=
        (data.base.projective_diagonal_admissible X epsilon hepsilon
          scale hscale).2
      have hbound := data.base.rationalFunctional.bound
        (continuumSquareObservable D Ta) epsilon hepsilon scale hadmissible
      have hpointwise : D.wilson.toGNSData.veq
          (TX.seq (data.base.sampleIndex X scale)) Ta :=
        data.base.pointwiseTimeTranslation.pointwise X
          (data.base.sampleIndex X scale)
      have hform :
          (D.wilson.toGNSData.B
            (TX.seq (data.base.sampleIndex X scale))
            (TX.seq (data.base.sampleIndex X scale))).eqv
            (continuumSquareExpectation D Ta) :=
        Q'.eqv_trans _ _ _
          (D.wilson.toGNSData.B_diag_congr hpointwise)
          (Q'.eqv_of_eq
            (continuumForm_eq_continuumSquareExpectation D Ta))
      exact
        ⟨le_of_le_eqv hbound.1
            (Q'.add_eqv_congr_right _ _ epsilon
              (Q'.eqv_symm hform)),
          le_of_eqv_le hform hbound.2⟩
  }

def rawMeanProjectiveClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose (data.rawMeanSequence X)
      (data.projectiveMeanSequence X) where
  stageRate := data.rawMeanComparisonRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale _ _
    exact (data.rawMeanComparison X epsilon hepsilon scale hscale).1

def translatedRawMeanProjectiveClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose (data.translatedRawMeanSequence X)
      (data.translatedProjectiveMeanSequence X) where
  stageRate := data.rawMeanComparisonRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale _ _
    exact (data.rawMeanComparison X epsilon hepsilon scale hscale).2

def projectiveMeanContinuumClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose (data.projectiveMeanSequence X)
      (continuumDenseVacuumPairingSequence D
        (data.base.sampleIndex X) X) where
  stageRate := data.base.projectiveDiagonalRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale _ _
    let a := X.seq (data.base.sampleIndex X scale)
    have hadmissible :=
      (data.base.projective_pairing_diagonal_admissible X epsilon hepsilon
        scale hscale).1
    have hbound := data.base.rationalFunctional.bound
      (continuumVacuumPairingObservable D a)
      epsilon hepsilon scale hadmissible
    rw [← WilsonDenseUnitVacuumPairingModulus.pairing_eq_continuumVacuumPairingExpectation
      (D := D) a] at hbound
    exact hbound

def translatedProjectiveMeanContinuumClose
    (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose (data.translatedProjectiveMeanSequence X)
      (fun scale => CReal.ofQ'
        (D.wilson.toGNSData.B
          (D.timeTranslation.tau
            (X.seq (data.base.sampleIndex X scale)))
          H.os_axioms.A.one)) where
  stageRate := data.base.projectiveDiagonalRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale _ _
    let a := X.seq (data.base.sampleIndex X scale)
    let Ta := D.timeTranslation.tau a
    have hadmissible :=
      (data.base.projective_pairing_diagonal_admissible X epsilon hepsilon
        scale hscale).2
    have hbound := data.base.rationalFunctional.bound
      (continuumVacuumPairingObservable D Ta)
      epsilon hepsilon scale hadmissible
    rw [← WilsonDenseUnitVacuumPairingModulus.pairing_eq_continuumVacuumPairingExpectation
      (D := D) Ta] at hbound
    exact hbound

/-! ## Qualitative raw limits -/

theorem rawSquareSequence_converges
    (X : SelectedWilsonCauchy D) :
    CReal.ConvergesTo (data.rawSquareSequence X)
      (D.wilson.toGNSData.cinnerRep X X) :=
  convergesTo_of_eventuallyClose (data.rawSquareProjectiveClose X)
    (convergesTo_of_eventuallyClose (data.projectiveSquareContinuumClose X)
      (continuumDenseNormSequence_converges D
        (data.base.sampleIndex X) (data.base.sampleRate X)
        (data.base.sampleIndex_cofinal X) X))

theorem translatedRawSquareSequence_converges
    (X : SelectedWilsonCauchy D) :
    let TX := data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X
    CReal.ConvergesTo (data.translatedRawSquareSequence X)
      (D.wilson.toGNSData.cinnerRep TX TX) := by
  let TX := data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X
  exact convergesTo_of_eventuallyClose
    (data.translatedRawSquareProjectiveClose X)
    (convergesTo_of_eventuallyClose
      (data.translatedProjectiveSquareContinuumClose X)
      (continuumDenseNormSequence_converges D
        (data.base.sampleIndex X) (data.base.sampleRate X)
        (data.base.sampleIndex_cofinal X) TX))

theorem rawMeanSequence_converges_zero
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo (data.rawMeanSequence X) CReal.czero :=
  convergesTo_of_eventuallyClose (data.rawMeanProjectiveClose X)
    (convergesTo_of_eventuallyClose (data.projectiveMeanContinuumClose X)
      (continuumDenseVacuumPairingSequence_converges_zero
        data.base.vacuumPin
        (data.base.sampleIndex X) (data.base.sampleRate X)
        (data.base.sampleIndex_cofinal X) X horthogonal))

theorem translatedRawMeanSequence_converges_zero
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo (data.translatedRawMeanSequence X) CReal.czero :=
  convergesTo_of_eventuallyClose
    (data.translatedRawMeanProjectiveClose X)
    (convergesTo_of_eventuallyClose
      (data.translatedProjectiveMeanContinuumClose X)
      (continuumTranslatedDenseVacuumPairingSequence_converges_zero
        data.base.vacuumPin
        data.base.pointwiseTimeTranslation
        (data.base.sampleIndex X) (data.base.sampleRate X)
        (data.base.sampleIndex_cofinal X) X horthogonal))

/-! ## Exact centering and the two graph-norm limits -/

private theorem creal_ofQ'_centered_equiv (raw mean : Q') :
    CReal.Equiv
      (CReal.ofQ' (raw + -(mean * mean)))
      (CReal.add (CReal.ofQ' raw)
        (CReal.neg
          (CReal.mul (CReal.ofQ' mean) (CReal.ofQ' mean)))) :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.eqv_refl _)

private theorem creal_mul_czero (value : CReal) :
    CReal.Equiv (CReal.mul value CReal.czero) CReal.czero :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_zero_eqv (value.approx n))

private theorem creal_neg_czero :
    CReal.Equiv (CReal.neg CReal.czero) CReal.czero :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun _ => by
      change (-(0 : Q')).eqv 0
      decide)

private theorem creal_add_czero (value : CReal) :
    CReal.Equiv (CReal.add value CReal.czero) value :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (value.approx n)))

theorem norm_converges_qualitative
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo
      (adaptiveDenseStageNormSequence D data.base.sampleIndex
        data.base.centeredStageObservable X)
      (D.wilson.toGNSData.cinnerRep X X) := by
  let rawSeq := data.rawSquareSequence X
  let meanSeq := data.rawMeanSequence X
  have hraw : CReal.ConvergesTo rawSeq
      (D.wilson.toGNSData.cinnerRep X X) := by
    simpa only [rawSeq] using data.rawSquareSequence_converges X
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    simpa only [meanSeq] using
      data.rawMeanSequence_converges_zero X horthogonal
  have hsquare := CReal.convergesTo_mul_general hmean hmean
  have hsquareZero : CReal.ConvergesTo
      (fun scale => CReal.mul (meanSeq scale) (meanSeq scale))
      CReal.czero :=
    CReal.convergesTo_limit_congr hsquare (creal_mul_czero CReal.czero)
  have hcenteredRaw := CReal.convergesTo_add hraw
    (CReal.convergesTo_neg hsquareZero)
  have hcenteredLimit : CReal.ConvergesTo
      (fun scale => CReal.add (rawSeq scale)
        (CReal.neg (CReal.mul (meanSeq scale) (meanSeq scale))))
      (D.wilson.toGNSData.cinnerRep X X) := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
      (creal_add_czero (D.wilson.toGNSData.cinnerRep X X))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun scale => CReal.add (rawSeq scale)
      (CReal.neg (CReal.mul (meanSeq scale) (meanSeq scale))))
  · intro scale
    let a := X.seq (data.base.sampleIndex X scale)
    let raw := finiteStageSquareExpectation D
      data.base.rawStageObservable scale a
    let mean := finiteStageRawMean D data.base.rawStageObservable scale a
    have hcentered := finiteStageCenteredSquare_identity
      D data.base.rawStageObservable scale a
    exact CReal.Equiv.trans
      (CReal.Equiv.symm (creal_ofQ'_centered_equiv raw mean))
      (CReal.Equiv.symm (CReal.ofQ'_equiv_of_eqv hcentered))
  · simpa only [rawSeq, meanSeq, rawSquareSequence, rawMeanSequence,
      adaptiveDenseStageNormSequence_approx] using hcenteredLimit

theorem transferredNorm_converges_qualitative
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo
      (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
        (adaptiveDenseStageApproximant D data.base.sampleIndex
          data.base.centeredStageObservable X scale))
      (D.wilson.toGNSData.cinnerRep
        (data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)
        (data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)) := by
  let TX := data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X
  let rawSeq := data.translatedRawSquareSequence X
  let meanSeq := data.translatedRawMeanSequence X
  have hraw : CReal.ConvergesTo rawSeq
      (D.wilson.toGNSData.cinnerRep TX TX) := by
    simpa only [rawSeq, TX] using data.translatedRawSquareSequence_converges X
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    simpa only [meanSeq] using
      data.translatedRawMeanSequence_converges_zero X horthogonal
  have hsquare := CReal.convergesTo_mul_general hmean hmean
  have hsquareZero : CReal.ConvergesTo
      (fun scale => CReal.mul (meanSeq scale) (meanSeq scale))
      CReal.czero :=
    CReal.convergesTo_limit_congr hsquare (creal_mul_czero CReal.czero)
  have hcenteredRaw := CReal.convergesTo_add hraw
    (CReal.convergesTo_neg hsquareZero)
  have hcenteredLimit : CReal.ConvergesTo
      (fun scale => CReal.add (rawSeq scale)
        (CReal.neg (CReal.mul (meanSeq scale) (meanSeq scale))))
      (D.wilson.toGNSData.cinnerRep TX TX) := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
      (creal_add_czero (D.wilson.toGNSData.cinnerRep TX TX))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun scale => CReal.add (rawSeq scale)
      (CReal.neg (CReal.mul (meanSeq scale) (meanSeq scale))))
  · intro scale
    let a := X.seq (data.base.sampleIndex X scale)
    let Ta := D.timeTranslation.tau a
    let raw := finiteStageSquareExpectation D
      data.base.rawStageObservable scale Ta
    let mean := finiteStageRawMean D data.base.rawStageObservable scale Ta
    have hcentered := finiteStageCenteredSquare_identity
      D data.base.rawStageObservable scale Ta
    have htransfer :
        ((MatchedPhysicalStageGNSData family coupling scale).B
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0
            (data.base.centeredStageObservable scale a))
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0
            (data.base.centeredStageObservable scale a))).eqv
          (finiteStageSquareExpectation D
            data.base.centeredStageObservable scale Ta) :=
      (MatchedPhysicalStageGNSData family coupling scale).B_welldef
        (data.base.centeredStageTransfer_intertwines scale a)
        (data.base.centeredStageTransfer_intertwines scale a)
    exact CReal.Equiv.trans
      (CReal.Equiv.symm (creal_ofQ'_centered_equiv raw mean))
      (CReal.Equiv.trans
        (CReal.Equiv.symm (CReal.ofQ'_equiv_of_eqv hcentered))
        (CReal.Equiv.symm (CReal.ofQ'_equiv_of_eqv htransfer)))
  · simpa only [rawSeq, meanSeq, translatedRawSquareSequence,
      translatedRawMeanSequence, matchedPhysicalStageTransferredNorm,
      adaptiveDenseStageApproximant, denseStageApproximant, constCauchy]
      using hcenteredLimit

/-- The direct qualitative route reaches the conditional graph-norm limit.
Only `data.base.vacuumPin` is used; no representative pairing rate is carried
by this interface. -/
def toVacuumLinearGraphNormLimitApproximationQualitative :
    BF4WilsonVacuumLinearGraphNormLimitApproximation producer D where
  separatorPinned := data.base.separatorPinned
  linearTimeTranslation := data.base.pointwiseTimeTranslation.linear
  approximant := fun X scale =>
    adaptiveDenseStageApproximant D data.base.sampleIndex
      data.base.centeredStageObservable X scale
  approximant_vacuumOrthogonal := by
    intro X _ scale
    exact centralPhysicalModulatedEmbedV_vacuumOrthogonal_of_meanZero
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (data.base.centeredStageObservable scale
        (X.seq (data.base.sampleIndex X scale)))
      (centralPhysicalCenteredObservable_meanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (data.base.rawStageObservable scale
          (X.seq (data.base.sampleIndex X scale))))
  norm_converges := data.norm_converges_qualitative
  transferredNorm_converges := data.transferredNorm_converges_qualitative

/-- The direct qualitative route reaches the selected completed operator gap. -/
def toWilsonOperatorNormGapPinQualitative : WilsonOperatorNormGapPin D :=
  data.toVacuumLinearGraphNormLimitApproximationQualitative
    |>.toWilsonOperatorNormGapPin

end BF4WilsonDenseStageRawMeanQualitativeComparison

/-! ## General fixed-observable construction without pairing rates -/

namespace BF4WilsonDenseStageQualitativeProjectiveCompiler

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
    (base : BF4WilsonDenseStageCenteredVacuumQualitativeProjectiveBase
      producer D)

def regularizedFunctional : ProjectiveOSRationalModulus D :=
  regularizedProjectiveModulus base.rationalFunctional

def projectiveRequirement (X : SelectedWilsonCauchy D)
    (index : Nat) : Nat :=
  max
    (max
      ((regularizedFunctional base).rate
        (continuumSquareObservable D (X.seq index))
        (Q'.invSucc index))
      ((regularizedFunctional base).rate
        (continuumSquareObservable D
          (D.timeTranslation.tau (X.seq index)))
        (Q'.invSucc index)))
    (max
      ((regularizedFunctional base).rate
        (continuumVacuumPairingObservable D (X.seq index))
        (Q'.invSucc index))
      ((regularizedFunctional base).rate
        (continuumVacuumPairingObservable D
          (D.timeTranslation.tau (X.seq index)))
        (Q'.invSucc index)))

def rawRequirement (X : SelectedWilsonCauchy D) (index : Nat) : Nat :=
  max
    (max
      (base.rawMoments.regularSquareRate (X.seq index)
        (Q'.invSucc index))
      (base.rawMoments.regularSquareRate
        (D.timeTranslation.tau (X.seq index))
        (Q'.invSucc index)))
    (max
      (base.rawMoments.regularMeanRate (X.seq index)
        (Q'.invSucc index))
      (base.rawMoments.regularMeanRate
        (D.timeTranslation.tau (X.seq index))
        (Q'.invSucc index)))

def requirement (X : SelectedWilsonCauchy D) (index : Nat) : Nat :=
  max (projectiveRequirement base X index) (rawRequirement base X index)

def sampleRate (X : SelectedWilsonCauchy D) (threshold : Nat) : Nat :=
  slowThreshold (requirement base X) threshold

def sampleIndex (X : SelectedWilsonCauchy D) (scale : Nat) : Nat :=
  slowIndex (requirement base X) scale

def projectiveDiagonalRate (X : SelectedWilsonCauchy D)
    (epsilon : Q') : Nat :=
  sampleRate base X (CReal.lv epsilon)

theorem sampleIndex_cofinal (X : SelectedWilsonCauchy D)
    (threshold scale : Nat)
    (hscale : sampleRate base X threshold <= scale) :
    threshold <= sampleIndex base X scale :=
  slowIndex_cofinal (requirement base X) threshold scale hscale

private theorem selected_requirement_paid (X : SelectedWilsonCauchy D)
    (epsilon : Q') (scale : Nat)
    (hscale : projectiveDiagonalRate base X epsilon <= scale) :
    requirement base X (sampleIndex base X scale) <= scale := by
  have hzeroRate : sampleRate base X 0 <=
      sampleRate base X (CReal.lv epsilon) :=
    slowThreshold_mono (requirement base X) (Nat.zero_le _)
  exact required_slowIndex_le (requirement base X) scale
    (Nat.le_trans hzeroRate hscale)

private theorem selected_precision (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale : projectiveDiagonalRate base X epsilon <= scale) :
    Q'.invSucc (sampleIndex base X scale) <= epsilon := by
  have hprecision : CReal.lv epsilon <= sampleIndex base X scale :=
    sampleIndex_cofinal base X (CReal.lv epsilon) scale hscale
  exact Q'.le_trans' _ _ _
    (ExpNeg.invSucc_le_of_le hprecision)
    (CReal.invSucc_lv_le hepsilon)

theorem projective_diagonal_admissible (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale : projectiveDiagonalRate base X epsilon <= scale) :
    let a := X.seq (sampleIndex base X scale)
    (regularizedFunctional base).rate
        (continuumSquareObservable D a) epsilon <= scale /\
      (regularizedFunctional base).rate
        (continuumSquareObservable D (D.timeTranslation.tau a)) epsilon <=
          scale := by
  let index := sampleIndex base X scale
  have hrequired := selected_requirement_paid base X epsilon scale hscale
  have hindexepsilon := selected_precision base X epsilon hepsilon scale hscale
  have hordinary : (regularizedFunctional base).rate
      (continuumSquareObservable D (X.seq index)) epsilon <=
      (regularizedFunctional base).rate
        (continuumSquareObservable D (X.seq index))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone base.rationalFunctional
      (continuumSquareObservable D (X.seq index))
      (Q'.invSucc_pos index) hindexepsilon
  have htranslated : (regularizedFunctional base).rate
      (continuumSquareObservable D
        (D.timeTranslation.tau (X.seq index))) epsilon <=
      (regularizedFunctional base).rate
        (continuumSquareObservable D
          (D.timeTranslation.tau (X.seq index)))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone base.rationalFunctional
      (continuumSquareObservable D
        (D.timeTranslation.tau (X.seq index)))
      (Q'.invSucc_pos index) hindexepsilon
  dsimp only
  constructor
  · exact Nat.le_trans hordinary
      (Nat.le_trans
        (Nat.le_trans
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
          (Nat.le_max_left _ _))
        hrequired)
  · exact Nat.le_trans htranslated
      (Nat.le_trans
        (Nat.le_trans
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
          (Nat.le_max_left _ _))
        hrequired)

theorem projective_pairing_diagonal_admissible
    (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale : projectiveDiagonalRate base X epsilon <= scale) :
    let a := X.seq (sampleIndex base X scale)
    (regularizedFunctional base).rate
        (continuumVacuumPairingObservable D a) epsilon <= scale /\
      (regularizedFunctional base).rate
        (continuumVacuumPairingObservable D
          (D.timeTranslation.tau a)) epsilon <= scale := by
  let index := sampleIndex base X scale
  have hrequired := selected_requirement_paid base X epsilon scale hscale
  have hindexepsilon := selected_precision base X epsilon hepsilon scale hscale
  have hordinary : (regularizedFunctional base).rate
      (continuumVacuumPairingObservable D (X.seq index)) epsilon <=
      (regularizedFunctional base).rate
        (continuumVacuumPairingObservable D (X.seq index))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone base.rationalFunctional
      (continuumVacuumPairingObservable D (X.seq index))
      (Q'.invSucc_pos index) hindexepsilon
  have htranslated : (regularizedFunctional base).rate
      (continuumVacuumPairingObservable D
        (D.timeTranslation.tau (X.seq index))) epsilon <=
      (regularizedFunctional base).rate
        (continuumVacuumPairingObservable D
          (D.timeTranslation.tau (X.seq index)))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone base.rationalFunctional
      (continuumVacuumPairingObservable D
        (D.timeTranslation.tau (X.seq index)))
      (Q'.invSucc_pos index) hindexepsilon
  dsimp only
  constructor
  · exact Nat.le_trans hordinary
      (Nat.le_trans
        (Nat.le_trans
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
          (Nat.le_max_left _ _))
        hrequired)
  · exact Nat.le_trans htranslated
      (Nat.le_trans
        (Nat.le_trans
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
          (Nat.le_max_left _ _))
        hrequired)

theorem raw_square_diagonal_admissible (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale : projectiveDiagonalRate base X epsilon <= scale) :
    let a := X.seq (sampleIndex base X scale)
    base.rawMoments.regularSquareRate a epsilon <= scale /\
      base.rawMoments.regularSquareRate
        (D.timeTranslation.tau a) epsilon <= scale := by
  let index := sampleIndex base X scale
  have hrequired := selected_requirement_paid base X epsilon scale hscale
  have hindexepsilon := selected_precision base X epsilon hepsilon scale hscale
  have hordinary : base.rawMoments.regularSquareRate
      (X.seq index) epsilon <=
      base.rawMoments.regularSquareRate
        (X.seq index) (Q'.invSucc index) :=
    base.rawMoments.regularSquareRate_antitone
      (X.seq index) (Q'.invSucc_pos index) hindexepsilon
  have htranslated : base.rawMoments.regularSquareRate
      (D.timeTranslation.tau (X.seq index)) epsilon <=
      base.rawMoments.regularSquareRate
        (D.timeTranslation.tau (X.seq index)) (Q'.invSucc index) :=
    base.rawMoments.regularSquareRate_antitone
      (D.timeTranslation.tau (X.seq index))
      (Q'.invSucc_pos index) hindexepsilon
  dsimp only
  constructor
  · exact Nat.le_trans hordinary
      (Nat.le_trans
        (Nat.le_trans
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
          (Nat.le_max_right _ _))
        hrequired)
  · exact Nat.le_trans htranslated
      (Nat.le_trans
        (Nat.le_trans
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
          (Nat.le_max_right _ _))
        hrequired)

theorem raw_mean_diagonal_admissible (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale : projectiveDiagonalRate base X epsilon <= scale) :
    let a := X.seq (sampleIndex base X scale)
    base.rawMoments.regularMeanRate a epsilon <= scale /\
      base.rawMoments.regularMeanRate
        (D.timeTranslation.tau a) epsilon <= scale := by
  let index := sampleIndex base X scale
  have hrequired := selected_requirement_paid base X epsilon scale hscale
  have hindexepsilon := selected_precision base X epsilon hepsilon scale hscale
  have hordinary : base.rawMoments.regularMeanRate
      (X.seq index) epsilon <=
      base.rawMoments.regularMeanRate
        (X.seq index) (Q'.invSucc index) :=
    base.rawMoments.regularMeanRate_antitone
      (X.seq index) (Q'.invSucc_pos index) hindexepsilon
  have htranslated : base.rawMoments.regularMeanRate
      (D.timeTranslation.tau (X.seq index)) epsilon <=
      base.rawMoments.regularMeanRate
        (D.timeTranslation.tau (X.seq index)) (Q'.invSucc index) :=
    base.rawMoments.regularMeanRate_antitone
      (D.timeTranslation.tau (X.seq index))
      (Q'.invSucc_pos index) hindexepsilon
  dsimp only
  constructor
  · exact Nat.le_trans hordinary
      (Nat.le_trans
        (Nat.le_trans
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
          (Nat.le_max_right _ _))
        hrequired)
  · exact Nat.le_trans htranslated
      (Nat.le_trans
        (Nat.le_trans
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
          (Nat.le_max_right _ _))
        hrequired)

/-- General fixed-observable raw moment moduli construct the qualitative
moving-diagonal comparison with no representative vacuum-pairing rate. -/
def toQualitativeComparison :
    BF4WilsonDenseStageRawMeanQualitativeComparison producer D where
  base := {
    separatorPinned := base.separatorPinned
    pointwiseTimeTranslation := base.pointwiseTimeTranslation
    rawStageObservable := base.rawStageObservable
    rawStageTransfer_intertwines := base.rawStageTransfer_intertwines
    rationalFunctional := regularizedFunctional base
    vacuumPin := base.vacuumPin
    sampleRate := sampleRate base
    sampleIndex := sampleIndex base
    sampleIndex_cofinal := sampleIndex_cofinal base
    projectiveDiagonalRate := projectiveDiagonalRate base
    projective_diagonal_admissible := projective_diagonal_admissible base
    projective_pairing_diagonal_admissible :=
      projective_pairing_diagonal_admissible base
  }
  rawSquareComparisonRate := projectiveDiagonalRate base
  rawSquareComparison := by
    intro X epsilon hepsilon scale hscale
    have hadmissible := raw_square_diagonal_admissible base
      X epsilon hepsilon scale hscale
    dsimp only
    exact
      ⟨base.rawMoments.regularSquareBound _ epsilon hepsilon scale
          hadmissible.1,
        base.rawMoments.regularSquareBound _ epsilon hepsilon scale
          hadmissible.2⟩
  rawMeanComparisonRate := projectiveDiagonalRate base
  rawMeanComparison := by
    intro X epsilon hepsilon scale hscale
    have hadmissible := raw_mean_diagonal_admissible base
      X epsilon hepsilon scale hscale
    dsimp only
    exact
      ⟨base.rawMoments.regularMeanBound _ epsilon hepsilon scale
          hadmissible.1,
        base.rawMoments.regularMeanBound _ epsilon hepsilon scale
          hadmissible.2⟩

def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  (toQualitativeComparison base).toWilsonOperatorNormGapPinQualitative

end BF4WilsonDenseStageQualitativeProjectiveCompiler

/-! ## Exact-semantic construction of the qualitative diagonal -/

namespace BF4WilsonDenseStageCenteredVacuumQualitativeSemanticBase

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
    (base :
      YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumQualitativeSemanticBase
        producer D)

/-- Antitone regularization of the projective rate, with the evaluator and
same-thread semantics unchanged. -/
def regularizedFunctional : ProjectiveOSRationalModulus D :=
  regularizedProjectiveModulus base.rationalFunctional

/-- The four projective rates needed for the ordinary/translated square and
ordinary/translated vacuum pairing of one selected representative. -/
def requirement (X : SelectedWilsonCauchy D) (index : Nat) : Nat :=
  max
    (max
      ((regularizedFunctional base).rate
        (continuumSquareObservable D (X.seq index))
        (Q'.invSucc index))
      ((regularizedFunctional base).rate
        (continuumSquareObservable D
          (D.timeTranslation.tau (X.seq index)))
        (Q'.invSucc index)))
    (max
      ((regularizedFunctional base).rate
        (continuumVacuumPairingObservable D (X.seq index))
        (Q'.invSucc index))
      ((regularizedFunctional base).rate
        (continuumVacuumPairingObservable D
          (D.timeTranslation.tau (X.seq index)))
        (Q'.invSucc index)))

def sampleRate (X : SelectedWilsonCauchy D) (threshold : Nat) : Nat :=
  slowThreshold (requirement base X) threshold

def sampleIndex (X : SelectedWilsonCauchy D) (scale : Nat) : Nat :=
  slowIndex (requirement base X) scale

def projectiveDiagonalRate (X : SelectedWilsonCauchy D)
    (epsilon : Q') : Nat :=
  sampleRate base X (CReal.lv epsilon)

theorem sampleIndex_cofinal (X : SelectedWilsonCauchy D)
    (threshold scale : Nat)
    (hscale : sampleRate base X threshold <= scale) :
    threshold <= sampleIndex base X scale :=
  slowIndex_cofinal (requirement base X) threshold scale hscale

theorem projective_diagonal_admissible (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale : projectiveDiagonalRate base X epsilon <= scale) :
    let a := X.seq (sampleIndex base X scale)
    (regularizedFunctional base).rate
        (continuumSquareObservable D a) epsilon <= scale /\
      (regularizedFunctional base).rate
        (continuumSquareObservable D (D.timeTranslation.tau a)) epsilon <=
          scale := by
  let precision := CReal.lv epsilon
  let index := sampleIndex base X scale
  have hprecision : precision <= index :=
    sampleIndex_cofinal base X precision scale hscale
  have hzeroRate : sampleRate base X 0 <= sampleRate base X precision :=
    slowThreshold_mono (requirement base X) (Nat.zero_le precision)
  have hzero : sampleRate base X 0 <= scale :=
    Nat.le_trans hzeroRate hscale
  have hrequired : requirement base X index <= scale :=
    required_slowIndex_le (requirement base X) scale hzero
  have hindexepsilon : Q'.invSucc index <= epsilon :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hprecision)
      (CReal.invSucc_lv_le hepsilon)
  have hordinary : (regularizedFunctional base).rate
      (continuumSquareObservable D (X.seq index)) epsilon <=
      (regularizedFunctional base).rate
        (continuumSquareObservable D (X.seq index))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone base.rationalFunctional
      (continuumSquareObservable D (X.seq index))
      (Q'.invSucc_pos index) hindexepsilon
  have htranslated : (regularizedFunctional base).rate
      (continuumSquareObservable D
        (D.timeTranslation.tau (X.seq index))) epsilon <=
      (regularizedFunctional base).rate
        (continuumSquareObservable D
          (D.timeTranslation.tau (X.seq index)))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone base.rationalFunctional
      (continuumSquareObservable D
        (D.timeTranslation.tau (X.seq index)))
      (Q'.invSucc_pos index) hindexepsilon
  dsimp only
  constructor
  · exact Nat.le_trans hordinary
      (Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
        hrequired)
  · exact Nat.le_trans htranslated
      (Nat.le_trans
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
        hrequired)

theorem projective_pairing_diagonal_admissible
    (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale : projectiveDiagonalRate base X epsilon <= scale) :
    let a := X.seq (sampleIndex base X scale)
    (regularizedFunctional base).rate
        (continuumVacuumPairingObservable D a) epsilon <= scale /\
      (regularizedFunctional base).rate
        (continuumVacuumPairingObservable D
          (D.timeTranslation.tau a)) epsilon <= scale := by
  let precision := CReal.lv epsilon
  let index := sampleIndex base X scale
  have hprecision : precision <= index :=
    sampleIndex_cofinal base X precision scale hscale
  have hzeroRate : sampleRate base X 0 <= sampleRate base X precision :=
    slowThreshold_mono (requirement base X) (Nat.zero_le precision)
  have hzero : sampleRate base X 0 <= scale :=
    Nat.le_trans hzeroRate hscale
  have hrequired : requirement base X index <= scale :=
    required_slowIndex_le (requirement base X) scale hzero
  have hindexepsilon : Q'.invSucc index <= epsilon :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hprecision)
      (CReal.invSucc_lv_le hepsilon)
  have hordinary : (regularizedFunctional base).rate
      (continuumVacuumPairingObservable D (X.seq index)) epsilon <=
      (regularizedFunctional base).rate
        (continuumVacuumPairingObservable D (X.seq index))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone base.rationalFunctional
      (continuumVacuumPairingObservable D (X.seq index))
      (Q'.invSucc_pos index) hindexepsilon
  have htranslated : (regularizedFunctional base).rate
      (continuumVacuumPairingObservable D
        (D.timeTranslation.tau (X.seq index))) epsilon <=
      (regularizedFunctional base).rate
        (continuumVacuumPairingObservable D
          (D.timeTranslation.tau (X.seq index)))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone base.rationalFunctional
      (continuumVacuumPairingObservable D
        (D.timeTranslation.tau (X.seq index)))
      (Q'.invSucc_pos index) hindexepsilon
  dsimp only
  constructor
  · exact Nat.le_trans hordinary
      (Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        hrequired)
  · exact Nat.le_trans htranslated
      (Nat.le_trans
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        hrequired)

/-- Exact same-stage semantics make both raw comparison rates zero. -/
def toQualitativeComparison :
    BF4WilsonDenseStageRawMeanQualitativeComparison producer D where
  base := {
    separatorPinned := base.separatorPinned
    pointwiseTimeTranslation := base.pointwiseTimeTranslation
    rawStageObservable := base.rawStageObservable
    rawStageTransfer_intertwines := base.rawStageTransfer_intertwines
    rationalFunctional := regularizedFunctional base
    vacuumPin := base.vacuumPin
    sampleRate := sampleRate base
    sampleIndex := sampleIndex base
    sampleIndex_cofinal := sampleIndex_cofinal base
    projectiveDiagonalRate := projectiveDiagonalRate base
    projective_diagonal_admissible := projective_diagonal_admissible base
    projective_pairing_diagonal_admissible :=
      projective_pairing_diagonal_admissible base
  }
  rawSquareComparisonRate := fun _ _ => 0
  rawSquareComparison := by
    intro X epsilon hepsilon scale _
    let index := sampleIndex base X scale
    let a := X.seq index
    let Ta := D.timeTranslation.tau a
    let rawMoments := base.rawMomentSemantics.toRawStageMomentModulus
      (regularizedFunctional base)
    dsimp only
    exact
      ⟨rawMoments.squareBound a epsilon hepsilon scale (Nat.zero_le scale),
        rawMoments.squareBound Ta epsilon hepsilon scale
          (Nat.zero_le scale)⟩
  rawMeanComparisonRate := fun _ _ => 0
  rawMeanComparison := by
    intro X epsilon hepsilon scale _
    let index := sampleIndex base X scale
    let a := X.seq index
    let Ta := D.timeTranslation.tau a
    let rawMoments := base.rawMomentSemantics.toRawStageMomentModulus
      (regularizedFunctional base)
    dsimp only
    exact
      ⟨rawMoments.meanBound a epsilon hepsilon scale (Nat.zero_le scale),
        rawMoments.meanBound Ta epsilon hepsilon scale
          (Nat.zero_le scale)⟩

/-- The weak semantic input alone compiles to the selected completed gap. -/
def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  (toQualitativeComparison base).toWilsonOperatorNormGapPinQualitative

end BF4WilsonDenseStageCenteredVacuumQualitativeSemanticBase

end YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison

#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanQualitativeComparison.rawSquareSequence_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanQualitativeComparison.rawMeanSequence_converges_zero
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanQualitativeComparison.norm_converges_qualitative
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanQualitativeComparison.transferredNorm_converges_qualitative
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanQualitativeComparison.toWilsonOperatorNormGapPinQualitative
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageQualitativeProjectiveCompiler.projective_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageQualitativeProjectiveCompiler.projective_pairing_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageQualitativeProjectiveCompiler.raw_square_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageQualitativeProjectiveCompiler.raw_mean_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageQualitativeProjectiveCompiler.toQualitativeComparison
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageQualitativeProjectiveCompiler.toWilsonOperatorNormGapPin
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageCenteredVacuumQualitativeSemanticBase.projective_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageCenteredVacuumQualitativeSemanticBase.projective_pairing_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageCenteredVacuumQualitativeSemanticBase.toQualitativeComparison
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageCenteredVacuumQualitativeSemanticBase.toWilsonOperatorNormGapPin
