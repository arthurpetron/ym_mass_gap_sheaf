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
limits.  The current input record still contains the stronger pairing modulus;
the proofs below use only its `vacuumPin`, preparing the next interface
weakening.
-/

import YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison

namespace YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
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

namespace BF4WilsonDenseStageRawMeanSlowComparison

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
    (data : BF4WilsonDenseStageRawMeanSlowComparison producer D)

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
    CReal.ofQ' (data.base.regularizedFunctional.stageExpectationQ
      scale (mu.pick scale) (continuumSquareObservable D a))

def translatedProjectiveSquareSequence
    (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (data.base.sampleIndex X scale)
    CReal.ofQ' (data.base.regularizedFunctional.stageExpectationQ
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
    CReal.ofQ' (data.base.regularizedFunctional.stageExpectationQ
      scale (mu.pick scale) (continuumVacuumPairingObservable D a))

def translatedProjectiveMeanSequence
    (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (data.base.sampleIndex X scale)
    CReal.ofQ' (data.base.regularizedFunctional.stageExpectationQ
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
    have hbound := data.base.regularizedFunctional.bound
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
      have hbound := data.base.regularizedFunctional.bound
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
    have hbound := data.base.regularizedFunctional.bound
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
    have hbound := data.base.regularizedFunctional.bound
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
        data.base.vacuumPairing.vacuumPin
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
        data.base.vacuumPairing.vacuumPin
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
Only `data.base.vacuumPairing.vacuumPin` is used; its rate fields are absent
from every convergence proof above. -/
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

end BF4WilsonDenseStageRawMeanSlowComparison

end YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison

#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanSlowComparison.rawSquareSequence_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanSlowComparison.rawMeanSequence_converges_zero
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanSlowComparison.norm_converges_qualitative
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanSlowComparison.transferredNorm_converges_qualitative
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanSlowComparison.toWilsonOperatorNormGapPinQualitative
