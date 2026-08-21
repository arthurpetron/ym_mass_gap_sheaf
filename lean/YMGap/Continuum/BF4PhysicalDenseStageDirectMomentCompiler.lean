/-
# Direct raw-moment compiler for the physical BF4 graph-norm limit

The projective compiler reaches the selected continuum Wilson moments through
two separately rate-controlled legs.  `BF4RawStageContinuumMomentModulus`
already fuses those legs.  This module consumes that weaker certificate
directly, constructs a cofinal slow diagonal paying only the ordinary and
translated square/mean rates, and derives the centered graph-norm limit.

No raw realization, direct moment convergence, continuum measure, transfer
pin, or vacuum pin is constructed here.
-/

import YMGap.Continuum.BF4PhysicalDenseStageQualitativeVacuumCompiler

namespace YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler

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

/-! ## 1. The minimal representative transfer lift -/

/-- A chosen Cauchy representative of the selected transfer, with the exact
termwise observable-shift law used by the direct moment comparison.  Unlike
`WilsonPointwiseLinearTimeTranslationPin`, this interface asks for no
additivity or scalar homogeneity of the completed transfer. -/
structure WilsonPointwiseRepresentativeTimeTranslationPin
    {A : ObservableMeasure.ObsAlg}
    {W : WilsonGNS.WilsonGNSData A}
    (P : WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin W) :
    Type 2 where
  transferredRepresentative :
    CauchyGNS W.toGNSData -> CauchyGNS W.toGNSData
  transferredRepresentative_class : forall X,
    Quotient.mk (cauchySetoid W.toGNSData) (transferredRepresentative X) =
      P.op.T (Quotient.mk (cauchySetoid W.toGNSData) X)
  pointwise : forall (X : CauchyGNS W.toGNSData) (n : Nat),
    W.toGNSData.veq
      ((transferredRepresentative X).seq n)
      (P.tau (X.seq n))

namespace WilsonPointwiseRepresentativeTimeTranslationPin

/-- The former pointwise linear pin refines the representative-only pin. -/
def ofLinear
    {A : ObservableMeasure.ObsAlg}
    {W : WilsonGNS.WilsonGNSData A}
    {P : WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin W}
    (L : WilsonPointwiseLinearTimeTranslationPin P) :
    WilsonPointwiseRepresentativeTimeTranslationPin P where
  transferredRepresentative := L.linear.linearOperator.TCauchy
  transferredRepresentative_class := by
    intro X
    rw [<- L.linear.operatorPinned]
    exact (L.linear.linearOperator.T_ofCauchy X).symm
  pointwise := L.pointwise

end WilsonPointwiseRepresentativeTimeTranslationPin

/-! ## 2. The weaker direct-moment input -/

/-- Dense-stage data with direct finite-to-continuum raw moment moduli.  No
rational stage functional or intermediate projective diagonal occurs in this
interface. -/
structure BF4WilsonDenseStageCenteredVacuumQualitativeDirectBase
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
  representativeTimeTranslation :
    WilsonPointwiseRepresentativeTimeTranslationPin D.timeTranslation
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
  directMoments : BF4RawStageContinuumMomentModulus D rawStageObservable
  vacuumPin : WilsonDenseUnitVacuumPin D

namespace BF4WilsonDenseStageCenteredVacuumQualitativeDirectBase

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

/-- The older two-leg projective base constructs the weaker direct base. -/
def ofProjectiveBase
    (base : BF4WilsonDenseStageCenteredVacuumQualitativeProjectiveBase
      producer D) :
    BF4WilsonDenseStageCenteredVacuumQualitativeDirectBase producer D where
  separatorPinned := base.separatorPinned
  representativeTimeTranslation :=
    WilsonPointwiseRepresentativeTimeTranslationPin.ofLinear
      base.pointwiseTimeTranslation
  rawStageObservable := base.rawStageObservable
  rawStageTransfer_intertwines := base.rawStageTransfer_intertwines
  directMoments := base.rawMoments.toContinuumMomentModulus
  vacuumPin := base.vacuumPin

/-- Exact same-stage semantics specialize the direct base through the proved
zero-rate raw moment and half-error projective adapters. -/
def ofSemanticBase
    (base : BF4WilsonDenseStageCenteredVacuumQualitativeSemanticBase
      producer D) :
    BF4WilsonDenseStageCenteredVacuumQualitativeDirectBase producer D :=
  ofProjectiveBase base.toQualitativeProjectiveBase

end BF4WilsonDenseStageCenteredVacuumQualitativeDirectBase

/-! ## 3. Four-rate slow diagonal -/

namespace BF4WilsonDenseStageDirectMomentCompiler

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
    (base : BF4WilsonDenseStageCenteredVacuumQualitativeDirectBase
      producer D)

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
        (centeredStageObservable base scale a))
      (centeredStageObservable base scale (D.timeTranslation.tau a)) :=
  centralPhysicalCenteredTransfer_rad_of_raw
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (base.rawStageObservable scale a)
    (base.rawStageObservable scale (D.timeTranslation.tau a))
    (base.rawStageTransfer_intertwines scale a)

/-- The four rates for the square/mean of a selected representative and its
one-step translate. -/
def requirement (X : SelectedWilsonCauchy D) (index : Nat) : Nat :=
  max
    (max
      (base.directMoments.regularSquareRate (X.seq index)
        (Q'.invSucc index))
      (base.directMoments.regularSquareRate
        (D.timeTranslation.tau (X.seq index)) (Q'.invSucc index)))
    (max
      (base.directMoments.regularMeanRate (X.seq index)
        (Q'.invSucc index))
      (base.directMoments.regularMeanRate
        (D.timeTranslation.tau (X.seq index)) (Q'.invSucc index)))

def sampleRate (X : SelectedWilsonCauchy D) (threshold : Nat) : Nat :=
  slowThreshold (requirement base X) threshold

def sampleIndex (X : SelectedWilsonCauchy D) (scale : Nat) : Nat :=
  slowIndex (requirement base X) scale

def diagonalRate (X : SelectedWilsonCauchy D) (epsilon : Q') : Nat :=
  sampleRate base X (CReal.lv epsilon)

theorem sampleIndex_cofinal (X : SelectedWilsonCauchy D)
    (threshold scale : Nat)
    (hscale : sampleRate base X threshold <= scale) :
    threshold <= sampleIndex base X scale :=
  slowIndex_cofinal (requirement base X) threshold scale hscale

private theorem selected_requirement_paid (X : SelectedWilsonCauchy D)
    (epsilon : Q') (scale : Nat)
    (hscale : diagonalRate base X epsilon <= scale) :
    requirement base X (sampleIndex base X scale) <= scale := by
  have hzeroRate : sampleRate base X 0 <=
      sampleRate base X (CReal.lv epsilon) :=
    slowThreshold_mono (requirement base X) (Nat.zero_le _)
  exact required_slowIndex_le (requirement base X) scale
    (Nat.le_trans hzeroRate hscale)

private theorem selected_precision (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : diagonalRate base X epsilon <= scale) :
    Q'.invSucc (sampleIndex base X scale) <= epsilon := by
  have hprecision : CReal.lv epsilon <= sampleIndex base X scale :=
    sampleIndex_cofinal base X (CReal.lv epsilon) scale hscale
  exact Q'.le_trans' _ _ _
    (ExpNeg.invSucc_le_of_le hprecision)
    (CReal.invSucc_lv_le hepsilon)

theorem square_diagonal_admissible (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : diagonalRate base X epsilon <= scale) :
    let a := X.seq (sampleIndex base X scale)
    base.directMoments.regularSquareRate a epsilon <= scale /\
      base.directMoments.regularSquareRate
        (D.timeTranslation.tau a) epsilon <= scale := by
  let index := sampleIndex base X scale
  have hrequired := selected_requirement_paid base X epsilon scale hscale
  have hindexepsilon := selected_precision base X epsilon hepsilon scale hscale
  have hordinary := base.directMoments.regularSquareRate_antitone
    (X.seq index) (Q'.invSucc_pos index) hindexepsilon
  have htranslated := base.directMoments.regularSquareRate_antitone
    (D.timeTranslation.tau (X.seq index))
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

theorem mean_diagonal_admissible (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : diagonalRate base X epsilon <= scale) :
    let a := X.seq (sampleIndex base X scale)
    base.directMoments.regularMeanRate a epsilon <= scale /\
      base.directMoments.regularMeanRate
        (D.timeTranslation.tau a) epsilon <= scale := by
  let index := sampleIndex base X scale
  have hrequired := selected_requirement_paid base X epsilon scale hscale
  have hindexepsilon := selected_precision base X epsilon hepsilon scale hscale
  have hordinary := base.directMoments.regularMeanRate_antitone
    (X.seq index) (Q'.invSucc_pos index) hindexepsilon
  have htranslated := base.directMoments.regularMeanRate_antitone
    (D.timeTranslation.tau (X.seq index))
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

/-! ## 4. Direct comparison streams -/

def rawSquareSequence (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (sampleIndex base X scale)
    CReal.ofQ'
      (finiteStageSquareExpectation D base.rawStageObservable scale a)

def translatedRawSquareSequence (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (sampleIndex base X scale)
    CReal.ofQ' (finiteStageSquareExpectation D base.rawStageObservable
      scale (D.timeTranslation.tau a))

def rawMeanSequence (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (sampleIndex base X scale)
    CReal.ofQ' (finiteStageRawMean D base.rawStageObservable scale a)

def translatedRawMeanSequence (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale =>
    let a := X.seq (sampleIndex base X scale)
    CReal.ofQ' (finiteStageRawMean D base.rawStageObservable scale
      (D.timeTranslation.tau a))

def rawSquareContinuumClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose (rawSquareSequence base X)
      (continuumDenseNormSequence D (sampleIndex base X) X) where
  stageRate := diagonalRate base X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale k _
    rw [continuumDenseNormSequence_approx]
    let a := X.seq (sampleIndex base X scale)
    have hadmissible := (square_diagonal_admissible base
      X epsilon hepsilon scale hscale).1
    have hbound := base.directMoments.regularSquareBound
      a epsilon hepsilon scale hadmissible
    rw [continuumForm_eq_continuumSquareExpectation D a]
    exact hbound

def translatedRawSquareContinuumClose (X : SelectedWilsonCauchy D) :
    let TX := base.representativeTimeTranslation.transferredRepresentative X
    CRealEventuallyClose (translatedRawSquareSequence base X)
      (continuumDenseNormSequence D (sampleIndex base X) TX) := by
  let TX := base.representativeTimeTranslation.transferredRepresentative X
  exact {
    stageRate := diagonalRate base X
    approxRate := fun _ _ => 0
    close := by
      intro epsilon hepsilon scale hscale k _
      rw [continuumDenseNormSequence_approx]
      let a := X.seq (sampleIndex base X scale)
      let Ta := D.timeTranslation.tau a
      have hadmissible := (square_diagonal_admissible base
        X epsilon hepsilon scale hscale).2
      have hbound := base.directMoments.regularSquareBound
        Ta epsilon hepsilon scale hadmissible
      have hpointwise : D.wilson.toGNSData.veq
          (TX.seq (sampleIndex base X scale)) Ta :=
        base.representativeTimeTranslation.pointwise X
          (sampleIndex base X scale)
      have hform :
          (D.wilson.toGNSData.B
            (TX.seq (sampleIndex base X scale))
            (TX.seq (sampleIndex base X scale))).eqv
            (continuumSquareExpectation D Ta) :=
        Q'.eqv_trans _ _ _
          (D.wilson.toGNSData.B_diag_congr hpointwise)
          (Q'.eqv_of_eq (continuumForm_eq_continuumSquareExpectation D Ta))
      exact
        ⟨le_of_le_eqv hbound.1
            (Q'.add_eqv_congr_right _ _ epsilon (Q'.eqv_symm hform)),
          le_of_eqv_le hform hbound.2⟩
  }

def rawMeanContinuumClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose (rawMeanSequence base X)
      (continuumDenseVacuumPairingSequence D (sampleIndex base X) X) where
  stageRate := diagonalRate base X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale _ _
    let a := X.seq (sampleIndex base X scale)
    have hadmissible := (mean_diagonal_admissible base
      X epsilon hepsilon scale hscale).1
    have hbound := base.directMoments.regularMeanBound
      a epsilon hepsilon scale hadmissible
    rw [← WilsonDenseUnitVacuumPairingModulus.pairing_eq_continuumVacuumPairingExpectation
      (D := D) a] at hbound
    exact hbound

def translatedRawMeanContinuumClose (X : SelectedWilsonCauchy D) :
    CRealEventuallyClose (translatedRawMeanSequence base X)
      (fun scale => CReal.ofQ'
        (D.wilson.toGNSData.B
          (D.timeTranslation.tau (X.seq (sampleIndex base X scale)))
          H.os_axioms.A.one)) where
  stageRate := diagonalRate base X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale _ _
    let a := X.seq (sampleIndex base X scale)
    let Ta := D.timeTranslation.tau a
    have hadmissible := (mean_diagonal_admissible base
      X epsilon hepsilon scale hscale).2
    have hbound := base.directMoments.regularMeanBound
      Ta epsilon hepsilon scale hadmissible
    rw [← WilsonDenseUnitVacuumPairingModulus.pairing_eq_continuumVacuumPairingExpectation
      (D := D) Ta] at hbound
    exact hbound

theorem rawSquareSequence_converges (X : SelectedWilsonCauchy D) :
    CReal.ConvergesTo (rawSquareSequence base X)
      (D.wilson.toGNSData.cinnerRep X X) :=
  convergesTo_of_eventuallyClose (rawSquareContinuumClose base X)
    (continuumDenseNormSequence_converges D
      (sampleIndex base X) (sampleRate base X)
      (sampleIndex_cofinal base X) X)

theorem translatedRawSquareSequence_converges
    (X : SelectedWilsonCauchy D) :
    let TX := base.representativeTimeTranslation.transferredRepresentative X
    CReal.ConvergesTo (translatedRawSquareSequence base X)
      (D.wilson.toGNSData.cinnerRep TX TX) := by
  let TX := base.representativeTimeTranslation.transferredRepresentative X
  exact convergesTo_of_eventuallyClose
    (translatedRawSquareContinuumClose base X)
    (continuumDenseNormSequence_converges D
      (sampleIndex base X) (sampleRate base X)
      (sampleIndex_cofinal base X) TX)

theorem rawMeanSequence_converges_zero
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo (rawMeanSequence base X) CReal.czero :=
  convergesTo_of_eventuallyClose (rawMeanContinuumClose base X)
    (continuumDenseVacuumPairingSequence_converges_zero
      base.vacuumPin (sampleIndex base X) (sampleRate base X)
      (sampleIndex_cofinal base X) X horthogonal)

theorem translatedRawMeanSequence_converges_zero
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo (translatedRawMeanSequence base X) CReal.czero :=
  convergesTo_of_eventuallyClose (translatedRawMeanContinuumClose base X) (by
    let TX := base.representativeTimeTranslation.transferredRepresentative X
    have hTXOrthogonal :
        D.selectedSpectralData.vacPerp (selectedWilsonPoint D TX) := by
      change D.selectedSpectralData.vacPerp
        (Quotient.mk (cauchySetoid D.wilson.toGNSData)
          (base.representativeTimeTranslation.transferredRepresentative X))
      rw [base.representativeTimeTranslation.transferredRepresentative_class X]
      exact base.vacuumPin.toStationarity.transfer_preservesVacPerp horthogonal
    have hTX := continuumDenseVacuumPairingSequence_converges_zero
      base.vacuumPin (sampleIndex base X) (sampleRate base X)
      (sampleIndex_cofinal base X) TX hTXOrthogonal
    apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (s := continuumDenseVacuumPairingSequence D (sampleIndex base X) TX)
    · intro scale
      exact CReal.ofQ'_equiv_of_eqv
        (D.wilson.toGNSData.B_congr_left H.os_axioms.A.one
          (base.representativeTimeTranslation.pointwise X
            (sampleIndex base X scale)))
    · exact hTX)

/-! ## 5. Centering and graph-norm contraction -/

private theorem creal_ofQ'_centered_equiv (raw mean : Q') :
    CReal.Equiv
      (CReal.ofQ' (raw + -(mean * mean)))
      (CReal.add (CReal.ofQ' raw)
        (CReal.neg (CReal.mul (CReal.ofQ' mean) (CReal.ofQ' mean)))) :=
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

theorem norm_converges
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo
      (adaptiveDenseStageNormSequence D (sampleIndex base)
        (centeredStageObservable base) X)
      (D.wilson.toGNSData.cinnerRep X X) := by
  let rawSeq := rawSquareSequence base X
  let meanSeq := rawMeanSequence base X
  have hraw : CReal.ConvergesTo rawSeq
      (D.wilson.toGNSData.cinnerRep X X) := by
    simpa only [rawSeq] using rawSquareSequence_converges base X
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    simpa only [meanSeq] using rawMeanSequence_converges_zero base X horthogonal
  have hsquare := CReal.convergesTo_mul_general hmean hmean
  have hsquareZero : CReal.ConvergesTo
      (fun scale => CReal.mul (meanSeq scale) (meanSeq scale)) CReal.czero :=
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
    let a := X.seq (sampleIndex base X scale)
    let raw := finiteStageSquareExpectation D base.rawStageObservable scale a
    let mean := finiteStageRawMean D base.rawStageObservable scale a
    have hcentered := finiteStageCenteredSquare_identity
      D base.rawStageObservable scale a
    exact CReal.Equiv.trans
      (CReal.Equiv.symm (creal_ofQ'_centered_equiv raw mean))
      (CReal.Equiv.symm (CReal.ofQ'_equiv_of_eqv hcentered))
  · simpa only [rawSeq, meanSeq, rawSquareSequence, rawMeanSequence,
      adaptiveDenseStageNormSequence_approx] using hcenteredLimit

theorem transferredNorm_converges
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo
      (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
        (adaptiveDenseStageApproximant D (sampleIndex base)
          (centeredStageObservable base) X scale))
      (D.wilson.toGNSData.cinnerRep
        (base.representativeTimeTranslation.transferredRepresentative X)
        (base.representativeTimeTranslation.transferredRepresentative X)) := by
  let TX := base.representativeTimeTranslation.transferredRepresentative X
  let rawSeq := translatedRawSquareSequence base X
  let meanSeq := translatedRawMeanSequence base X
  have hraw : CReal.ConvergesTo rawSeq
      (D.wilson.toGNSData.cinnerRep TX TX) := by
    simpa only [rawSeq, TX] using translatedRawSquareSequence_converges base X
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    simpa only [meanSeq] using
      translatedRawMeanSequence_converges_zero base X horthogonal
  have hsquare := CReal.convergesTo_mul_general hmean hmean
  have hsquareZero : CReal.ConvergesTo
      (fun scale => CReal.mul (meanSeq scale) (meanSeq scale)) CReal.czero :=
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
    let a := X.seq (sampleIndex base X scale)
    let Ta := D.timeTranslation.tau a
    let raw := finiteStageSquareExpectation D base.rawStageObservable scale Ta
    let mean := finiteStageRawMean D base.rawStageObservable scale Ta
    have hcentered := finiteStageCenteredSquare_identity
      D base.rawStageObservable scale Ta
    have htransfer :
        ((MatchedPhysicalStageGNSData family coupling scale).B
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0
            (centeredStageObservable base scale a))
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0
            (centeredStageObservable base scale a))).eqv
          (finiteStageSquareExpectation D
            (centeredStageObservable base) scale Ta) :=
      (MatchedPhysicalStageGNSData family coupling scale).B_welldef
        (centeredStageTransfer_intertwines base scale a)
        (centeredStageTransfer_intertwines base scale a)
    exact CReal.Equiv.trans
      (CReal.Equiv.symm (creal_ofQ'_centered_equiv raw mean))
      (CReal.Equiv.trans
        (CReal.Equiv.symm (CReal.ofQ'_equiv_of_eqv hcentered))
        (CReal.Equiv.symm (CReal.ofQ'_equiv_of_eqv htransfer)))
  · simpa only [rawSeq, meanSeq, translatedRawSquareSequence,
      translatedRawMeanSequence, matchedPhysicalStageTransferredNorm,
      adaptiveDenseStageApproximant, denseStageApproximant, constCauchy]
      using hcenteredLimit

def toVacuumRepresentativeGraphNormLimitApproximation :
    BF4WilsonVacuumRepresentativeGraphNormLimitApproximation producer D where
  separatorPinned := base.separatorPinned
  transferredRepresentative :=
    base.representativeTimeTranslation.transferredRepresentative
  transferredRepresentative_class :=
    base.representativeTimeTranslation.transferredRepresentative_class
  approximant := fun X scale =>
    adaptiveDenseStageApproximant D (sampleIndex base)
      (centeredStageObservable base) X scale
  approximant_vacuumOrthogonal := by
    intro X _ scale
    exact centralPhysicalModulatedEmbedV_vacuumOrthogonal_of_meanZero
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (centeredStageObservable base scale
        (X.seq (sampleIndex base X scale)))
      (centralPhysicalCenteredObservable_meanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (base.rawStageObservable scale
          (X.seq (sampleIndex base X scale))))
  norm_converges := norm_converges base
  transferredNorm_converges := transferredNorm_converges base

def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  (toVacuumRepresentativeGraphNormLimitApproximation base).toWilsonOperatorNormGapPin

end BF4WilsonDenseStageDirectMomentCompiler

end YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler

#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageCenteredVacuumQualitativeDirectBase.ofProjectiveBase
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageCenteredVacuumQualitativeDirectBase.ofSemanticBase
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.WilsonPointwiseRepresentativeTimeTranslationPin.ofLinear
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageDirectMomentCompiler.sampleIndex_cofinal
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageDirectMomentCompiler.square_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageDirectMomentCompiler.mean_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageDirectMomentCompiler.rawSquareSequence_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageDirectMomentCompiler.rawMeanSequence_converges_zero
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageDirectMomentCompiler.norm_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageDirectMomentCompiler.transferredNorm_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageDirectMomentCompiler.toVacuumRepresentativeGraphNormLimitApproximation
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDirectMomentCompiler.BF4WilsonDenseStageDirectMomentCompiler.toWilsonOperatorNormGapPin
