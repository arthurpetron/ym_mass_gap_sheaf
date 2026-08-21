/-
# Centered raw-stage compiler for the physical BF4 slow diagonal

The slow-diagonal endpoint needs finite stage observables that are exactly
mean zero and whose transfer intertwines continuum time translation modulo the
physical GNS radical.  Both facts are automatic after exact stationary
centering of a raw finite realization.

This module packages that reduction and constructs a vector-adaptive slow
diagonal from fixed-observable projective and raw-moment moduli.  The exact
centering identity is compiled in the downstream raw-square/raw-mean module.
No thermodynamic or continuum estimate is proved here.
-/

import YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining
import YMGap.Continuum.BF4PhysicalDenseStageRawMomentModulus
import YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
import YMGap.Continuum.BF4PhysicalVacuumGraphNormLimitStability
import YMGap.Continuum.BF4PhysicalVacuumPairingModulus

namespace YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageRationalComparison
open YMGap.Continuum.BF4PhysicalDenseStageRawMomentModulus
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence
open YMGap.Continuum.BF4PhysicalVacuumGraphNormLimitStability
open YMGap.Continuum.BF4PhysicalVacuumPairingModulus
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.WilsonLinearTimeTranslationHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-- Exact stationary centering of a raw finite-stage realization. -/
def matchedCenteredStageObservable
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (rawStageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (scale : Nat) (observable : D.wilson.toGNSData.V) :
    (MatchedPhysicalStageGNSData family coupling scale).V :=
  centralPhysicalCenteredObservable
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (rawStageObservable scale observable)

/-- Raw dense realization data with the genuinely remaining comparison made
against the exact centered finite square. -/
structure BF4WilsonDenseStageCenteredSlowProjectiveCore
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
  rawStageObservable_congr : forall scale : Nat,
    forall {a b : D.wilson.toGNSData.V}, D.wilson.toGNSData.veq a b ->
      (MatchedPhysicalStageGNSData family coupling scale).veq
        (rawStageObservable scale a) (rawStageObservable scale b)
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
  centeredFiniteSquarePinned : forall (scale : Nat)
    (observable : D.wilson.toGNSData.V),
      (finiteStageSquareExpectation D
        (matchedCenteredStageObservable D rawStageObservable)
        scale observable).eqv
        (rationalFunctional.stageExpectationQ scale (mu.pick scale)
          (continuumSquareObservable D observable))

namespace BF4WilsonDenseStageCenteredSlowProjectiveCore

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
    (data : BF4WilsonDenseStageCenteredSlowProjectiveCore producer D)

/-- Centering preserves the raw realization's carrier congruence. -/
theorem centeredStageObservable_congr (scale : Nat)
    {a b : D.wilson.toGNSData.V} (hab : D.wilson.toGNSData.veq a b) :
    (MatchedPhysicalStageGNSData family coupling scale).veq
      (matchedCenteredStageObservable D data.rawStageObservable scale a)
      (matchedCenteredStageObservable D data.rawStageObservable scale b) := by
  exact centralPhysicalCenteredObservable_congr
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (data.rawStageObservable_congr scale hab)

/-- Raw radical intertwining compiles to centered radical intertwining. -/
theorem centeredStageTransfer_intertwines (scale : Nat)
    (a : D.wilson.toGNSData.V) :
    (MatchedPhysicalStageGNSData family coupling scale).rad
      (centralPhysicalMarkovApply
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (matchedCenteredStageObservable D data.rawStageObservable scale a))
      (matchedCenteredStageObservable D data.rawStageObservable scale
        (D.timeTranslation.tau a)) := by
  exact centralPhysicalCenteredTransfer_rad_of_raw
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (data.rawStageObservable scale a)
    (data.rawStageObservable scale (D.timeTranslation.tau a))
    (data.rawStageTransfer_intertwines scale a)

/-- Compile raw stage data and the centered-square pin into the existing slow
projective core. -/
def toSlowProjectiveCore :
    BF4WilsonDenseStageSlowProjectiveCore producer D where
  separatorPinned := data.separatorPinned
  pointwiseTimeTranslation := data.pointwiseTimeTranslation
  stageObservable := matchedCenteredStageObservable D data.rawStageObservable
  stageObservable_congr := data.centeredStageObservable_congr
  stageTransfer_intertwines := data.centeredStageTransfer_intertwines
  rationalFunctional := data.rationalFunctional
  finiteSquarePinned := data.centeredFiniteSquarePinned

/-- Exact centering constructs the mean-zero slow-projective comparison; no
separate vacuum-complement field remains. -/
def toSlowProjectiveComparison :
    BF4WilsonDenseStageSlowProjectiveComparison producer D where
  core := data.toSlowProjectiveCore
  stage_meanZero := by
    intro X _ scale
    exact centralPhysicalCenteredObservable_meanZero
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (data.rawStageObservable scale
        (X.seq (data.toSlowProjectiveCore.sampleIndex X scale)))

/-- The centered raw-stage data reaches the selected continuum operator gap
through the constructed slow diagonal. -/
def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  data.toSlowProjectiveComparison.toWilsonOperatorNormGapPin

end BF4WilsonDenseStageCenteredSlowProjectiveCore

/-! ## Conditional centered comparison on the continuum vacuum complement -/

/-- Raw realization and projective data before the genuinely diagonal
centered finite/continuum estimate is supplied. -/
structure BF4WilsonDenseStageCenteredVacuumProjectiveBase
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
  rawStageObservable_congr : forall scale : Nat,
    forall {a b : D.wilson.toGNSData.V}, D.wilson.toGNSData.veq a b ->
      (MatchedPhysicalStageGNSData family coupling scale).veq
        (rawStageObservable scale a) (rawStageObservable scale b)
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
  rawMoments : BF4RawStageMomentModulus D rawStageObservable
    rationalFunctional
  vacuumPairing : WilsonDenseUnitVacuumPairingModulus D

namespace BF4WilsonDenseStageCenteredVacuumProjectiveBase

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
    (base : BF4WilsonDenseStageCenteredVacuumProjectiveBase producer D)

def centeredStageObservable (scale : Nat)
    (observable : D.wilson.toGNSData.V) :
    (MatchedPhysicalStageGNSData family coupling scale).V :=
  matchedCenteredStageObservable D base.rawStageObservable scale observable

theorem centeredStageObservable_congr (scale : Nat)
    {a b : D.wilson.toGNSData.V} (hab : D.wilson.toGNSData.veq a b) :
    (MatchedPhysicalStageGNSData family coupling scale).veq
      (base.centeredStageObservable scale a)
      (base.centeredStageObservable scale b) := by
  exact centralPhysicalCenteredObservable_congr
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (base.rawStageObservable_congr scale hab)

theorem centeredStageTransfer_intertwines (scale : Nat)
    (a : D.wilson.toGNSData.V) :
    (MatchedPhysicalStageGNSData family coupling scale).rad
      (centralPhysicalMarkovApply
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (base.centeredStageObservable scale a))
      (base.centeredStageObservable scale (D.timeTranslation.tau a)) := by
  exact centralPhysicalCenteredTransfer_rad_of_raw
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (base.rawStageObservable scale a)
    (base.rawStageObservable scale (D.timeTranslation.tau a))
    (base.rawStageTransfer_intertwines scale a)

def regularizedFunctional : ProjectiveOSRationalModulus D :=
  regularizedProjectiveModulus base.rationalFunctional

def projectiveRequirement (X : SelectedWilsonCauchy D)
    (index : Nat) : Nat :=
  max
    (max
      (base.regularizedFunctional.rate
        (continuumSquareObservable D (X.seq index))
        (Q'.invSucc index))
      (base.regularizedFunctional.rate
        (continuumSquareObservable D
          (D.timeTranslation.tau (X.seq index)))
        (Q'.invSucc index)))
    (max
      (base.regularizedFunctional.rate
        (continuumVacuumPairingObservable D (X.seq index))
        (Q'.invSucc index))
      (base.regularizedFunctional.rate
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

/-- All pointwise rates that the selected slow term must pay: four projective
evaluator rates and four raw finite/projective moment rates. -/
def requirement (X : SelectedWilsonCauchy D) (index : Nat) : Nat :=
  max (base.projectiveRequirement X index) (base.rawRequirement X index)

def sampleRate (X : SelectedWilsonCauchy D) (threshold : Nat) : Nat :=
  slowThreshold (base.requirement X) threshold

def sampleIndex (X : SelectedWilsonCauchy D) (scale : Nat) : Nat :=
  slowIndex (base.requirement X) scale

def projectiveDiagonalRate (X : SelectedWilsonCauchy D)
    (epsilon : Q') : Nat :=
  base.sampleRate X (CReal.lv epsilon)

/-- The outer rate making the cofinal sampler reach both explicit
vacuum-pairing moduli. -/
def vacuumPairingDiagonalRate (X : SelectedWilsonCauchy D)
    (epsilon : Q') : Nat :=
  base.sampleRate X
    (max
      (base.vacuumPairing.regularPairingRate X epsilon)
      (base.vacuumPairing.regularTransferredPairingRate
        base.pointwiseTimeTranslation X epsilon))

theorem sampleIndex_cofinal (X : SelectedWilsonCauchy D)
    (threshold scale : Nat)
    (hscale : base.sampleRate X threshold <= scale) :
    threshold <= base.sampleIndex X scale :=
  slowIndex_cofinal (base.requirement X) threshold scale hscale

theorem projective_diagonal_admissible (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : base.projectiveDiagonalRate X epsilon <= scale) :
    let a := X.seq (base.sampleIndex X scale)
    base.regularizedFunctional.rate
        (continuumSquareObservable D a) epsilon <= scale /\
      base.regularizedFunctional.rate
        (continuumSquareObservable D (D.timeTranslation.tau a)) epsilon <=
          scale := by
  let precision := CReal.lv epsilon
  let index := base.sampleIndex X scale
  have hprecision : precision <= index :=
    base.sampleIndex_cofinal X precision scale hscale
  have hzeroRate : base.sampleRate X 0 <= base.sampleRate X precision :=
    slowThreshold_mono (base.requirement X) (Nat.zero_le precision)
  have hzero : base.sampleRate X 0 <= scale :=
    Nat.le_trans hzeroRate hscale
  have hrequired : base.requirement X index <= scale :=
    required_slowIndex_le (base.requirement X) scale hzero
  have hindexepsilon : Q'.invSucc index <= epsilon :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hprecision)
      (CReal.invSucc_lv_le hepsilon)
  have hordinary : base.regularizedFunctional.rate
      (continuumSquareObservable D (X.seq index)) epsilon <=
      base.regularizedFunctional.rate
        (continuumSquareObservable D (X.seq index))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone base.rationalFunctional
      (continuumSquareObservable D (X.seq index))
      (Q'.invSucc_pos index) hindexepsilon
  have htranslated : base.regularizedFunctional.rate
      (continuumSquareObservable D
        (D.timeTranslation.tau (X.seq index))) epsilon <=
      base.regularizedFunctional.rate
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

/-- The same constructed slow diagonal pays the two projective rates for the
ordinary and translated vacuum-pairing observables. -/
theorem projective_pairing_diagonal_admissible
    (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : base.projectiveDiagonalRate X epsilon <= scale) :
    let a := X.seq (base.sampleIndex X scale)
    base.regularizedFunctional.rate
        (continuumVacuumPairingObservable D a) epsilon <= scale /\
      base.regularizedFunctional.rate
        (continuumVacuumPairingObservable D
          (D.timeTranslation.tau a)) epsilon <= scale := by
  let precision := CReal.lv epsilon
  let index := base.sampleIndex X scale
  have hprecision : precision <= index :=
    base.sampleIndex_cofinal X precision scale hscale
  have hzeroRate : base.sampleRate X 0 <= base.sampleRate X precision :=
    slowThreshold_mono (base.requirement X) (Nat.zero_le precision)
  have hzero : base.sampleRate X 0 <= scale :=
    Nat.le_trans hzeroRate hscale
  have hrequired : base.requirement X index <= scale :=
    required_slowIndex_le (base.requirement X) scale hzero
  have hindexepsilon : Q'.invSucc index <= epsilon :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hprecision)
      (CReal.invSucc_lv_le hepsilon)
  have hordinary : base.regularizedFunctional.rate
      (continuumVacuumPairingObservable D (X.seq index)) epsilon <=
      base.regularizedFunctional.rate
        (continuumVacuumPairingObservable D (X.seq index))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone base.rationalFunctional
      (continuumVacuumPairingObservable D (X.seq index))
      (Q'.invSucc_pos index) hindexepsilon
  have htranslated : base.regularizedFunctional.rate
      (continuumVacuumPairingObservable D
        (D.timeTranslation.tau (X.seq index))) epsilon <=
      base.regularizedFunctional.rate
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

/-- The constructed slow diagonal also pays the two fixed-observable
raw-square rates for the representatives it selects. -/
theorem raw_square_diagonal_admissible
    (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : base.projectiveDiagonalRate X epsilon <= scale) :
    let a := X.seq (base.sampleIndex X scale)
    base.rawMoments.regularSquareRate a epsilon <= scale /\
      base.rawMoments.regularSquareRate
        (D.timeTranslation.tau a) epsilon <= scale := by
  let precision := CReal.lv epsilon
  let index := base.sampleIndex X scale
  have hprecision : precision <= index :=
    base.sampleIndex_cofinal X precision scale hscale
  have hzeroRate : base.sampleRate X 0 <= base.sampleRate X precision :=
    slowThreshold_mono (base.requirement X) (Nat.zero_le precision)
  have hzero : base.sampleRate X 0 <= scale :=
    Nat.le_trans hzeroRate hscale
  have hrequired : base.requirement X index <= scale :=
    required_slowIndex_le (base.requirement X) scale hzero
  have hindexepsilon : Q'.invSucc index <= epsilon :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hprecision)
      (CReal.invSucc_lv_le hepsilon)
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

/-- The constructed slow diagonal also pays the two fixed-observable
raw-mean rates for the representatives it selects. -/
theorem raw_mean_diagonal_admissible
    (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : base.projectiveDiagonalRate X epsilon <= scale) :
    let a := X.seq (base.sampleIndex X scale)
    base.rawMoments.regularMeanRate a epsilon <= scale /\
      base.rawMoments.regularMeanRate
        (D.timeTranslation.tau a) epsilon <= scale := by
  let precision := CReal.lv epsilon
  let index := base.sampleIndex X scale
  have hprecision : precision <= index :=
    base.sampleIndex_cofinal X precision scale hscale
  have hzeroRate : base.sampleRate X 0 <= base.sampleRate X precision :=
    slowThreshold_mono (base.requirement X) (Nat.zero_le precision)
  have hzero : base.sampleRate X 0 <= scale :=
    Nat.le_trans hzeroRate hscale
  have hrequired : base.requirement X index <= scale :=
    required_slowIndex_le (base.requirement X) scale hzero
  have hindexepsilon : Q'.invSucc index <= epsilon :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hprecision)
      (CReal.invSucc_lv_le hepsilon)
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

/-- Fixed-observable raw-square estimates become a uniform comparison along
the vector-adaptive slow diagonal selected by `base`. -/
theorem raw_square_diagonal_comparison
    (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : base.projectiveDiagonalRate X epsilon <= scale) :
    let index := base.sampleIndex X scale
    let a := X.seq index
    let Ta := D.timeTranslation.tau a
    let finiteA := finiteStageSquareExpectation D
      base.rawStageObservable scale a
    let finiteTa := finiteStageSquareExpectation D
      base.rawStageObservable scale Ta
    let rationalA := base.regularizedFunctional.stageExpectationQ
      scale (mu.pick scale) (continuumSquareObservable D a)
    let rationalTa := base.regularizedFunctional.stageExpectationQ
      scale (mu.pick scale) (continuumSquareObservable D Ta)
    (finiteA <= rationalA + epsilon /\ rationalA <= finiteA + epsilon) /\
      (finiteTa <= rationalTa + epsilon /\
        rationalTa <= finiteTa + epsilon) := by
  have hadmissible := base.raw_square_diagonal_admissible
    X epsilon hepsilon scale hscale
  dsimp only
  exact
    ⟨base.rawMoments.regularSquareBound _ epsilon hepsilon scale
        hadmissible.1,
      base.rawMoments.regularSquareBound _ epsilon hepsilon scale
        hadmissible.2⟩

/-- Fixed-observable raw-mean estimates become a uniform comparison along
the vector-adaptive slow diagonal selected by `base`. -/
theorem raw_mean_diagonal_comparison
    (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : base.projectiveDiagonalRate X epsilon <= scale) :
    let index := base.sampleIndex X scale
    let a := X.seq index
    let Ta := D.timeTranslation.tau a
    let finiteA := finiteStageRawMean D base.rawStageObservable scale a
    let finiteTa := finiteStageRawMean D base.rawStageObservable scale Ta
    let rationalA := base.regularizedFunctional.stageExpectationQ
      scale (mu.pick scale) (continuumVacuumPairingObservable D a)
    let rationalTa := base.regularizedFunctional.stageExpectationQ
      scale (mu.pick scale) (continuumVacuumPairingObservable D Ta)
    (finiteA <= rationalA + epsilon /\ rationalA <= finiteA + epsilon) /\
      (finiteTa <= rationalTa + epsilon /\
        rationalTa <= finiteTa + epsilon) := by
  have hadmissible := base.raw_mean_diagonal_admissible
    X epsilon hepsilon scale hscale
  dsimp only
  exact
    ⟨base.rawMoments.regularMeanBound _ epsilon hepsilon scale
        hadmissible.1,
      base.rawMoments.regularMeanBound _ epsilon hepsilon scale
        hadmissible.2⟩

/-- The same slow diagonal also pays the explicit Type-level vacuum-pairing
moduli for the ordinary and transferred representatives. -/
theorem vacuum_pairing_diagonal_small
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale : base.vacuumPairingDiagonalRate X epsilon <= scale) :
    let index := base.sampleIndex X scale
    let a := X.seq index
    (-epsilon <= D.wilson.toGNSData.B a H.os_axioms.A.one /\
        D.wilson.toGNSData.B a H.os_axioms.A.one <= epsilon) /\
      (-epsilon <= D.wilson.toGNSData.B
          (D.timeTranslation.tau a) H.os_axioms.A.one /\
        D.wilson.toGNSData.B
          (D.timeTranslation.tau a) H.os_axioms.A.one <= epsilon) := by
  let index := base.sampleIndex X scale
  have hreached :
      max
          (base.vacuumPairing.regularPairingRate X epsilon)
          (base.vacuumPairing.regularTransferredPairingRate
            base.pointwiseTimeTranslation X epsilon) <= index :=
    base.sampleIndex_cofinal X _ scale hscale
  have hordinaryPaid : base.vacuumPairing.regularPairingRate X epsilon <=
      index := by
    exact Nat.le_trans (Nat.le_max_left _ _) hreached
  have htranslatedPaid :
      base.vacuumPairing.regularTransferredPairingRate
          base.pointwiseTimeTranslation X epsilon <= index := by
    exact Nat.le_trans (Nat.le_max_right _ _) hreached
  dsimp only
  exact
    ⟨base.vacuumPairing.regularPairingSmall X horthogonal
        epsilon hepsilon index hordinaryPaid,
      base.vacuumPairing.regularTransferredPairingSmall
        base.pointwiseTimeTranslation X horthogonal
        epsilon hepsilon index htranslatedPaid⟩

end BF4WilsonDenseStageCenteredVacuumProjectiveBase

/-- The remaining analytic bridge, stated only along the constructed diagonal
and only for representatives of the continuum vacuum complement.  It compares
both the centered observable and its one-step translate with the rational
projective evaluator. -/
structure BF4WilsonDenseStageCenteredVacuumSlowComparison
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
  base : BF4WilsonDenseStageCenteredVacuumProjectiveBase producer D
  centeredComparisonRate : SelectedWilsonCauchy D -> Q' -> Nat
  centeredComparison : forall (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      forall (epsilon : Q'), (0 : Q') < epsilon ->
        forall scale : Nat, centeredComparisonRate X epsilon <= scale ->
          let index := base.sampleIndex X scale
          let a := X.seq index
          let Ta := D.timeTranslation.tau a
          let finiteA := finiteStageSquareExpectation D
            base.centeredStageObservable scale a
          let finiteTa := finiteStageSquareExpectation D
            base.centeredStageObservable scale Ta
          let rationalA := base.regularizedFunctional.stageExpectationQ
            scale (mu.pick scale) (continuumSquareObservable D a)
          let rationalTa := base.regularizedFunctional.stageExpectationQ
            scale (mu.pick scale) (continuumSquareObservable D Ta)
          (finiteA <= rationalA + epsilon /\
              rationalA <= finiteA + epsilon) /\
            (finiteTa <= rationalTa + epsilon /\
              rationalTa <= finiteTa + epsilon)

namespace BF4WilsonDenseStageCenteredVacuumSlowComparison

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
    (data : BF4WilsonDenseStageCenteredVacuumSlowComparison producer D)

private theorem half_error_chain
    (first middle last epsilon : Q')
    (hfirst : first <= middle + HalfPow.half * epsilon)
    (hsecond : middle <= last + HalfPow.half * epsilon) :
    first <= last + epsilon := by
  have hstep : middle + HalfPow.half * epsilon <=
      (last + HalfPow.half * epsilon) + HalfPow.half * epsilon :=
    Q'.add_le_add_right _ _ (HalfPow.half * epsilon) hsecond
  have hsum := Q'.le_trans' _ _ _ hfirst hstep
  exact le_of_le_eqv hsum
    (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv last
        (HalfPow.half * epsilon) (HalfPow.half * epsilon))
      (Q'.add_eqv_congr' (Q'.eqv_refl last)
        (ExpNeg.two_halves epsilon)))

def diagonalRate (X : SelectedWilsonCauchy D) (epsilon : Q') : Nat :=
  let halfEpsilon := HalfPow.half * epsilon
  max (data.base.projectiveDiagonalRate X halfEpsilon)
    (data.centeredComparisonRate X halfEpsilon)

def normClose (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CRealEventuallyClose
      (adaptiveDenseStageNormSequence D data.base.sampleIndex
        data.base.centeredStageObservable X)
      (continuumDenseNormSequence D (data.base.sampleIndex X) X) where
  stageRate := data.diagonalRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale k _
    rw [adaptiveDenseStageNormSequence_approx,
      continuumDenseNormSequence_approx]
    let halfEpsilon := HalfPow.half * epsilon
    have hhalf : (0 : Q') < halfEpsilon :=
      ExpNeg.half_mul_pos epsilon hepsilon
    have hprojectiveRate :
        data.base.projectiveDiagonalRate X halfEpsilon <= scale :=
      Nat.le_trans (Nat.le_max_left _ _) hscale
    have hcomparisonRate :
        data.centeredComparisonRate X halfEpsilon <= scale :=
      Nat.le_trans (Nat.le_max_right _ _) hscale
    let a := X.seq (data.base.sampleIndex X scale)
    have hadmissible :=
      (data.base.projective_diagonal_admissible X halfEpsilon hhalf
        scale hprojectiveRate).1
    have hprojective := data.base.regularizedFunctional.bound
      (continuumSquareObservable D a) halfEpsilon hhalf scale hadmissible
    have hcentered :=
      (data.centeredComparison X horthogonal halfEpsilon hhalf
        scale hcomparisonRate).1
    have hcontinuum : D.wilson.toGNSData.B a a =
        continuumSquareExpectation D a :=
      continuumForm_eq_continuumSquareExpectation D a
    rw [hcontinuum]
    constructor
    · exact half_error_chain _ _ _ epsilon hcentered.1 hprojective.1
    · exact half_error_chain _ _ _ epsilon hprojective.2 hcentered.2

theorem norm_converges (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo
      (adaptiveDenseStageNormSequence D data.base.sampleIndex
        data.base.centeredStageObservable X)
      (D.wilson.toGNSData.cinnerRep X X) :=
  convergesTo_of_eventuallyClose (data.normClose X horthogonal)
    (continuumDenseNormSequence_converges D
      (data.base.sampleIndex X) (data.base.sampleRate X)
      (data.base.sampleIndex_cofinal X) X)

theorem transferredNorm_approx
    (X : SelectedWilsonCauchy D) (scale k : Nat) :
    (matchedPhysicalStageTransferredNorm family coupling scale
      (adaptiveDenseStageApproximant D data.base.sampleIndex
        data.base.centeredStageObservable X scale)).approx k =
      (MatchedPhysicalStageGNSData family coupling scale).B
        (centralPhysicalMarkovApply
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (data.base.centeredStageObservable scale
            (X.seq (data.base.sampleIndex X scale))))
        (centralPhysicalMarkovApply
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (data.base.centeredStageObservable scale
            (X.seq (data.base.sampleIndex X scale)))) := by
  rfl

def transferredNormClose (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CRealEventuallyClose
      (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
        (adaptiveDenseStageApproximant D data.base.sampleIndex
          data.base.centeredStageObservable X scale))
      (continuumDenseNormSequence D (data.base.sampleIndex X)
        (data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)) where
  stageRate := data.diagonalRate X
  approxRate := fun _ _ => 0
  close := by
    intro epsilon hepsilon scale hscale k _
    rw [data.transferredNorm_approx X scale k,
      continuumDenseNormSequence_approx]
    let halfEpsilon := HalfPow.half * epsilon
    have hhalf : (0 : Q') < halfEpsilon :=
      ExpNeg.half_mul_pos epsilon hepsilon
    have hprojectiveRate :
        data.base.projectiveDiagonalRate X halfEpsilon <= scale :=
      Nat.le_trans (Nat.le_max_left _ _) hscale
    have hcomparisonRate :
        data.centeredComparisonRate X halfEpsilon <= scale :=
      Nat.le_trans (Nat.le_max_right _ _) hscale
    let a := X.seq (data.base.sampleIndex X scale)
    let Ta := D.timeTranslation.tau a
    let TX := data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X
    have hadmissible :=
      (data.base.projective_diagonal_admissible X halfEpsilon hhalf
        scale hprojectiveRate).2
    have hprojective := data.base.regularizedFunctional.bound
      (continuumSquareObservable D Ta) halfEpsilon hhalf scale hadmissible
    have hcentered :=
      (data.centeredComparison X horthogonal halfEpsilon hhalf
        scale hcomparisonRate).2
    have hfiniteTransfer :
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
            data.base.centeredStageObservable scale Ta) := by
      exact (MatchedPhysicalStageGNSData family coupling scale).B_welldef
        (data.base.centeredStageTransfer_intertwines scale a)
        (data.base.centeredStageTransfer_intertwines scale a)
    have hcenteredLeft := le_of_eqv_le hfiniteTransfer hcentered.1
    have hcenteredRight := le_of_le_eqv hcentered.2
      (Q'.add_eqv_congr_right _ _ halfEpsilon
        (Q'.eqv_symm hfiniteTransfer))
    have hpointwise : D.wilson.toGNSData.veq
        (TX.seq (data.base.sampleIndex X scale)) Ta :=
      data.base.pointwiseTimeTranslation.pointwise X
        (data.base.sampleIndex X scale)
    have hcontinuumForm :
        (D.wilson.toGNSData.B
          (TX.seq (data.base.sampleIndex X scale))
          (TX.seq (data.base.sampleIndex X scale))).eqv
          (continuumSquareExpectation D Ta) :=
      Q'.eqv_trans _ _ _
        (D.wilson.toGNSData.B_diag_congr hpointwise)
        (Q'.eqv_of_eq
          (continuumForm_eq_continuumSquareExpectation D Ta))
    have hprojectiveForward :
        data.base.regularizedFunctional.stageExpectationQ
            scale (mu.pick scale) (continuumSquareObservable D Ta) <=
          D.wilson.toGNSData.B
              (TX.seq (data.base.sampleIndex X scale))
              (TX.seq (data.base.sampleIndex X scale)) + halfEpsilon :=
      le_of_le_eqv hprojective.1
        (Q'.add_eqv_congr_right _ _ halfEpsilon
          (Q'.eqv_symm hcontinuumForm))
    have hprojectiveBackward :
        D.wilson.toGNSData.B
              (TX.seq (data.base.sampleIndex X scale))
              (TX.seq (data.base.sampleIndex X scale)) <=
          data.base.regularizedFunctional.stageExpectationQ
              scale (mu.pick scale) (continuumSquareObservable D Ta) +
            halfEpsilon :=
      le_of_eqv_le hcontinuumForm hprojective.2
    constructor
    · exact half_error_chain _ _ _ epsilon
        hcenteredLeft hprojectiveForward
    · exact half_error_chain _ _ _ epsilon
        hprojectiveBackward hcenteredRight

theorem transferredNorm_converges (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.ConvergesTo
      (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
        (adaptiveDenseStageApproximant D data.base.sampleIndex
          data.base.centeredStageObservable X scale))
      (D.wilson.toGNSData.cinnerRep
        (data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)
        (data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)) :=
  convergesTo_of_eventuallyClose
    (data.transferredNormClose X horthogonal)
    (continuumDenseNormSequence_converges D
      (data.base.sampleIndex X) (data.base.sampleRate X)
      (data.base.sampleIndex_cofinal X)
      (data.base.pointwiseTimeTranslation.linear.linearOperator.TCauchy X))

def toVacuumLinearGraphNormLimitApproximation :
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
  norm_converges := data.norm_converges
  transferredNorm_converges := data.transferredNorm_converges

def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  data.toVacuumLinearGraphNormLimitApproximation.toWilsonOperatorNormGapPin

end BF4WilsonDenseStageCenteredVacuumSlowComparison

end YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison

#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredSlowProjectiveCore.centeredStageObservable_congr
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredSlowProjectiveCore.centeredStageTransfer_intertwines
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredSlowProjectiveCore.toSlowProjectiveCore
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredSlowProjectiveCore.toSlowProjectiveComparison
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredSlowProjectiveCore.toWilsonOperatorNormGapPin
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumProjectiveBase.projective_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumProjectiveBase.projective_pairing_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumProjectiveBase.raw_square_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumProjectiveBase.raw_mean_diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumProjectiveBase.raw_square_diagonal_comparison
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumProjectiveBase.raw_mean_diagonal_comparison
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumProjectiveBase.vacuum_pairing_diagonal_small
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumSlowComparison.norm_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumSlowComparison.transferredNorm_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumSlowComparison.toVacuumLinearGraphNormLimitApproximation
#print axioms YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison.BF4WilsonDenseStageCenteredVacuumSlowComparison.toWilsonOperatorNormGapPin
