/-
# Constructive slow diagonals for dense physical BF4 stages

The vector-adaptive projective compiler still accepts a cofinal sampler and a
proof that its sampled observables clear the projective expectation modulus.
This file constructs both pieces.

First, an arbitrary rational modulus is regularized along the canonical
`invSucc` precision ladder.  Its new rate is antitone in the tolerance and
retains the original two-sided estimate.  Second, for each completed Wilson
representative, a strictly increasing threshold ladder records the ordinary
and translated square-observable requirements of its `n`-th dense term.  A
bounded greatest-admissible search selects the largest term whose accumulated
requirement fits inside the current finite stage.

The resulting sampler is constructive, cofinal, and automatically admissible
for every positive rational tolerance.  The finite realization, evaluator
pin, vacuum-complement preservation, and continuum projective modulus remain
analytic inputs.  No continuum theory or Clay target is constructed here.
-/

import YMGap.Constructive.SelfSimilarFlow
import YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison

namespace YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovModulusCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.WilsonLinearTimeTranslationHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. A generic executable slow diagonal -/

/-- The cumulative stage threshold for the first `n` requirements.  Successor
thresholds advance strictly, even when the raw requirement is constant. -/
def slowThreshold (required : Nat -> Nat) : Nat -> Nat
  | 0 => required 0
  | n + 1 => max (slowThreshold required n + 1) (required (n + 1))

/-- Every raw requirement is dominated by its cumulative threshold. -/
theorem required_le_slowThreshold (required : Nat -> Nat) :
    forall n : Nat, required n <= slowThreshold required n
  | 0 => Nat.le_refl _
  | _ + 1 => Nat.le_max_right _ _

/-- The cumulative threshold advances strictly at every successor. -/
theorem slowThreshold_lt_succ (required : Nat -> Nat) (n : Nat) :
    slowThreshold required n < slowThreshold required (n + 1) := by
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    (Nat.le_max_left _ _)

/-- The `n`-th cumulative threshold is at least `n`. -/
theorem self_le_slowThreshold (required : Nat -> Nat) :
    forall n : Nat, n <= slowThreshold required n
  | 0 => Nat.zero_le _
  | n + 1 => Nat.succ_le_of_lt
      (Nat.lt_of_le_of_lt (self_le_slowThreshold required n)
        (slowThreshold_lt_succ required n))

/-- The cumulative threshold is monotone. -/
theorem slowThreshold_mono (required : Nat -> Nat) :
    forall {a b : Nat}, a <= b ->
      slowThreshold required a <= slowThreshold required b := by
  intro a b hab
  induction b with
  | zero =>
      have ha : a = 0 := Nat.le_zero.mp hab
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt))
          (Nat.le_of_lt (slowThreshold_lt_succ required b))
      · have ha : a = b + 1 := Nat.le_antisymm hab hge
        subst a
        exact Nat.le_refl _

/-- Bounded search for the greatest index at most `fuel` whose cumulative
threshold is no larger than `stage`.  It falls back to zero when no positive
index is admissible. -/
def greatestAdmissibleAux (required : Nat -> Nat) (stage : Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 =>
      if slowThreshold required (n + 1) <= stage then
        n + 1
      else
        greatestAdmissibleAux required stage n

/-- The bounded search never returns an index beyond its fuel. -/
theorem greatestAdmissibleAux_le (required : Nat -> Nat) (stage : Nat) :
    forall fuel : Nat,
      greatestAdmissibleAux required stage fuel <= fuel
  | 0 => Nat.le_refl _
  | n + 1 => by
      simp only [greatestAdmissibleAux]
      split
      · exact Nat.le_refl _
      · exact Nat.le_trans (greatestAdmissibleAux_le required stage n)
          (Nat.le_succ n)

/-- If index zero is admissible, the bounded search always lands on an
admissible index. -/
theorem slowThreshold_greatestAdmissibleAux_le
    (required : Nat -> Nat) (stage : Nat)
    (hzero : slowThreshold required 0 <= stage) :
    forall fuel : Nat,
      slowThreshold required
        (greatestAdmissibleAux required stage fuel) <= stage
  | 0 => hzero
  | n + 1 => by
      simp only [greatestAdmissibleAux]
      split
      · assumption
      · exact slowThreshold_greatestAdmissibleAux_le required stage hzero n

/-- Every admissible index within the fuel lies below the bounded greatest
admissible index. -/
theorem le_greatestAdmissibleAux_of_slowThreshold_le
    (required : Nat -> Nat) (stage : Nat) :
    forall (fuel index : Nat), index <= fuel ->
      slowThreshold required index <= stage ->
      index <= greatestAdmissibleAux required stage fuel
  | 0, index, hindex, _ => by
      have hzero : index = 0 := Nat.le_zero.mp hindex
      subst index
      exact Nat.le_refl _
  | fuel + 1, index, hindex, hadmissible => by
      simp only [greatestAdmissibleAux]
      split
      case isTrue => exact hindex
      case isFalse hlast =>
        have hne : index ≠ fuel + 1 := by
          intro heq
          subst index
          exact hlast hadmissible
        have hprev : index <= fuel := by omega
        exact le_greatestAdmissibleAux_of_slowThreshold_le
          required stage fuel index hprev hadmissible

/-- The executable slow sampler at a finite stage. -/
def slowIndex (required : Nat -> Nat) (stage : Nat) : Nat :=
  greatestAdmissibleAux required stage stage

/-- Once stage zero is admissible, the selected raw requirement is paid by
the current stage. -/
theorem required_slowIndex_le
    (required : Nat -> Nat) (stage : Nat)
    (hzero : slowThreshold required 0 <= stage) :
    required (slowIndex required stage) <= stage := by
  exact Nat.le_trans
    (required_le_slowThreshold required (slowIndex required stage))
    (slowThreshold_greatestAdmissibleAux_le required stage hzero stage)

/-- The slow sampler is cofinal with the cumulative threshold as an explicit
Type-level rate. -/
theorem slowIndex_cofinal
    (required : Nat -> Nat) (threshold stage : Nat)
    (hstage : slowThreshold required threshold <= stage) :
    threshold <= slowIndex required stage := by
  have hthreshold : threshold <= stage :=
    Nat.le_trans (self_le_slowThreshold required threshold) hstage
  exact le_greatestAdmissibleAux_of_slowThreshold_le
    required stage stage threshold hthreshold hstage

/-! ## 2. Antitone regularization of a projective modulus -/

variable
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}

/-- Running-maximum regularization of a projective rate along the canonical
positive rational precision ladder. -/
def regularProjectiveRate (data : ProjectiveOSRationalModulus D)
    (observable : H.os_axioms.A.carrier) (epsilon : Q') : Nat :=
  CReal.Gmax
    (fun precision => data.rate observable (Q'.invSucc precision))
    (CReal.lv epsilon)

/-- The regularized rate is antitone in its positive tolerance. -/
theorem regularProjectiveRate_antitone
    (data : ProjectiveOSRationalModulus D)
    (observable : H.os_axioms.A.carrier)
    {epsilon delta : Q'} (hdelta : (0 : Q') < delta)
    (hdeltaepsilon : delta <= epsilon) :
    regularProjectiveRate data observable epsilon <=
      regularProjectiveRate data observable delta := by
  exact CReal.Gmax_mono _ _ _
    (CReal.lv_antitone hdelta hdeltaepsilon)

/-- Every projective rational modulus has a definitionally identical
evaluator with an antitone tolerance rate. -/
def regularizedProjectiveModulus (data : ProjectiveOSRationalModulus D) :
    ProjectiveOSRationalModulus D where
  stageExpectationQ := data.stageExpectationQ
  stageFunctionalPinned := data.stageFunctionalPinned
  rate := regularProjectiveRate data
  bound := by
    intro observable epsilon hepsilon stage hstage
    let delta : Q' := Q'.invSucc (CReal.lv epsilon)
    have hdelta : (0 : Q') < delta := Q'.invSucc_pos _
    have hrawRate : data.rate observable delta <=
        regularProjectiveRate data observable epsilon :=
      CReal.Gmax_ge
        (fun precision => data.rate observable (Q'.invSucc precision))
        (CReal.lv epsilon)
    have hbound := data.bound observable delta hdelta stage
      (Nat.le_trans hrawRate hstage)
    have hdeltaepsilon : delta <= epsilon :=
      CReal.invSucc_lv_le hepsilon
    constructor
    · exact Q'.le_trans' _ _ _ hbound.1
        (Q'.add_le_add_left _ _ _ hdeltaepsilon)
    · exact Q'.le_trans' _ _ _ hbound.2
        (Q'.add_le_add_left _ _ _ hdeltaepsilon)

/-- The rate field of the regularized modulus is antitone. -/
theorem regularizedProjectiveModulus_rate_antitone
    (data : ProjectiveOSRationalModulus D)
    (observable : H.os_axioms.A.carrier)
    {epsilon delta : Q'} (hdelta : (0 : Q') < delta)
    (hdeltaepsilon : delta <= epsilon) :
    (regularizedProjectiveModulus data).rate observable epsilon <=
      (regularizedProjectiveModulus data).rate observable delta := by
  exact regularProjectiveRate_antitone data observable
    hdelta hdeltaepsilon

/-! ## 3. The projective requirements of one completed representative -/

/-- Pointwise finite/continuum data from which the sampler and its
admissibility proof will be constructed. -/
structure BF4WilsonDenseStageSlowProjectiveCore
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
  stageObservable : forall scale : Nat,
    D.wilson.toGNSData.V ->
      (MatchedPhysicalStageGNSData family coupling scale).V
  stageObservable_congr : forall scale : Nat,
    forall {a b : D.wilson.toGNSData.V}, D.wilson.toGNSData.veq a b ->
      (MatchedPhysicalStageGNSData family coupling scale).veq
        (stageObservable scale a) (stageObservable scale b)
  stageTransfer_intertwines : forall (scale : Nat)
    (a : D.wilson.toGNSData.V),
      (MatchedPhysicalStageGNSData family coupling scale).veq
        (centralPhysicalMarkovApply
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (stageObservable scale a))
        (stageObservable scale (D.timeTranslation.tau a))
  rationalFunctional : ProjectiveOSRationalModulus D
  finiteSquarePinned : forall (scale : Nat)
    (observable : D.wilson.toGNSData.V),
      (finiteStageSquareExpectation D stageObservable scale observable).eqv
        (rationalFunctional.stageExpectationQ scale (mu.pick scale)
          (continuumSquareObservable D observable))

namespace BF4WilsonDenseStageSlowProjectiveCore

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
    (core : BF4WilsonDenseStageSlowProjectiveCore producer D)

/-- The antitone projective modulus used by the slow sampler. -/
def regularizedFunctional : ProjectiveOSRationalModulus D :=
  regularizedProjectiveModulus core.rationalFunctional

/-- The ordinary and translated projective requirements of the `index`-th
dense term at canonical precision `invSucc index`. -/
def requirement (X : SelectedWilsonCauchy D) (index : Nat) : Nat :=
  max
    (core.regularizedFunctional.rate
      (continuumSquareObservable D (X.seq index))
      (Q'.invSucc index))
    (core.regularizedFunctional.rate
      (continuumSquareObservable D
        (D.timeTranslation.tau (X.seq index)))
      (Q'.invSucc index))

/-- The cumulative threshold ladder of one completed representative. -/
def sampleRate (X : SelectedWilsonCauchy D) (threshold : Nat) : Nat :=
  slowThreshold (core.requirement X) threshold

/-- The greatest dense term whose accumulated projective requirements fit in
the current finite stage. -/
def sampleIndex (X : SelectedWilsonCauchy D) (scale : Nat) : Nat :=
  slowIndex (core.requirement X) scale

/-- The outer diagonal rate for an arbitrary rational tolerance. -/
def diagonalRate (X : SelectedWilsonCauchy D) (epsilon : Q') : Nat :=
  core.sampleRate X (CReal.lv epsilon)

/-- The constructed sampler is cofinal. -/
theorem sampleIndex_cofinal (X : SelectedWilsonCauchy D)
    (threshold scale : Nat)
    (hscale : core.sampleRate X threshold <= scale) :
    threshold <= core.sampleIndex X scale :=
  slowIndex_cofinal (core.requirement X) threshold scale hscale

/-- At every sufficiently late stage, the selected dense term pays both
regularized projective rates at the requested tolerance. -/
theorem diagonal_admissible (X : SelectedWilsonCauchy D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : core.diagonalRate X epsilon <= scale) :
    let a := X.seq (core.sampleIndex X scale)
    core.regularizedFunctional.rate
        (continuumSquareObservable D a) epsilon <= scale /\
      core.regularizedFunctional.rate
        (continuumSquareObservable D (D.timeTranslation.tau a)) epsilon <=
          scale := by
  let precision := CReal.lv epsilon
  let index := core.sampleIndex X scale
  have hprecision : precision <= index :=
    core.sampleIndex_cofinal X precision scale hscale
  have hzeroRate : core.sampleRate X 0 <= core.sampleRate X precision :=
    slowThreshold_mono (core.requirement X) (Nat.zero_le precision)
  have hzero : core.sampleRate X 0 <= scale :=
    Nat.le_trans hzeroRate hscale
  have hrequired : core.requirement X index <= scale :=
    required_slowIndex_le (core.requirement X) scale hzero
  have hindexepsilon : Q'.invSucc index <= epsilon :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hprecision)
      (CReal.invSucc_lv_le hepsilon)
  have hordinary : core.regularizedFunctional.rate
      (continuumSquareObservable D (X.seq index)) epsilon <=
      core.regularizedFunctional.rate
        (continuumSquareObservable D (X.seq index))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone core.rationalFunctional
      (continuumSquareObservable D (X.seq index))
      (Q'.invSucc_pos index) hindexepsilon
  have htranslated : core.regularizedFunctional.rate
      (continuumSquareObservable D
        (D.timeTranslation.tau (X.seq index))) epsilon <=
      core.regularizedFunctional.rate
        (continuumSquareObservable D
          (D.timeTranslation.tau (X.seq index)))
        (Q'.invSucc index) :=
    regularizedProjectiveModulus_rate_antitone core.rationalFunctional
      (continuumSquareObservable D
        (D.timeTranslation.tau (X.seq index)))
      (Q'.invSucc_pos index) hindexepsilon
  dsimp only
  constructor
  · exact Nat.le_trans hordinary
      (Nat.le_trans (Nat.le_max_left _ _) hrequired)
  · exact Nat.le_trans htranslated
      (Nat.le_trans (Nat.le_max_right _ _) hrequired)

end BF4WilsonDenseStageSlowProjectiveCore

/-! ## 4. Compilation to the adaptive graph-norm comparison -/

/-- Slow-projective data plus vacuum-complement preservation along the
constructed sampler.  No sampler, cofinality proof, or diagonal-admissibility
proof remains as an input. -/
structure BF4WilsonDenseStageSlowProjectiveComparison
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
  core : BF4WilsonDenseStageSlowProjectiveCore producer D
  stage_vacuumOrthogonal : forall (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      forall scale : Nat,
        CentralPhysicalModulatedVacuumOrthogonal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (matchedPhysicalStagePoint family coupling scale
            (adaptiveDenseStageApproximant D core.sampleIndex
              core.stageObservable X scale))

namespace BF4WilsonDenseStageSlowProjectiveComparison

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
    (data : BF4WilsonDenseStageSlowProjectiveComparison producer D)

/-- Construct the complete vector-adaptive comparison from pointwise data and
the executable slow diagonal. -/
def toAdaptiveProjectiveComparison :
    BF4WilsonDenseStageAdaptiveProjectiveComparison producer D where
  separatorPinned := data.core.separatorPinned
  pointwiseTimeTranslation := data.core.pointwiseTimeTranslation
  sampleIndex := data.core.sampleIndex
  sampleRate := data.core.sampleRate
  sampleIndex_cofinal := data.core.sampleIndex_cofinal
  stageObservable := data.core.stageObservable
  stageObservable_congr := data.core.stageObservable_congr
  stageTransfer_intertwines := data.core.stageTransfer_intertwines
  stage_vacuumOrthogonal := data.stage_vacuumOrthogonal
  rationalFunctional := data.core.regularizedFunctional
  finiteSquarePinned := data.core.finiteSquarePinned
  diagonalRate := data.core.diagonalRate
  diagonal_admissible := data.core.diagonal_admissible

/-- Pointwise projective data with the constructed slow diagonal supplies the
selected continuum Wilson operator gap. -/
def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  data.toAdaptiveProjectiveComparison.toWilsonOperatorNormGapPin

end BF4WilsonDenseStageSlowProjectiveComparison

end YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison

#print axioms YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison.required_slowIndex_le
#print axioms YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison.slowIndex_cofinal
#print axioms YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison.regularProjectiveRate_antitone
#print axioms YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison.regularizedProjectiveModulus
#print axioms YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison.regularizedProjectiveModulus_rate_antitone
#print axioms YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison.BF4WilsonDenseStageSlowProjectiveCore.diagonal_admissible
#print axioms YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison.BF4WilsonDenseStageSlowProjectiveComparison.toAdaptiveProjectiveComparison
#print axioms YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison.BF4WilsonDenseStageSlowProjectiveComparison.toWilsonOperatorNormGapPin
