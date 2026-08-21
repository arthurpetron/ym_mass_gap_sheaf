/-
# Fixed-observable raw-moment moduli for physical BF4 stages

The vector-adaptive diagonal should not assume convergence along a moving
observable sequence.  It should be constructed from ordinary pointwise
finite/projective estimates by making the slow sampler pay the rate attached
to the observable it selects.

This module packages those pointwise inputs for the raw square and raw
stationary mean, and regularizes both rates along the canonical `invSucc`
precision ladder.  No estimate is proved for the physical measure here.
-/

import YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
import YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence

namespace YMGap.Continuum.BF4PhysicalDenseStageRawMomentModulus

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-- The exact stationary mean of one raw finite-stage realization. -/
def finiteStageRawMean
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (rawStageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (scale : Nat) (observable : D.wilson.toGNSData.V) : Q' :=
  centralPhysicalStationaryMean
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (rawStageObservable scale observable)

/-- Fixed-observable moduli for the two raw moments used by exact centering.
The target evaluator is the selected rational projective OS functional on the
same stage and measure thread. -/
structure BF4RawStageMomentModulus
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (rawStageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (rationalFunctional : ProjectiveOSRationalModulus D) : Type 2 where
  squareRate : D.wilson.toGNSData.V -> Q' -> Nat
  squareBound : forall (observable : D.wilson.toGNSData.V)
    (epsilon : Q'), (0 : Q') < epsilon -> forall scale : Nat,
      squareRate observable epsilon <= scale ->
        finiteStageSquareExpectation D rawStageObservable scale observable <=
            rationalFunctional.stageExpectationQ scale (mu.pick scale)
              (continuumSquareObservable D observable) + epsilon /\
          rationalFunctional.stageExpectationQ scale (mu.pick scale)
              (continuumSquareObservable D observable) <=
            finiteStageSquareExpectation D rawStageObservable scale observable +
              epsilon
  meanRate : D.wilson.toGNSData.V -> Q' -> Nat
  meanBound : forall (observable : D.wilson.toGNSData.V)
    (epsilon : Q'), (0 : Q') < epsilon -> forall scale : Nat,
      meanRate observable epsilon <= scale ->
        finiteStageRawMean D rawStageObservable scale observable <=
            rationalFunctional.stageExpectationQ scale (mu.pick scale)
              (continuumVacuumPairingObservable D observable) + epsilon /\
          rationalFunctional.stageExpectationQ scale (mu.pick scale)
              (continuumVacuumPairingObservable D observable) <=
            finiteStageRawMean D rawStageObservable scale observable + epsilon

namespace BF4RawStageMomentModulus

variable
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {rawStageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V}
    {rationalFunctional : ProjectiveOSRationalModulus D}
    (data : BF4RawStageMomentModulus D rawStageObservable rationalFunctional)

/-- Antitone regularization of the pointwise raw-square rate. -/
def regularSquareRate (observable : D.wilson.toGNSData.V)
    (epsilon : Q') : Nat :=
  CReal.Gmax
    (fun precision => data.squareRate observable (Q'.invSucc precision))
    (CReal.lv epsilon)

/-- Antitone regularization of the pointwise raw-mean rate. -/
def regularMeanRate (observable : D.wilson.toGNSData.V)
    (epsilon : Q') : Nat :=
  CReal.Gmax
    (fun precision => data.meanRate observable (Q'.invSucc precision))
    (CReal.lv epsilon)

theorem regularSquareRate_antitone
    (observable : D.wilson.toGNSData.V)
    {epsilon delta : Q'} (hdelta : (0 : Q') < delta)
    (hdeltaepsilon : delta <= epsilon) :
    data.regularSquareRate observable epsilon <=
      data.regularSquareRate observable delta := by
  exact CReal.Gmax_mono _ _ _
    (CReal.lv_antitone hdelta hdeltaepsilon)

theorem regularMeanRate_antitone
    (observable : D.wilson.toGNSData.V)
    {epsilon delta : Q'} (hdelta : (0 : Q') < delta)
    (hdeltaepsilon : delta <= epsilon) :
    data.regularMeanRate observable epsilon <=
      data.regularMeanRate observable delta := by
  exact CReal.Gmax_mono _ _ _
    (CReal.lv_antitone hdelta hdeltaepsilon)

/-- The regularized raw-square rate retains the original pointwise estimate. -/
theorem regularSquareBound
    (observable : D.wilson.toGNSData.V)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : data.regularSquareRate observable epsilon <= scale) :
    finiteStageSquareExpectation D rawStageObservable scale observable <=
        rationalFunctional.stageExpectationQ scale (mu.pick scale)
          (continuumSquareObservable D observable) + epsilon /\
      rationalFunctional.stageExpectationQ scale (mu.pick scale)
          (continuumSquareObservable D observable) <=
        finiteStageSquareExpectation D rawStageObservable scale observable +
          epsilon := by
  let delta : Q' := Q'.invSucc (CReal.lv epsilon)
  have hdelta : (0 : Q') < delta := Q'.invSucc_pos _
  have hrawRate : data.squareRate observable delta <=
      data.regularSquareRate observable epsilon :=
    CReal.Gmax_ge
      (fun precision => data.squareRate observable (Q'.invSucc precision))
      (CReal.lv epsilon)
  have hbound := data.squareBound observable delta hdelta scale
    (Nat.le_trans hrawRate hscale)
  have hdeltaepsilon : delta <= epsilon :=
    CReal.invSucc_lv_le hepsilon
  exact
    ⟨Q'.le_trans' _ _ _ hbound.1
        (Q'.add_le_add_left _ _ _ hdeltaepsilon),
      Q'.le_trans' _ _ _ hbound.2
        (Q'.add_le_add_left _ _ _ hdeltaepsilon)⟩

/-- The regularized raw-mean rate retains the original pointwise estimate. -/
theorem regularMeanBound
    (observable : D.wilson.toGNSData.V)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : data.regularMeanRate observable epsilon <= scale) :
    finiteStageRawMean D rawStageObservable scale observable <=
        rationalFunctional.stageExpectationQ scale (mu.pick scale)
          (continuumVacuumPairingObservable D observable) + epsilon /\
      rationalFunctional.stageExpectationQ scale (mu.pick scale)
          (continuumVacuumPairingObservable D observable) <=
        finiteStageRawMean D rawStageObservable scale observable + epsilon := by
  let delta : Q' := Q'.invSucc (CReal.lv epsilon)
  have hdelta : (0 : Q') < delta := Q'.invSucc_pos _
  have hrawRate : data.meanRate observable delta <=
      data.regularMeanRate observable epsilon :=
    CReal.Gmax_ge
      (fun precision => data.meanRate observable (Q'.invSucc precision))
      (CReal.lv epsilon)
  have hbound := data.meanBound observable delta hdelta scale
    (Nat.le_trans hrawRate hscale)
  have hdeltaepsilon : delta <= epsilon :=
    CReal.invSucc_lv_le hepsilon
  exact
    ⟨Q'.le_trans' _ _ _ hbound.1
        (Q'.add_le_add_left _ _ _ hdeltaepsilon),
      Q'.le_trans' _ _ _ hbound.2
        (Q'.add_le_add_left _ _ _ hdeltaepsilon)⟩

end BF4RawStageMomentModulus

end YMGap.Continuum.BF4PhysicalDenseStageRawMomentModulus

#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMomentModulus.BF4RawStageMomentModulus.regularSquareRate_antitone
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMomentModulus.BF4RawStageMomentModulus.regularMeanRate_antitone
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMomentModulus.BF4RawStageMomentModulus.regularSquareBound
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMomentModulus.BF4RawStageMomentModulus.regularMeanBound
