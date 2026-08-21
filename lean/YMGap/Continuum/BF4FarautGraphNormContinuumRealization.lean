/-
# AF/Faraut continuum realization through graph-norm limits

The existing minimal bounded continuum residual asks directly for a
`WilsonOperatorNormGapPin`.  The physical BF4 limit-stability compiler can now
derive that pin from explicit varying-cutoff graph-norm approximation data.

This module replaces the direct operator-gap field by the causal inputs that
produce it: a selected continuum Yang--Mills/Wilson object, exact-rate
reconstruction on that same object, and a graph-norm limit of the concrete
modulated physical BF4 carriers.  It then constructs the old minimal residual
and hence the positive exact-log bounded mass-gap endpoint.

The continuum existence, exact-rate reconstruction, graph-norm approximation,
and the underlying AF/Faraut producer remain explicit uninhabited inputs.  No
continuum Yang--Mills theory is constructed here.
-/

import YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization
import YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison
import YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
import YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison
import YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
import YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison
import YMGap.Continuum.BF4PhysicalDenseStageRationalComparison
import YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
import YMGap.Continuum.BF4PhysicalModulatedGapLimitStability

namespace YMGap.Continuum.BF4FarautGraphNormContinuumRealization

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AsymptoticSpectralLoc
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare
open YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
open YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer
open YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization
open YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalDenseStageExpectationComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalDenseStageProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageRationalComparison
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ExactRateReconstructionHandoff
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.GradedBondMovingBudget
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. Replace the assumed continuum norm gap by its limit construction -/

/-- The minimal bounded AF/Faraut continuum residual with the direct
operator-gap field replaced by explicit graph-norm approximation data. -/
structure ContinuumWilsonGraphNormResidualData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus}
    {N0 : Nat}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure.ContinuumMeasure M) : Type 3 where
  /-- Genuine continuum Yang--Mills existence on the selected measure. -/
  existence : ContinuumYMExistence mu
  /-- The selected Wilson completion and actual time translation, before any
  gap inequality is imposed. -/
  osGNS : WilsonSelectedOSGNSData existence
  /-- The finite physical rate sequence converges to the logarithmic gap of
  this same selected reconstruction. -/
  rateReconstruction : ExactRateReconstructionHandoff
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare)
    osGNS.reconstruction
  /-- The explicit varying-carrier graph-norm limit from which the continuum
  operator gap will be derived. -/
  graphNormLimit : BF4WilsonLinearGraphNormLimitApproximation
    producer.toBF4QuarterPhysicalSeparatorProducer osGNS

namespace ContinuumWilsonGraphNormResidualData

/-- Compile graph-norm limit stability into the former direct-gap residual. -/
def toContinuumWilsonMinimalBoundedResidualData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus}
    {N0 : Nat}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    (D : ContinuumWilsonGraphNormResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ContinuumWilsonMinimalBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  existence := D.existence
  osGNS := D.osGNS
  rateReconstruction := D.rateReconstruction
  operatorNormGap := D.graphNormLimit.toWilsonOperatorNormGapPin

/-- The graph-norm residual therefore constructs the existing same-object
minimal bounded mass-gap endpoint: a positive exact logarithmic rate together
with the derived bounded transfer gap. -/
def continuumWilsonMinimalBoundedMassGap
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus}
    {N0 : Nat}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    (D : ContinuumWilsonGraphNormResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    WilsonMinimalBoundedMassGap D.osGNS :=
  D.toContinuumWilsonMinimalBoundedResidualData
    |>.continuumWilsonMinimalBoundedMassGap

/-! ## 2. Adapter from the projective OS residual -/

/-- A projective same-object continuum realization plus graph-norm convergence
constructs the graph-norm residual without an independently assumed norm gap. -/
def ofProjectiveOSResidualData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus}
    {N0 : Nat}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    (D : ContinuumProjectiveOSResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (graphNormLimit : BF4WilsonLinearGraphNormLimitApproximation
      producer.toBF4QuarterPhysicalSeparatorProducer
      (WilsonSelectedOSGNSData.ofLinked D.osGNS)) :
    ContinuumWilsonGraphNormResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  existence := D.existence
  osGNS := WilsonSelectedOSGNSData.ofLinked D.osGNS
  rateReconstruction := D.rateReconstruction
  graphNormLimit := graphNormLimit

end ContinuumWilsonGraphNormResidualData

/-! ## 3. Measure-level dense-stage causal endpoint -/

/-- The AF/Faraut continuum residual factored all the way down to literal
dense finite-stage observables and an eventual rational same-observable form
comparison, stated as convergence of the corresponding finite and continuum
reflected-square expectations and factored through a modulus-carrying
refinement of the selected projective OS functional.

Unlike `ContinuumWilsonGraphNormResidualData`, this record does not assume the
two graph-norm convergence laws or a `CReal`-level norm-limit pin.  Its
dense-stage field constructs both laws from pointwise transfer compatibility,
an executable vector-adaptive slow diagonal, and rational
finite-to-continuum quadratic-form bounds. -/
structure ContinuumWilsonDenseStageResidualData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus}
    {N0 : Nat}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure.ContinuumMeasure M) : Type 3 where
  existence : ContinuumYMExistence mu
  osGNS : WilsonSelectedOSGNSData existence
  rateReconstruction : ExactRateReconstructionHandoff
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare)
    osGNS.reconstruction
  denseStageLimit : BF4WilsonDenseStageSlowProjectiveComparison
    producer.toBF4QuarterPhysicalSeparatorProducer osGNS

namespace ContinuumWilsonDenseStageResidualData

/-- Compile the dense-stage causal inputs into the previous graph-norm
residual. -/
def toContinuumWilsonGraphNormResidualData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus}
    {N0 : Nat}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    (D : ContinuumWilsonDenseStageResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ContinuumWilsonGraphNormResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  existence := D.existence
  osGNS := D.osGNS
  rateReconstruction := D.rateReconstruction
  graphNormLimit := D.denseStageLimit.toAdaptiveProjectiveComparison
    |>.toLinearGraphNormLimitApproximation

/-- Literal dense finite-stage maps and projective expectation moduli construct
their vector-adaptive slow diagonal and then the same-object positive exact-log
bounded mass-gap endpoint. -/
def continuumWilsonMinimalBoundedMassGap
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus}
    {N0 : Nat}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    (D : ContinuumWilsonDenseStageResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    WilsonMinimalBoundedMassGap D.osGNS :=
  D.toContinuumWilsonGraphNormResidualData
    |>.continuumWilsonMinimalBoundedMassGap

/-- A projective same-object continuum realization plus literal dense-stage
data constructs the fully factored endpoint. -/
def ofProjectiveOSResidualData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus}
    {N0 : Nat}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    (D : ContinuumProjectiveOSResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (denseStageLimit : BF4WilsonDenseStageSlowProjectiveComparison
      producer.toBF4QuarterPhysicalSeparatorProducer
      (WilsonSelectedOSGNSData.ofLinked D.osGNS)) :
    ContinuumWilsonDenseStageResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  existence := D.existence
  osGNS := WilsonSelectedOSGNSData.ofLinked D.osGNS
  rateReconstruction := D.rateReconstruction
  denseStageLimit := denseStageLimit

end ContinuumWilsonDenseStageResidualData

end YMGap.Continuum.BF4FarautGraphNormContinuumRealization

#print axioms YMGap.Continuum.BF4FarautGraphNormContinuumRealization.ContinuumWilsonGraphNormResidualData.toContinuumWilsonMinimalBoundedResidualData
#print axioms YMGap.Continuum.BF4FarautGraphNormContinuumRealization.ContinuumWilsonGraphNormResidualData.continuumWilsonMinimalBoundedMassGap
#print axioms YMGap.Continuum.BF4FarautGraphNormContinuumRealization.ContinuumWilsonGraphNormResidualData.ofProjectiveOSResidualData
#print axioms YMGap.Continuum.BF4FarautGraphNormContinuumRealization.ContinuumWilsonDenseStageResidualData.toContinuumWilsonGraphNormResidualData
#print axioms YMGap.Continuum.BF4FarautGraphNormContinuumRealization.ContinuumWilsonDenseStageResidualData.continuumWilsonMinimalBoundedMassGap
#print axioms YMGap.Continuum.BF4FarautGraphNormContinuumRealization.ContinuumWilsonDenseStageResidualData.ofProjectiveOSResidualData
