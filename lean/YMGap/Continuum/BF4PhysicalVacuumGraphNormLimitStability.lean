/-
# Vacuum-complement-only BF4 graph-norm limit stability

The operator gap is quantified only over the selected vacuum complement.  It
therefore does not require graph-norm convergence for representatives with a
nonzero vacuum component.  This file records the logically minimal limit
interface and compiles it to the same selected Wilson operator-gap pin.

This weakening is essential for exact finite centering: centered finite
approximants represent the original continuum vector precisely on the vacuum
complement, not on arbitrary vacuum-shifted representatives.
-/

import YMGap.Continuum.BF4PhysicalModulatedGapLimitStability

namespace YMGap.Continuum.BF4PhysicalVacuumGraphNormLimitStability

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMarkovModulusCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.WilsonLinearTimeTranslationHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-- Representative graph-norm convergence restricted to the vectors on which
the final operator gap is actually asserted. -/
structure BF4WilsonVacuumRepresentativeGraphNormLimitApproximation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 3 where
  separatorPinned : D.selectedSpectralData.gap.sep = bf4MacroNormRate
  transferredRepresentative :
    SelectedWilsonCauchy D -> SelectedWilsonCauchy D
  transferredRepresentative_class : forall X,
    selectedWilsonPoint D (transferredRepresentative X) =
      D.timeTranslation.op.T (selectedWilsonPoint D X)
  approximant : forall _X : SelectedWilsonCauchy D,
    (scale : Nat) -> MatchedPhysicalStageCauchy family coupling scale
  approximant_vacuumOrthogonal : forall
    (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      forall scale : Nat,
        CentralPhysicalModulatedVacuumOrthogonal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (matchedPhysicalStagePoint family coupling scale
            (approximant X scale))
  norm_converges : forall (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      CReal.ConvergesTo
        (fun scale => matchedPhysicalStageNorm family coupling scale
          (approximant X scale))
        (D.wilson.toGNSData.cinnerRep X X)
  transferredNorm_converges : forall (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      CReal.ConvergesTo
        (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
          (approximant X scale))
        (D.wilson.toGNSData.cinnerRep
          (transferredRepresentative X) (transferredRepresentative X))

namespace BF4WilsonVacuumRepresentativeGraphNormLimitApproximation

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : BF4WilsonVacuumRepresentativeGraphNormLimitApproximation producer D)

/-- The finite uniform gap survives the two conditional graph-norm limits. -/
theorem representative_limit_operator_norm_gap_sixteenth
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.leEv
      (D.wilson.toGNSData.cinnerRep
        (data.transferredRepresentative X)
        (data.transferredRepresentative X))
      (CReal.mul (CReal.ofQ' bf4MacroSquaredNormRate)
        (D.wilson.toGNSData.cinnerRep X X)) := by
  apply CReal.leEv_of_convergesTo_le
    (data.transferredNorm_converges X horthogonal)
    (CReal.convergesTo_constMul bf4MacroSquaredNormRate
      (data.norm_converges X horthogonal))
  intro scale
  exact matchedPhysicalStage_operator_norm_gap_sixteenth
    producer scale (data.approximant X scale)
      (data.approximant_vacuumOrthogonal X horthogonal scale)

/-- Conditional representative limits suffice for the choice-free quotient
operator-gap theorem. -/
def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D where
  normGap := by
    intro vector
    refine Quotient.inductionOn vector ?_
    intro X horthogonal
    change CReal.RCle
      (D.wilson.toGNSData.gnsComplete.hilbert.cinner
        (D.timeTranslation.op.T (selectedWilsonPoint D X))
        (D.timeTranslation.op.T (selectedWilsonPoint D X)))
      (CReal.RCscale
        (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep)
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (selectedWilsonPoint D X) (selectedWilsonPoint D X)))
    rw [<- data.transferredRepresentative_class X]
    change CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (D.wilson.toGNSData.cinnerRep
          (data.transferredRepresentative X)
          (data.transferredRepresentative X)))
      (CReal.RCscale
        (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep)
        (Quotient.mk CReal.crealSetoid
          (D.wilson.toGNSData.cinnerRep X X)))
    rw [data.separatorPinned]
    change CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (D.wilson.toGNSData.cinnerRep
          (data.transferredRepresentative X)
          (data.transferredRepresentative X)))
      (CReal.RCscale bf4MacroSquaredNormRate
        (Quotient.mk CReal.crealSetoid
          (D.wilson.toGNSData.cinnerRep X X)))
    rw [CReal.RCscale_mk, CReal.RCle_mk]
    exact data.representative_limit_operator_norm_gap_sixteenth X horthogonal

end BF4WilsonVacuumRepresentativeGraphNormLimitApproximation

/-- Linear-time-translation version of the conditional graph-norm interface. -/
structure BF4WilsonVacuumLinearGraphNormLimitApproximation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 3 where
  separatorPinned : D.selectedSpectralData.gap.sep = bf4MacroNormRate
  linearTimeTranslation : WilsonLinearTimeTranslationPin D.timeTranslation
  approximant : forall _X : SelectedWilsonCauchy D,
    (scale : Nat) -> MatchedPhysicalStageCauchy family coupling scale
  approximant_vacuumOrthogonal : forall
    (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      forall scale : Nat,
        CentralPhysicalModulatedVacuumOrthogonal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (matchedPhysicalStagePoint family coupling scale
            (approximant X scale))
  norm_converges : forall (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      CReal.ConvergesTo
        (fun scale => matchedPhysicalStageNorm family coupling scale
          (approximant X scale))
        (D.wilson.toGNSData.cinnerRep X X)
  transferredNorm_converges : forall (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      CReal.ConvergesTo
        (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
          (approximant X scale))
        (D.wilson.toGNSData.cinnerRep
          (linearTimeTranslation.linearOperator.TCauchy X)
          (linearTimeTranslation.linearOperator.TCauchy X))

namespace BF4WilsonVacuumLinearGraphNormLimitApproximation

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : BF4WilsonVacuumLinearGraphNormLimitApproximation producer D)

def toRepresentativeGraphNormLimitApproximation :
    BF4WilsonVacuumRepresentativeGraphNormLimitApproximation producer D where
  separatorPinned := data.separatorPinned
  transferredRepresentative := data.linearTimeTranslation.linearOperator.TCauchy
  transferredRepresentative_class := by
    intro X
    rw [<- data.linearTimeTranslation.operatorPinned]
    exact (data.linearTimeTranslation.linearOperator.T_ofCauchy X).symm
  approximant := data.approximant
  approximant_vacuumOrthogonal := data.approximant_vacuumOrthogonal
  norm_converges := data.norm_converges
  transferredNorm_converges := data.transferredNorm_converges

def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  data.toRepresentativeGraphNormLimitApproximation.toWilsonOperatorNormGapPin

end BF4WilsonVacuumLinearGraphNormLimitApproximation

end YMGap.Continuum.BF4PhysicalVacuumGraphNormLimitStability

#print axioms YMGap.Continuum.BF4PhysicalVacuumGraphNormLimitStability.BF4WilsonVacuumRepresentativeGraphNormLimitApproximation.representative_limit_operator_norm_gap_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalVacuumGraphNormLimitStability.BF4WilsonVacuumRepresentativeGraphNormLimitApproximation.toWilsonOperatorNormGapPin
#print axioms YMGap.Continuum.BF4PhysicalVacuumGraphNormLimitStability.BF4WilsonVacuumLinearGraphNormLimitApproximation.toRepresentativeGraphNormLimitApproximation
#print axioms YMGap.Continuum.BF4PhysicalVacuumGraphNormLimitStability.BF4WilsonVacuumLinearGraphNormLimitApproximation.toWilsonOperatorNormGapPin
