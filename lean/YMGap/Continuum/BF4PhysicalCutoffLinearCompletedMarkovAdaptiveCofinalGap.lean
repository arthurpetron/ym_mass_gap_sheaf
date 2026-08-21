/-
# Cofinal finite gaps suffice for the adaptive completed BF4 transfer

The adaptive graph-norm compiler previously consumed a `1/16` certificate at
every finite representation cutoff.  Completed convergence needs less: an
exact finite gap on any constructively cofinal family of cutoffs.

This file proves the completed finite operator gap at each selected anchor,
reindexes both adaptive graph-norm limits along those anchors, and recovers the
same strict contraction of the actual cutoff-removed transfer.  The remaining
finite input is therefore weakened from all-cutoff strictness to the existing
`FixedNomeCofinalCenteredSixteenth` interface.

Neither that cofinal certificate nor the Markov completion modulus is
inhabited here.

## Axiom gate

Only exact finite centering, constructive-real limit reindexing, quotient
induction, and the existing division-free form-to-operator theorem are used.
There is no classical choice, noncomputable declaration, custom axiom, or
placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
import YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovContraction
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient

/-! ## 1. The completed finite gap at one cofinal anchor -/

/-- The selected anchor's mean-zero theorem controls every term of the
centered form representative. -/
theorem cofinal_cauchyCenteredFormSeq_le_sixteenth
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCofinalCenteredSixteenth w hw half)
    (base : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS
        w hw (certificate.anchor base) half).toGNSData)
    (stage : Nat) :
    CReal.leEv
      (centralPhysicalCauchyCenteredMarkovFormSeq
        w hw (certificate.anchor base) half X stage)
      (CReal.mul (CReal.ofQ' physicalCutoffSixteenth)
        (centralPhysicalCauchyCenteredNormSeq
          w hw (certificate.anchor base) half X stage)) := by
  let K := certificate.anchor base
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw K half).toGNSData
  let mean := centralPhysicalStationaryMean w hw K half (X.seq stage)
  let normCorrection := D.B (X.seq stage) (X.seq stage) + -(mean * mean)
  let formCorrection := E.B (X.seq stage) (X.seq stage) + -(mean * mean)
  have hfinite : formCorrection <=
      physicalCutoffSixteenth * normCorrection := by
    exact centralPhysical_centeredCorrection_form_le_of_abs_gap
      w hw K half physicalCutoffSixteenth
      (certificate.meanZeroGap base) (X.seq stage)
  refine CReal.leEv_trans
    (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hfinite)) ?_
  exact CReal.leEv_of_equiv
    (CRealAlg.ofQ'_mul physicalCutoffSixteenth normCorrection)

/-- Representative-level completed form gap at one selected anchor. -/
theorem cofinal_cinnerRep_form_gap_sixteenth
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCofinalCenteredSixteenth w hw half)
    (base : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS
        w hw (certificate.anchor base) half).toGNSData)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      w hw (certificate.anchor base) half
      (Quotient.mk
        (cauchySetoid
          (centralPhysicalSmulGNS
            w hw (certificate.anchor base) half).toGNSData) X)) :
    CReal.leEv
      ((centralPhysicalSmulGNS
        w hw (certificate.anchor base) half).toGNSData.cinnerRep
          ((centralPhysicalMarkovSymbol
            w hw (certificate.anchor base) half).cDiagCauchy X) X)
      (CReal.mul (CReal.ofQ' physicalCutoffSixteenth)
        ((centralPhysicalSmulGNS
          w hw (certificate.anchor base) half).toGNSData.cinnerRep X X)) := by
  apply CReal.leEv_of_convergesTo_le
    (centralPhysicalCauchyCenteredMarkovFormSeq_converges_form
      w hw (certificate.anchor base) half X horthogonal)
    (CReal.convergesTo_constMul physicalCutoffSixteenth
      (centralPhysicalCauchyCenteredNormSeq_converges_self
        w hw (certificate.anchor base) half X horthogonal))
  exact cofinal_cauchyCenteredFormSeq_le_sixteenth
    certificate base X

/-- The anchor theorem descends to the full finite GNS completion. -/
theorem cofinal_completed_vacuum_form_gap_sixteenth
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCofinalCenteredSixteenth w hw half)
    (base : Nat)
    (vector : CentralPhysicalGNSCompletion
      w hw (certificate.anchor base) half)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      w hw (certificate.anchor base) half vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS
        w hw (certificate.anchor base) half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer
            w hw (certificate.anchor base) half vector) vector)
      (CReal.RCscale physicalCutoffSixteenth
        ((centralPhysicalSmulGNS
          w hw (certificate.anchor base) half).toGNSData.cinnerCompl
            vector vector)) := by
  revert horthogonal
  refine Quotient.inductionOn vector ?_
  intro X horthogonal
  exact cofinal_cinnerRep_form_gap_sixteenth
    certificate base X horthogonal

/-- The selected anchor bundled in the reusable finite form-gap interface. -/
def cofinalCutoffCompletedVacuumFormGap
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCofinalCenteredSixteenth w hw half)
    (base : Nat) :
    CentralPhysicalCompletedVacuumFormGap
      w hw (certificate.anchor base) half physicalCutoffSixteenth :=
  ⟨physicalCutoffSixteenth_nonnegative,
    physicalCutoffSixteenth_lt_one,
    cofinal_completed_vacuum_form_gap_sixteenth certificate base⟩

/-- The division-free form-to-operator theorem upgrades every selected
cofinal anchor to squared-norm contraction by `(1/16)^2`. -/
theorem cofinal_completed_vacuum_operator_norm_gap_sixteenth
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCofinalCenteredSixteenth w hw half)
    (base : Nat)
    (vector : CentralPhysicalGNSCompletion
      w hw (certificate.anchor base) half)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      w hw (certificate.anchor base) half vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS
        w hw (certificate.anchor base) half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer
            w hw (certificate.anchor base) half vector)
          (centralPhysicalCompletedMarkovTransfer
            w hw (certificate.anchor base) half vector))
      (CReal.RCscale
        (physicalCutoffSixteenth * physicalCutoffSixteenth)
        ((centralPhysicalSmulGNS
          w hw (certificate.anchor base) half).toGNSData.cinnerCompl
            vector vector)) :=
  centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
    hw (certificate.anchor base) half
    (cofinalCutoffCompletedVacuumFormGap certificate base)
    vector horthogonal

/-! ## 2. The canonical adaptive stage at one cofinal anchor -/

/-- Specialize the cofinal finite completed gap to the canonical centered
approximant of a cutoff-completion representative. -/
theorem centralPhysicalCofinalCenteredStage_operator_norm_gap_sixteenth
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (base : Nat) :
    CReal.leEv
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half X (certificate.anchor base))
      (CReal.mul
        (CReal.ofQ'
          (physicalCutoffSixteenth * physicalCutoffSixteenth))
        (centralPhysicalCutoffCenteredStageNorm
          hw0 hw1 half X (certificate.anchor base))) := by
  have hgap := cofinal_completed_vacuum_operator_norm_gap_sixteenth
    certificate base
    (centralPhysicalCutoffCenteredStagePoint
      hw0 hw1 half X (certificate.anchor base))
    (centralPhysicalCutoffCenteredStagePoint_vacuumOrthogonal
      hw0 hw1 half X (certificate.anchor base))
  change CReal.RCle
    (Quotient.mk CReal.crealSetoid
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half X (certificate.anchor base)))
    (CReal.RCscale
      (physicalCutoffSixteenth * physicalCutoffSixteenth)
      (Quotient.mk CReal.crealSetoid
        (centralPhysicalCutoffCenteredStageNorm
          hw0 hw1 half X (certificate.anchor base)))) at hgap
  rw [CReal.RCscale_mk, CReal.RCle_mk] at hgap
  exact hgap

/-! ## 3. Reindex the two adaptive graph limits -/

private theorem anchor_cofinal
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCofinalCenteredSixteenth w hw half)
    (threshold stage : Nat) (hstage : threshold <= stage) :
    threshold <= certificate.anchor stage :=
  Nat.le_trans hstage (certificate.anchor_ge stage)

theorem adaptiveInputCenteredNorm_cofinal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal :
      let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
      CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid Y)) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    CReal.ConvergesTo
      (fun base => centralPhysicalCutoffCenteredStageNorm
        hw0 hw1 half Y (certificate.anchor base))
      (physicalCauchyPairingLimit hw0 hw1 half Y Y) := by
  exact convergesTo_cofinalReindex
    (adaptiveInputCenteredNorm_converges
      hw0 hw1 half X horthogonal)
    certificate.anchor (fun threshold => threshold)
    (anchor_cofinal certificate)

theorem adaptiveTransferredCenteredNorm_cofinal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal :
      let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
      CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid Y)) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalLinearMarkovMapCauchy M Y
    CReal.ConvergesTo
      (fun base => centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half Y (certificate.anchor base))
      (physicalCauchyPairingLimit hw0 hw1 half TY TY) := by
  exact convergesTo_cofinalReindex
    (adaptiveTransferredCenteredNorm_converges
      hw0 hw1 half M X horthogonal)
    certificate.anchor (fun threshold => threshold)
    (anchor_cofinal certificate)

/-! ## 4. Completed contraction from cofinal finite strictness -/

theorem adaptiveCofinalRepresentative_operator_norm_gap_sixteenth
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal :
      let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
      CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid Y)) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalLinearMarkovMapCauchy M Y
    CReal.leEv
      (physicalCauchyPairingLimit hw0 hw1 half TY TY)
      (CReal.mul
        (CReal.ofQ'
          (physicalCutoffSixteenth * physicalCutoffSixteenth))
        (physicalCauchyPairingLimit hw0 hw1 half Y Y)) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  apply CReal.leEv_of_convergesTo_le
    (adaptiveTransferredCenteredNorm_cofinal_converges
      hw0 hw1 half M certificate X horthogonal)
    (CReal.convergesTo_constMul
      (physicalCutoffSixteenth * physicalCutoffSixteenth)
      (adaptiveInputCenteredNorm_cofinal_converges
        hw0 hw1 half certificate X horthogonal))
  intro base
  exact centralPhysicalCofinalCenteredStage_operator_norm_gap_sixteenth
    hw0 hw1 half certificate Y base

/-- A completion modulus plus exact strictness on merely a cofinal cutoff
family suffice for strict contraction of the actual completed transfer. -/
def centralPhysicalCutoffCompletedMarkovAdaptiveCofinalStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalCutoffCompletedMarkovStrictContractionData
      hw0 hw1 half M
        (centralPhysicalCutoffCompletedMarkovAdaptivePairingInvariant
          hw0 hw1 half M) where
  rate := physicalCutoffSixteenth
  rate_nonnegative := physicalCutoffSixteenth_nonnegative
  rate_lt_one := physicalCutoffSixteenth_lt_one
  contraction := by
    intro vector
    rcases vector with ⟨point, horthogonal⟩
    revert horthogonal
    refine Quotient.inductionOn point ?_
    intro X horthogonal
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    have hclass := centralPhysicalGraphAdaptiveReindex_class_eq
      hw0 hw1 half X
    have horthogonalY :
        CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
          (Quotient.mk
            (centralPhysicalCutoffLinearSquaredSeminorm
              hw0 hw1 half).completionSetoid Y) := by
      rw [← hclass]
      exact horthogonal
    let vectorY : CentralPhysicalCutoffCompletedVacuumComplement
        hw0 hw1 half :=
      ⟨Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid Y, horthogonalY⟩
    have hvector :
        (⟨Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid X, horthogonal⟩ :
          CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half) =
        vectorY := by
      apply Subtype.ext
      exact hclass
    rw [hvector]
    change CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half
          (centralPhysicalLinearMarkovMapCauchy M Y)
          (centralPhysicalLinearMarkovMapCauchy M Y)))
      (CReal.RCscale
        (physicalCutoffSixteenth * physicalCutoffSixteenth)
        (Quotient.mk CReal.crealSetoid
          (physicalCauchyPairingLimit hw0 hw1 half Y Y)))
    rw [CReal.RCscale_mk, CReal.RCle_mk]
    exact adaptiveCofinalRepresentative_operator_norm_gap_sixteenth
      hw0 hw1 half M certificate X horthogonalY

/-- A cofinal family of genuine local-slice gluing witnesses is an even more
geometric sufficient input for the same completed strict contraction. -/
def centralPhysicalCutoffCompletedMarkovAdaptiveCofinalLocalGluingStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (certificate : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalCutoffCompletedMarkovStrictContractionData
      hw0 hw1 half M
        (centralPhysicalCutoffCompletedMarkovAdaptivePairingInvariant
          hw0 hw1 half M) :=
  centralPhysicalCutoffCompletedMarkovAdaptiveCofinalStrictContractionData
    hw0 hw1 half M certificate.toCenteredSixteenth

/-! ## Axiom audit -/

#print axioms cofinal_completed_vacuum_operator_norm_gap_sixteenth
#print axioms centralPhysicalCofinalCenteredStage_operator_norm_gap_sixteenth
#print axioms adaptiveInputCenteredNorm_cofinal_converges
#print axioms adaptiveTransferredCenteredNorm_cofinal_converges
#print axioms adaptiveCofinalRepresentative_operator_norm_gap_sixteenth
#print axioms centralPhysicalCutoffCompletedMarkovAdaptiveCofinalStrictContractionData
#print axioms centralPhysicalCutoffCompletedMarkovAdaptiveCofinalLocalGluingStrictContractionData

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalGap
