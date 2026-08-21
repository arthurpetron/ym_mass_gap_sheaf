/-
# Arbitrary-rate cofinal gaps for the adaptive completed BF4 transfer

The finite cofinal certificate now carries a supplied rational rate `q` with
constructive proofs `0 <= q < 1`.  This module propagates that exact rate
through finite GNS completion, the division-free form-to-operator theorem,
cofinal reindexing of both adaptive graph-norm streams, and quotient descent.

The result is strict contraction of the actual cutoff-removed completed
transfer at squared-norm rate `q*q`.  No cofinal finite certificate or Markov
completion modulus is constructed here, and no thermodynamic, continuum, QFT,
or Clay conclusion is claimed.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalGap
import YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalStrictGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalGap
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

/-! ## 1. The supplied finite rate at one cofinal anchor -/

/-- The selected anchor's supplied mean-zero theorem controls every term of
the centered form representative. -/
theorem cofinal_cauchyCenteredFormSeq_le_rate
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap w hw half q)
    (base : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS
        w hw (certificate.anchor base) half).toGNSData)
    (stage : Nat) :
    CReal.leEv
      (centralPhysicalCauchyCenteredMarkovFormSeq
        w hw (certificate.anchor base) half X stage)
      (CReal.mul (CReal.ofQ' q)
        (centralPhysicalCauchyCenteredNormSeq
          w hw (certificate.anchor base) half X stage)) := by
  let K := certificate.anchor base
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw K half).toGNSData
  let mean := centralPhysicalStationaryMean w hw K half (X.seq stage)
  let normCorrection := D.B (X.seq stage) (X.seq stage) + -(mean * mean)
  let formCorrection := E.B (X.seq stage) (X.seq stage) + -(mean * mean)
  have hfinite : formCorrection <= q * normCorrection := by
    exact centralPhysical_centeredCorrection_form_le_of_abs_gap
      w hw K half q (certificate.meanZeroGap base) (X.seq stage)
  refine CReal.leEv_trans
    (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hfinite)) ?_
  exact CReal.leEv_of_equiv (CRealAlg.ofQ'_mul q normCorrection)

/-- Representative-level completed form gap at the supplied rate. -/
theorem cofinal_cinnerRep_form_gap_rate
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap w hw half q)
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
      (CReal.mul (CReal.ofQ' q)
        ((centralPhysicalSmulGNS
          w hw (certificate.anchor base) half).toGNSData.cinnerRep X X)) := by
  apply CReal.leEv_of_convergesTo_le
    (centralPhysicalCauchyCenteredMarkovFormSeq_converges_form
      w hw (certificate.anchor base) half X horthogonal)
    (CReal.convergesTo_constMul q
      (centralPhysicalCauchyCenteredNormSeq_converges_self
        w hw (certificate.anchor base) half X horthogonal))
  exact cofinal_cauchyCenteredFormSeq_le_rate certificate base X

/-- The arbitrary-rate anchor theorem descends to the finite GNS completion. -/
theorem cofinal_completed_vacuum_form_gap_rate
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap w hw half q)
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
      (CReal.RCscale q
        ((centralPhysicalSmulGNS
          w hw (certificate.anchor base) half).toGNSData.cinnerCompl
            vector vector)) := by
  revert horthogonal
  refine Quotient.inductionOn vector ?_
  intro X horthogonal
  exact cofinal_cinnerRep_form_gap_rate certificate base X horthogonal

/-- The selected anchor bundled in the reusable finite form-gap interface at
the supplied strict rate. -/
def cofinalCutoffCompletedVacuumFormGapAtRate
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap w hw half q)
    (base : Nat) :
    CentralPhysicalCompletedVacuumFormGap
      w hw (certificate.anchor base) half q :=
  ⟨certificate.rate_nonnegative, certificate.rate_lt_one,
    cofinal_completed_vacuum_form_gap_rate certificate base⟩

/-- The division-free form-to-operator theorem upgrades every selected anchor
to squared-norm contraction by `q*q`. -/
theorem cofinal_completed_vacuum_operator_norm_gap_rate
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap w hw half q)
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
      (CReal.RCscale (q * q)
        ((centralPhysicalSmulGNS
          w hw (certificate.anchor base) half).toGNSData.cinnerCompl
            vector vector)) :=
  centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
    hw (certificate.anchor base) half
    (cofinalCutoffCompletedVacuumFormGapAtRate certificate base)
    vector horthogonal

/-! ## 2. The canonical adaptive stage at one supplied-rate anchor -/

theorem centralPhysicalCofinalCenteredStage_operator_norm_gap_rate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (base : Nat) :
    CReal.leEv
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half X (certificate.anchor base))
      (CReal.mul (CReal.ofQ' (q * q))
        (centralPhysicalCutoffCenteredStageNorm
          hw0 hw1 half X (certificate.anchor base))) := by
  have hgap := cofinal_completed_vacuum_operator_norm_gap_rate
    certificate base
    (centralPhysicalCutoffCenteredStagePoint
      hw0 hw1 half X (certificate.anchor base))
    (centralPhysicalCutoffCenteredStagePoint_vacuumOrthogonal
      hw0 hw1 half X (certificate.anchor base))
  change CReal.RCle
    (Quotient.mk CReal.crealSetoid
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half X (certificate.anchor base)))
    (CReal.RCscale (q * q)
      (Quotient.mk CReal.crealSetoid
        (centralPhysicalCutoffCenteredStageNorm
          hw0 hw1 half X (certificate.anchor base)))) at hgap
  rw [CReal.RCscale_mk, CReal.RCle_mk] at hgap
  exact hgap

/-! ## 3. Cofinal reindexing of the two adaptive graph limits -/

private theorem anchor_cofinal_rate
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap w hw half q)
    (threshold stage : Nat) (hstage : threshold <= stage) :
    threshold <= certificate.anchor stage :=
  Nat.le_trans hstage (certificate.anchor_ge stage)

theorem adaptiveInputCenteredNorm_cofinal_rate_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
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
    (anchor_cofinal_rate certificate)

theorem adaptiveTransferredCenteredNorm_cofinal_rate_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
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
    (anchor_cofinal_rate certificate)

/-! ## 4. Completed contraction at the supplied strict rate -/

theorem adaptiveCofinalRepresentative_operator_norm_gap_rate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
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
      (CReal.mul (CReal.ofQ' (q * q))
        (physicalCauchyPairingLimit hw0 hw1 half Y Y)) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  apply CReal.leEv_of_convergesTo_le
    (adaptiveTransferredCenteredNorm_cofinal_rate_converges
      hw0 hw1 half M certificate X horthogonal)
    (CReal.convergesTo_constMul (q * q)
      (adaptiveInputCenteredNorm_cofinal_rate_converges
        hw0 hw1 half certificate X horthogonal))
  intro base
  exact centralPhysicalCofinalCenteredStage_operator_norm_gap_rate
    hw0 hw1 half certificate Y base

/-- A completion modulus plus exact strictness at any supplied `q < 1` on a
cofinal cutoff family gives strict contraction of the actual completed
transfer. -/
def centralPhysicalCutoffCompletedMarkovAdaptiveCofinalStrictContractionDataAtRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q) :
    CentralPhysicalCutoffCompletedMarkovStrictContractionData
      hw0 hw1 half M
        (centralPhysicalCutoffCompletedMarkovAdaptivePairingInvariant
          hw0 hw1 half M) where
  rate := q
  rate_nonnegative := certificate.rate_nonnegative
  rate_lt_one := certificate.rate_lt_one
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
      (CReal.RCscale (q * q)
        (Quotient.mk CReal.crealSetoid
          (physicalCauchyPairingLimit hw0 hw1 half Y Y)))
    rw [CReal.RCscale_mk, CReal.RCle_mk]
    exact adaptiveCofinalRepresentative_operator_norm_gap_rate
      hw0 hw1 half M certificate X horthogonalY

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalStrictGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalStrictGap.cofinal_completed_vacuum_operator_norm_gap_rate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalStrictGap.centralPhysicalCofinalCenteredStage_operator_norm_gap_rate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalStrictGap.adaptiveCofinalRepresentative_operator_norm_gap_rate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalStrictGap.centralPhysicalCutoffCompletedMarkovAdaptiveCofinalStrictContractionDataAtRate
