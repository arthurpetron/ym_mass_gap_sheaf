/-
# Cofinal finite gap for the pointwise-data adaptive BF4 transfer

The adaptive centered input and transferred graph streams now converge on the
actual completed vacuum complement.  A strict finite estimate is needed only
along a constructively cofinal family of representation cutoffs.

This file reindexes both streams along an existing
`FixedNomeCofinalCenteredSixteenth`, applies its genuine finite completed
operator bound at each selected cutoff, and passes the inequality to the two
limits.  The result is strict squared-norm contraction of the new adaptive
completed transfer at the literal rate `1/16`.

Thus the historical same-index completion modulus is absent from the entire
fixed-nome completed gap compiler.  The remaining analytic inputs are exactly
the pointwise dense cross-cutoff Cauchy data and the cofinal finite sixteenth;
neither is inhabited here.

## Axiom gate

Only constructive cofinal reindexing, the proved finite completed gap,
constructive limit order, and quotient induction are used.  There is no
classical choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalGap

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerWellDefined
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalFixedNomeCompletedOperatorNormGap
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Cofinal reindexing of the two adaptive graph limits -/

private theorem anchor_cofinal
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCofinalCenteredSixteenth w hw half)
    (threshold stage : Nat) (hstage : threshold <= stage) :
    threshold <= certificate.anchor stage :=
  Nat.le_trans hstage (certificate.anchor_ge stage)

theorem centralPhysicalAdaptiveInputCenteredNorm_cofinal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal :
      let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
      let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
      CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid Z)) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
    CReal.ConvergesTo
      (fun base => centralPhysicalCutoffCenteredStageNorm
        hw0 hw1 half Z (certificate.anchor base))
      (physicalCauchyPairingLimit hw0 hw1 half Z Z) := by
  exact convergesTo_cofinalReindex
    (centralPhysicalAdaptiveInputCenteredNorm_converges
      hw0 hw1 half pointwise X horthogonal)
    certificate.anchor (fun threshold => threshold)
    (anchor_cofinal certificate)

theorem centralPhysicalAdaptiveTransferredCenteredNorm_cofinal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal :
      let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
      let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
      CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid Z)) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
    let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
    CReal.ConvergesTo
      (fun base => centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half Z (certificate.anchor base))
      (physicalCauchyPairingLimit hw0 hw1 half TY TY) := by
  exact convergesTo_cofinalReindex
    (centralPhysicalAdaptiveTransferredCenteredNorm_converges
      hw0 hw1 half pointwise X horthogonal)
    certificate.anchor (fun threshold => threshold)
    (anchor_cofinal certificate)

/-! ## 2. Representative-level completed strictness -/

private theorem creal_mul_congr_right
    {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A B') :=
  CReal.Equiv.trans (CRealAlg.cmul_comm A B)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm B' A))

theorem centralPhysicalAdaptiveCofinalRepresentative_operator_norm_gap_sixteenth
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
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
    let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
    CReal.leEv
      (physicalCauchyPairingLimit hw0 hw1 half TY TY)
      (CReal.mul
        (CReal.ofQ'
          (physicalCutoffSixteenth * physicalCutoffSixteenth))
        (physicalCauchyPairingLimit hw0 hw1 half Y Y)) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
  have hclassYZ := centralPhysicalAdaptiveMarkovInputMap_class_eq pointwise Y
  have horthogonalZ : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half (Quotient.mk D.completionSetoid Z) := by
    rw [← hclassYZ]
    exact horthogonal
  have hgap : CReal.leEv
      (physicalCauchyPairingLimit hw0 hw1 half TY TY)
      (CReal.mul
        (CReal.ofQ'
          (physicalCutoffSixteenth * physicalCutoffSixteenth))
        (physicalCauchyPairingLimit hw0 hw1 half Z Z)) := by
    apply CReal.leEv_of_convergesTo_le
      (centralPhysicalAdaptiveTransferredCenteredNorm_cofinal_converges
        hw0 hw1 half pointwise certificate X horthogonalZ)
      (CReal.convergesTo_constMul
        (physicalCutoffSixteenth * physicalCutoffSixteenth)
        (centralPhysicalAdaptiveInputCenteredNorm_cofinal_converges
          hw0 hw1 half pointwise certificate X horthogonalZ))
    intro base
    exact centralPhysicalCofinalCenteredStage_operator_norm_gap_sixteenth
      hw0 hw1 half certificate Z base
  have hZY := physicalCauchyPairingLimit_welldef
    hw0 hw1 half
    (D.closeSymm (centralPhysicalAdaptiveMarkovInputMapClose pointwise Y))
    (D.closeSymm (centralPhysicalAdaptiveMarkovInputMapClose pointwise Y))
  exact CReal.leEv_trans hgap
    (CReal.leEv_of_equiv (creal_mul_congr_right hZY))

/-! ## 3. The strict completed vacuum-complement contraction -/

structure CentralPhysicalAdaptiveCompletedMarkovStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData
      hw0 hw1 half) : Type where
  rate : Q'
  rate_nonnegative : (0 : Q') <= rate
  rate_lt_one : rate < (1 : Q')
  contraction : forall
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half),
    CReal.RCle
      (centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
          pointwise vector).1
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
          pointwise vector).1)
      (CReal.RCscale (rate * rate)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          vector.1 vector.1))

def centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalAdaptiveCompletedMarkovStrictContractionData
      hw0 hw1 half pointwise where
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
          (centralPhysicalAdaptiveMarkovMapCauchy pointwise Y)
          (centralPhysicalAdaptiveMarkovMapCauchy pointwise Y)))
      (CReal.RCscale
        (physicalCutoffSixteenth * physicalCutoffSixteenth)
        (Quotient.mk CReal.crealSetoid
          (physicalCauchyPairingLimit hw0 hw1 half Y Y)))
    rw [CReal.RCscale_mk, CReal.RCle_mk]
    exact centralPhysicalAdaptiveCofinalRepresentative_operator_norm_gap_sixteenth
      hw0 hw1 half pointwise certificate X horthogonalY

def centralPhysicalAdaptiveCompletedMarkovCofinalLocalGluingStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (certificate : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalAdaptiveCompletedMarkovStrictContractionData
      hw0 hw1 half pointwise :=
  centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData
    hw0 hw1 half pointwise certificate.toCenteredSixteenth

#print axioms centralPhysicalAdaptiveInputCenteredNorm_cofinal_converges
#print axioms centralPhysicalAdaptiveTransferredCenteredNorm_cofinal_converges
#print axioms centralPhysicalAdaptiveCofinalRepresentative_operator_norm_gap_sixteenth
#print axioms CentralPhysicalAdaptiveCompletedMarkovStrictContractionData
#print axioms centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData
#print axioms centralPhysicalAdaptiveCompletedMarkovCofinalLocalGluingStrictContractionData

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap
