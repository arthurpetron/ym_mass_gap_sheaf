/-
# Arbitrary-rate cofinal gap for the pointwise-adaptive BF4 transfer

The pointwise-adaptive completed transfer no longer needs the historical
same-index Markov completion modulus.  Its existing cofinal gap compiler was,
however, specialized to the literal rate `1/16`, while the arbitrary-rate
compiler still followed the older completion-modulus route.

This file combines the modern pointwise-adaptive graph limits with the
already-proved arbitrary-rate finite anchor theorem.  A single cofinal
centered certificate carrying any rational `q` with `0 <= q < 1` therefore
gives squared-norm contraction by `q*q` on the actual completed physical
vacuum complement.

Specializing the pointwise input to the already-constructed stationary-shell
Cauchy data leaves only the cofinal strict-rate certificate as an analytic
input.  No such common-rate certificate, thermodynamic limit, continuum QFT,
or Clay mass-gap theorem is constructed here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalStrictGap
import YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerWellDefined
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Cofinal reindexing at a supplied strict rate -/

private theorem anchor_cofinal_rate
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap w hw half q)
    (threshold stage : Nat) (hstage : threshold <= stage) :
    threshold <= certificate.anchor stage :=
  Nat.le_trans hstage (certificate.anchor_ge stage)

theorem centralPhysicalAdaptiveInputCenteredNorm_cofinal_rate_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
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
    (anchor_cofinal_rate certificate)

theorem centralPhysicalAdaptiveTransferredCenteredNorm_cofinal_rate_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
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
    (anchor_cofinal_rate certificate)

/-! ## 2. Representative-level contraction -/

private theorem creal_mul_congr_right
    {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A B') :=
  CReal.Equiv.trans (CRealAlg.cmul_comm A B)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm B' A))

theorem centralPhysicalAdaptiveCofinalRepresentative_operator_norm_gap_rate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
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
    let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
    CReal.leEv
      (physicalCauchyPairingLimit hw0 hw1 half TY TY)
      (CReal.mul (CReal.ofQ' (q * q))
        (physicalCauchyPairingLimit hw0 hw1 half Y Y)) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
  have hclassYZ := centralPhysicalAdaptiveMarkovInputMap_class_eq pointwise Y
  have horthogonalZ : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half (Quotient.mk D.completionSetoid Z) := by
    rw [<- hclassYZ]
    exact horthogonal
  have hgap : CReal.leEv
      (physicalCauchyPairingLimit hw0 hw1 half TY TY)
      (CReal.mul (CReal.ofQ' (q * q))
        (physicalCauchyPairingLimit hw0 hw1 half Z Z)) := by
    apply CReal.leEv_of_convergesTo_le
      (centralPhysicalAdaptiveTransferredCenteredNorm_cofinal_rate_converges
        hw0 hw1 half pointwise certificate X horthogonalZ)
      (CReal.convergesTo_constMul (q * q)
        (centralPhysicalAdaptiveInputCenteredNorm_cofinal_rate_converges
          hw0 hw1 half pointwise certificate X horthogonalZ))
    intro base
    exact centralPhysicalCofinalCenteredStage_operator_norm_gap_rate
      hw0 hw1 half certificate Z base
  have hZY := physicalCauchyPairingLimit_welldef
    hw0 hw1 half
    (D.closeSymm (centralPhysicalAdaptiveMarkovInputMapClose pointwise Y))
    (D.closeSymm (centralPhysicalAdaptiveMarkovInputMapClose pointwise Y))
  exact CReal.leEv_trans hgap
    (CReal.leEv_of_equiv (creal_mul_congr_right hZY))

/-! ## 3. Completed contraction and concrete specialization -/

/-- A cofinal finite certificate at any supplied strict rational rate gives
contraction of the actual pointwise-adaptive completed transfer. -/
def centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionDataAtRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q) :
    CentralPhysicalAdaptiveCompletedMarkovStrictContractionData
      hw0 hw1 half pointwise where
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
      rw [<- hclass]
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
      (CReal.RCscale (q * q)
        (Quotient.mk CReal.crealSetoid
          (physicalCauchyPairingLimit hw0 hw1 half Y Y)))
    rw [CReal.RCscale_mk, CReal.RCle_mk]
    exact centralPhysicalAdaptiveCofinalRepresentative_operator_norm_gap_rate
      hw0 hw1 half pointwise certificate X horthogonalY

/-- After the stationary source-shell theorem, the cofinal strict-rate
certificate is the sole remaining input to the completed global gap. -/
def centralPhysicalConcreteAdaptiveCompletedMarkovCofinalStrictContractionDataAtRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q) :
    CentralPhysicalAdaptiveCompletedMarkovStrictContractionData
      hw0 hw1 half
      (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) :=
  centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionDataAtRate
    hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) certificate

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap.centralPhysicalAdaptiveInputCenteredNorm_cofinal_rate_converges
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap.centralPhysicalAdaptiveTransferredCenteredNorm_cofinal_rate_converges
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap.centralPhysicalAdaptiveCofinalRepresentative_operator_norm_gap_rate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap.centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionDataAtRate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap.centralPhysicalConcreteAdaptiveCompletedMarkovCofinalStrictContractionDataAtRate
