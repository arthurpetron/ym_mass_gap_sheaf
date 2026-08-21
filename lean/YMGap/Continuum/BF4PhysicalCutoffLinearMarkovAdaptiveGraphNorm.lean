/-
# Centered graph norms for the adaptive completed BF4 transfer

The adaptive graph schedule pays all four inner rates and the adaptive
transfer now preserves the completed vacuum complement.  This file therefore
diagonalizes the input and action self-pair streams and removes their vacuum
means.

The finite graph representative is the input-side adaptive reindexing `Z` of
the graph-normalized representative.  Its literal finite transferred norm is
the same-cutoff Markov image of `Z`; this is definitionally the adaptive
output sequence.  Hence the two centered finite graph streams converge to the
completed squared norm of `Z` and of its adaptive image.

No finite strict-gap certificate is used yet.  Transporting a cofinal finite
sixteenth through these two limits is the next contraction step.

## Axiom gate

Only explicit graph rates, finite centering identities, constructive-real
limit algebra, and quotient soundness are used.  There is no classical
choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormCofinality
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormCofinality.CentralPhysicalLinearMarkovGraphNormInnerCofinality
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_eqv_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. The two raw self-pair diagonals -/

theorem centralPhysicalAdaptiveGraphInputSquare_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (Z.seq stage) (Z.seq stage)).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half Z Z) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  exact physicalCauchyPairingRegularizedDiagonal_converges
    hw0 hw1 half Z Z
    (centralPhysicalAdaptiveGraphDiagonalRate
      hw0 hw1 half pointwise X)
    (fun epsilon hepsilon stage hstage =>
      (centralPhysicalAdaptiveGraph_input_rates_paid
        hw0 hw1 half pointwise X epsilon hepsilon stage hstage).1)

theorem centralPhysicalAdaptiveGraphActionSquare_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (TY.seq stage) (TY.seq stage)).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half TY TY) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
  exact physicalCauchyPairingRegularizedDiagonal_converges
    hw0 hw1 half TY TY
    (centralPhysicalAdaptiveGraphDiagonalRate
      hw0 hw1 half pointwise X)
    (fun epsilon hepsilon stage hstage =>
      (centralPhysicalAdaptiveGraph_action_rates_paid
        hw0 hw1 half pointwise X epsilon hepsilon stage hstage).1)

/-! ## 2. Same-cutoff transferred norm identity without a completion modulus -/

theorem centeredStageTransferredNorm_equiv_adaptive_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    let TX := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (X.seq stage)
    CReal.Equiv
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half X stage)
      (CReal.add
        (CReal.ofQ'
          ((innerLimit hw0 hw1 half TX TX).approx stage))
        (CReal.neg
          (CReal.mul
            (CReal.ofQ'
              ((innerLimit hw0 hw1 half TX
                centralPhysicalLinearVacuum).approx stage))
            (CReal.ofQ'
              ((innerLimit hw0 hw1 half TX
                centralPhysicalLinearVacuum).approx stage))))) := by
  let hw := Q'.le_of_lt hw0
  let D := (centralPhysicalSmulGNS w hw stage half).toGNSData
  let raw := (X.seq stage).value
  let transferred := centralPhysicalMarkovApply w hw stage half raw
  let mean := centralPhysicalStationaryMean w hw stage half transferred
  let centered := centralPhysicalCenteredObservable w hw stage half raw
  let centeredTransferred :=
    centralPhysicalCenteredObservable w hw stage half transferred
  let TX := centralPhysicalLinearMarkovCutoffAction
    hw stage half (X.seq stage)
  have hintertwine : D.rad
      (centralPhysicalMarkovApply w hw stage half centered)
      centeredTransferred :=
    centralPhysicalMarkovApply_centered_rad w hw stage half raw
  have hwelldef :
      D.B (centralPhysicalMarkovApply w hw stage half centered)
          (centralPhysicalMarkovApply w hw stage half centered) ≈
        D.B centeredTransferred centeredTransferred :=
    D.B_welldef hintertwine hintertwine
  have hcentered : D.B centeredTransferred centeredTransferred ≈
      D.B transferred transferred + -(mean * mean) := by
    simpa only [D, transferred, mean, centeredTransferred,
      centralPhysicalSmulGNS_B_eq] using
      (centralPhysicalCenteredObservable_norm_identity
        w hw stage half transferred)
  have hraw := innerLimit_markovCutoffAction_both_approx_eqv
    hw0 hw1 half stage (X.seq stage) (X.seq stage)
  have hinputMeanStage := innerLimit_approx_eqv_stage
    hw0 hw1 half stage (X.seq stage) centralPhysicalLinearVacuum
  have hinputMean :
      (innerLimit hw0 hw1 half
        (X.seq stage) centralPhysicalLinearVacuum).approx stage ≈
        centralPhysicalStationaryMean w hw stage half raw := by
    exact Q'.eqv_trans _ _ _ hinputMeanStage
      (Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq
          (centralPhysicalSmulGNS_B_eq
            w hw stage half raw centralPhysicalLinearVacuum.value))
        (centralPhysicalWeightedInner_vacuum_right
          w hw stage half raw))
  have hactionMeanInput :=
    innerLimit_markovCutoffAction_vacuum_approx_eqv
      hw0 hw1 half stage (X.seq stage)
  have hstationary : mean ≈
      centralPhysicalStationaryMean w hw stage half raw :=
    centralPhysicalStationaryMean_markovApply w hw stage half raw
  have hmean :
      (innerLimit hw0 hw1 half TX
        centralPhysicalLinearVacuum).approx stage ≈ mean := by
    exact Q'.eqv_trans _ _ _ hactionMeanInput
      (Q'.eqv_trans _ _ _ hinputMean (Q'.eqv_symm hstationary))
  apply YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
  intro k
  change D.B
      (centralPhysicalMarkovApply w hw stage half centered)
      (centralPhysicalMarkovApply w hw stage half centered) ≈
    (innerLimit hw0 hw1 half TX TX).approx stage +
      -((innerLimit hw0 hw1 half TX
          centralPhysicalLinearVacuum).approx stage *
        (innerLimit hw0 hw1 half TX
          centralPhysicalLinearVacuum).approx stage)
  exact Q'.eqv_trans _ _ _ hwelldef
    (Q'.eqv_trans _ _ _ hcentered
      (Q'.add_eqv_congr'
        (Q'.eqv_symm hraw)
        (Q'.neg_eqv_congr _ _
          (qmul_eqv_congr (Q'.eqv_symm hmean) (Q'.eqv_symm hmean)))))

/-! ## 3. Removing the completed vacuum mean -/

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

private theorem completed_orthogonal_pairing_equiv_zero
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (Z : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid Z)) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half Z
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      CReal.czero := by
  unfold CentralPhysicalCutoffCompletedVacuumOrthogonal
    centralPhysicalCutoffCompletedVacuum
    embedCentralPhysicalLinearObservable at horthogonal
  change Quotient.mk CReal.crealSetoid
      (physicalCauchyPairingLimit hw0 hw1 half Z
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) =
    CReal.RCzero at horthogonal
  exact Quotient.exact horthogonal

theorem centralPhysicalAdaptiveInputCenteredNorm_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
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
      (centralPhysicalCutoffCenteredStageNorm hw0 hw1 half Z)
      (physicalCauchyPairingLimit hw0 hw1 half Z Z) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  let rawSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (Z.seq stage) (Z.seq stage)).approx stage)
  let meanSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (Z.seq stage) centralPhysicalLinearVacuum).approx stage)
  have hraw : CReal.ConvergesTo rawSeq
      (physicalCauchyPairingLimit hw0 hw1 half Z Z) := by
    simpa only [rawSeq, Y, Z] using
      (centralPhysicalAdaptiveGraphInputSquare_converges
        hw0 hw1 half pointwise X)
  have hmeanRaw := centralPhysicalAdaptiveGraphInputMean_converges
    hw0 hw1 half pointwise X
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr
      (by simpa only [meanSeq, Y, Z] using hmeanRaw)
    exact completed_orthogonal_pairing_equiv_zero Z horthogonal
  have hsquare := CReal.convergesTo_mul_general hmean hmean
  have hsquareZero : CReal.ConvergesTo
      (fun stage => CReal.mul (meanSeq stage) (meanSeq stage))
      CReal.czero :=
    CReal.convergesTo_limit_congr hsquare (creal_mul_czero CReal.czero)
  have hcenteredRaw := CReal.convergesTo_add hraw
    (CReal.convergesTo_neg hsquareZero)
  have hcenteredLimit : CReal.ConvergesTo
      (fun stage => CReal.add (rawSeq stage)
        (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
      (physicalCauchyPairingLimit hw0 hw1 half Z Z) := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
      (creal_add_czero (physicalCauchyPairingLimit hw0 hw1 half Z Z))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun stage => CReal.add (rawSeq stage)
      (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
  · intro stage
    exact CReal.Equiv.symm
      (centeredStageNorm_equiv_diagonal hw0 hw1 half Z stage)
  · simpa only [rawSeq, meanSeq] using hcenteredLimit

theorem centralPhysicalAdaptiveTransferredCenteredNorm_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
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
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half Z)
      (physicalCauchyPairingLimit hw0 hw1 half TY TY) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
  let rawSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (TY.seq stage) (TY.seq stage)).approx stage)
  let meanSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (TY.seq stage) centralPhysicalLinearVacuum).approx stage)
  have hraw : CReal.ConvergesTo rawSeq
      (physicalCauchyPairingLimit hw0 hw1 half TY TY) := by
    simpa only [rawSeq, Y, TY] using
      (centralPhysicalAdaptiveGraphActionSquare_converges
        hw0 hw1 half pointwise X)
  have hmeanRaw := centralPhysicalAdaptiveGraphActionMean_converges
    hw0 hw1 half pointwise X
  have hclassZY := centralPhysicalAdaptiveMarkovInputMap_class_eq pointwise Y
  have horthogonalY : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk D.completionSetoid Y) := by
    rw [hclassZY]
    exact horthogonal
  have hmeanTarget : CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half TY
        (D.constant centralPhysicalLinearVacuum))
      CReal.czero :=
    CReal.Equiv.trans
      (centralPhysicalAdaptiveGraphPairingLimit_vacuum_equiv
        hw0 hw1 half pointwise X)
      (completed_orthogonal_pairing_equiv_zero Y horthogonalY)
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr
      (by simpa only [meanSeq, Y, TY] using hmeanRaw)
    exact hmeanTarget
  have hsquare := CReal.convergesTo_mul_general hmean hmean
  have hsquareZero : CReal.ConvergesTo
      (fun stage => CReal.mul (meanSeq stage) (meanSeq stage))
      CReal.czero :=
    CReal.convergesTo_limit_congr hsquare (creal_mul_czero CReal.czero)
  have hcenteredRaw := CReal.convergesTo_add hraw
    (CReal.convergesTo_neg hsquareZero)
  have hcenteredLimit : CReal.ConvergesTo
      (fun stage => CReal.add (rawSeq stage)
        (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
      (physicalCauchyPairingLimit hw0 hw1 half TY TY) := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
      (creal_add_czero (physicalCauchyPairingLimit hw0 hw1 half TY TY))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun stage => CReal.add (rawSeq stage)
      (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
  · intro stage
    exact CReal.Equiv.symm
      (centeredStageTransferredNorm_equiv_adaptive_diagonal
        hw0 hw1 half Z stage)
  · simpa only [rawSeq, meanSeq, TY] using hcenteredLimit

#print axioms centralPhysicalAdaptiveGraphInputSquare_converges
#print axioms centralPhysicalAdaptiveGraphActionSquare_converges
#print axioms centeredStageTransferredNorm_equiv_adaptive_diagonal
#print axioms centralPhysicalAdaptiveInputCenteredNorm_converges
#print axioms centralPhysicalAdaptiveTransferredCenteredNorm_converges

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm
