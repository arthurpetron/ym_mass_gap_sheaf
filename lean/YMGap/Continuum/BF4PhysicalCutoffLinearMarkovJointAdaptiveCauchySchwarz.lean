/-
# Positive-form Cauchy--Schwarz on the completed adaptive BF4 carrier

The joint adaptive schedule aligns two arbitrary cutoff-completion
representatives at one finite action cutoff and pays both self inner rates and
their cross inner rate.  The three same-cutoff Markov forms therefore converge
to the literal completed pairings.  Finite rational positive-form
Cauchy--Schwarz passes through those three limits.

This proves the sharp Markov-form law for the actual adaptive transfer on the
whole fixed-nome, fixed-volume completed carrier.  Pullback along the inhabited
root-sector transfer lift then supplies the previously isolated completed
sector Cauchy--Schwarz datum.

No common strict rate, thermodynamic or continuum limit, or Clay conclusion
is asserted.

## Axiom gate

Only explicit joint schedules, finite positive Markov-form algebra,
constructive-real limit order, and quotient soundness are used.  There is no
classical choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveSchedule
import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_eqv_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. The three aligned completed limits -/

/-- The aligned cross Markov form converges to the completed pairing of the
joint left action representative with the joint right input representative. -/
theorem centralPhysicalJointAdaptiveMarkovCrossForm_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let LY := centralPhysicalJointAdaptiveRightInputCauchy
      hw0 hw1 half pointwise X Y
    let TX := centralPhysicalJointAdaptiveLeftActionCauchy
      hw0 hw1 half pointwise X Y
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (TX.seq stage) (LY.seq stage)).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half TX LY) := by
  let LY := centralPhysicalJointAdaptiveRightInputCauchy
    hw0 hw1 half pointwise X Y
  let TX := centralPhysicalJointAdaptiveLeftActionCauchy
    hw0 hw1 half pointwise X Y
  apply physicalCauchyPairingRegularizedDiagonal_converges
    hw0 hw1 half TX LY
    (fun epsilon => centralPhysicalJointAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X Y (CReal.lv epsilon))
  intro epsilon hepsilon stage hstage
  change
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half
          (X.seq (centralPhysicalJointAdaptiveMarkovSampleIndex
            hw0 hw1 half pointwise X Y stage)))
        (Y.seq (centralPhysicalJointAdaptiveMarkovSampleIndex
          hw0 hw1 half pointwise X Y stage)))).rate epsilon <= stage
  rw [regularizedInnerRegularity_markov_left_rate_eq]
  exact (centralPhysicalJointAdaptiveMarkov_inner_rates_paid
    hw0 hw1 half pointwise X Y epsilon hepsilon stage hstage).2.2

/-- The aligned left self Markov form converges to its actual completed
pairing. -/
theorem centralPhysicalJointAdaptiveMarkovLeftSelfForm_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let LX := centralPhysicalJointAdaptiveLeftInputCauchy
      hw0 hw1 half pointwise X Y
    let TX := centralPhysicalJointAdaptiveLeftActionCauchy
      hw0 hw1 half pointwise X Y
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (TX.seq stage) (LX.seq stage)).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half TX LX) := by
  let LX := centralPhysicalJointAdaptiveLeftInputCauchy
    hw0 hw1 half pointwise X Y
  let TX := centralPhysicalJointAdaptiveLeftActionCauchy
    hw0 hw1 half pointwise X Y
  apply physicalCauchyPairingRegularizedDiagonal_converges
    hw0 hw1 half TX LX
    (fun epsilon => centralPhysicalJointAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X Y (CReal.lv epsilon))
  intro epsilon hepsilon stage hstage
  change
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half
          (X.seq (centralPhysicalJointAdaptiveMarkovSampleIndex
            hw0 hw1 half pointwise X Y stage)))
        (X.seq (centralPhysicalJointAdaptiveMarkovSampleIndex
          hw0 hw1 half pointwise X Y stage)))).rate epsilon <= stage
  rw [regularizedInnerRegularity_markov_left_rate_eq]
  exact (centralPhysicalJointAdaptiveMarkov_inner_rates_paid
    hw0 hw1 half pointwise X Y epsilon hepsilon stage hstage).1

/-- The aligned right self Markov form converges to its actual completed
pairing. -/
theorem centralPhysicalJointAdaptiveMarkovRightSelfForm_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let LY := centralPhysicalJointAdaptiveRightInputCauchy
      hw0 hw1 half pointwise X Y
    let TY := centralPhysicalJointAdaptiveRightActionCauchy
      hw0 hw1 half pointwise X Y
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (TY.seq stage) (LY.seq stage)).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half TY LY) := by
  let LY := centralPhysicalJointAdaptiveRightInputCauchy
    hw0 hw1 half pointwise X Y
  let TY := centralPhysicalJointAdaptiveRightActionCauchy
    hw0 hw1 half pointwise X Y
  apply physicalCauchyPairingRegularizedDiagonal_converges
    hw0 hw1 half TY LY
    (fun epsilon => centralPhysicalJointAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X Y (CReal.lv epsilon))
  intro epsilon hepsilon stage hstage
  change
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half
          (Y.seq (centralPhysicalJointAdaptiveMarkovSampleIndex
            hw0 hw1 half pointwise X Y stage)))
        (Y.seq (centralPhysicalJointAdaptiveMarkovSampleIndex
          hw0 hw1 half pointwise X Y stage)))).rate epsilon <= stage
  rw [regularizedInnerRegularity_markov_left_rate_eq]
  exact (centralPhysicalJointAdaptiveMarkov_inner_rates_paid
    hw0 hw1 half pointwise X Y epsilon hepsilon stage hstage).2.1

/-! ## 2. Finite positive-form Cauchy--Schwarz through the joint limits -/

/-- Sharp positive-Markov-form Cauchy--Schwarz for two arbitrary global
cutoff-completion representatives. -/
theorem centralPhysicalJointAdaptiveMarkovForm_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let LX := centralPhysicalJointAdaptiveLeftInputCauchy
      hw0 hw1 half pointwise X Y
    let LY := centralPhysicalJointAdaptiveRightInputCauchy
      hw0 hw1 half pointwise X Y
    let TX := centralPhysicalJointAdaptiveLeftActionCauchy
      hw0 hw1 half pointwise X Y
    let TY := centralPhysicalJointAdaptiveRightActionCauchy
      hw0 hw1 half pointwise X Y
    CReal.leEv
      (CReal.mul
        (physicalCauchyPairingLimit hw0 hw1 half TX LY)
        (physicalCauchyPairingLimit hw0 hw1 half TX LY))
      (CReal.mul
        (physicalCauchyPairingLimit hw0 hw1 half TX LX)
        (physicalCauchyPairingLimit hw0 hw1 half TY LY)) := by
  let LX := centralPhysicalJointAdaptiveLeftInputCauchy
    hw0 hw1 half pointwise X Y
  let LY := centralPhysicalJointAdaptiveRightInputCauchy
    hw0 hw1 half pointwise X Y
  let TX := centralPhysicalJointAdaptiveLeftActionCauchy
    hw0 hw1 half pointwise X Y
  let TY := centralPhysicalJointAdaptiveRightActionCauchy
    hw0 hw1 half pointwise X Y
  apply CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_mul_general
      (centralPhysicalJointAdaptiveMarkovCrossForm_converges
        hw0 hw1 half pointwise X Y)
      (centralPhysicalJointAdaptiveMarkovCrossForm_converges
        hw0 hw1 half pointwise X Y))
    (CReal.convergesTo_mul_general
      (centralPhysicalJointAdaptiveMarkovLeftSelfForm_converges
        hw0 hw1 half pointwise X Y)
      (centralPhysicalJointAdaptiveMarkovRightSelfForm_converges
        hw0 hw1 half pointwise X Y))
  intro stage
  let index := centralPhysicalJointAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise X Y stage
  let left := X.seq index
  let right := Y.seq index
  let a := (innerLimit hw0 hw1 half
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half left) right).approx stage
  let b := (innerLimit hw0 hw1 half
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half left) left).approx stage
  let c := (innerLimit hw0 hw1 half
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half right) right).approx stage
  let A := centralPhysicalWeightedInner
    w (Q'.le_of_lt hw0) stage half
    (centralPhysicalMarkovApply
      w (Q'.le_of_lt hw0) stage half left.value) right.value
  let B := centralPhysicalWeightedInner
    w (Q'.le_of_lt hw0) stage half
    (centralPhysicalMarkovApply
      w (Q'.le_of_lt hw0) stage half left.value) left.value
  let C := centralPhysicalWeightedInner
    w (Q'.le_of_lt hw0) stage half
    (centralPhysicalMarkovApply
      w (Q'.le_of_lt hw0) stage half right.value) right.value
  change CReal.leEv
    (CReal.mul (CReal.ofQ' a) (CReal.ofQ' a))
    (CReal.mul (CReal.ofQ' b) (CReal.ofQ' c))
  have ha : a ≈ A := innerLimit_markovCutoffAction_cross_approx_eqv_form
    hw0 hw1 half stage left right
  have hb : b ≈ B := innerLimit_markovCutoffAction_cross_approx_eqv_form
    hw0 hw1 half stage left left
  have hc : c ≈ C := innerLimit_markovCutoffAction_cross_approx_eqv_form
    hw0 hw1 half stage right right
  have hfinite : A * A <= B * C :=
    centralPhysicalMarkovForm_cauchy_schwarz
      w (Q'.le_of_lt hw0) stage half left.value right.value
  have hrat : a * a <= b * c :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (qmul_eqv_congr ha ha))
      (Q'.le_trans' _ _ _ hfinite
        (Q'.ge_of_eqv (qmul_eqv_congr hb hc)))
  intro epsilon hepsilon
  exact ⟨0, fun approximation _ => Q'.le_trans' _ _ _ hrat
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

/-! ## 3. The actual global and sector completed forms -/

/-- Sharp positive-form Cauchy--Schwarz for the actual adaptive transfer on
the whole cutoff-completed physical carrier. -/
theorem centralPhysicalAdaptiveCompletedMarkovForm_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalAdaptiveCompletedMarkovTransfer pointwise left)
          right)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalAdaptiveCompletedMarkovTransfer pointwise left)
          right))
      (CReal.RCmul
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalAdaptiveCompletedMarkovTransfer pointwise left)
          left)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalAdaptiveCompletedMarkovTransfer pointwise right)
          right)) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  let leftSample := centralPhysicalJointAdaptiveMarkovLeftSample
    hw0 hw1 half pointwise X Y
  let rightSample := centralPhysicalJointAdaptiveMarkovRightSample
    hw0 hw1 half pointwise X Y
  let LX := centralPhysicalJointAdaptiveLeftInputCauchy
    hw0 hw1 half pointwise X Y
  let LY := centralPhysicalJointAdaptiveRightInputCauchy
    hw0 hw1 half pointwise X Y
  let TX := centralPhysicalJointAdaptiveLeftActionCauchy
    hw0 hw1 half pointwise X Y
  let TY := centralPhysicalJointAdaptiveRightActionCauchy
    hw0 hw1 half pointwise X Y
  have hLX := centralPhysicalAdmissibleMarkovInput_class_eq leftSample
  have hLY := centralPhysicalAdmissibleMarkovInput_class_eq rightSample
  have hTX := centralPhysicalAdmissibleMarkovMap_class_eq_adaptive
    hw0 hw1 half pointwise X leftSample
  have hTY := centralPhysicalAdmissibleMarkovMap_class_eq_adaptive
    hw0 hw1 half pointwise Y rightSample
  rw [centralPhysicalAdaptiveCompletedMarkovTransfer_mk]
  rw [centralPhysicalAdaptiveCompletedMarkovTransfer_mk]
  rw [← hTX, ← hTY, hLX, hLY]
  change CReal.RCle
    (CReal.RCmul
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half TX LY))
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half TX LY)))
    (CReal.RCmul
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half TX LX))
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half TY LY)))
  rw [CReal.RCmul_mk, CReal.RCmul_mk, CReal.RCle_mk]
  exact centralPhysicalJointAdaptiveMarkovForm_cauchy_schwarz
    hw0 hw1 half pointwise X Y

/-- The actual completed root-sector Markov form obeys sharp
Cauchy--Schwarz on every pair of arbitrary completed sector vectors. -/
theorem centralPhysicalVacuumSectorCylinderCompletedMarkovForm_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedTransfer
            hw0 hw1 half left) right)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedTransfer
            hw0 hw1 half left) right))
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedTransfer
            hw0 hw1 half left) left)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedTransfer
            hw0 hw1 half right) right)) := by
  unfold centralPhysicalVacuumSectorCylinderCompletedTransfer
  rw [CentralPhysicalVacuumSectorCylinderTransferLiftData.completedInner_transfer_eq_global
    (centralPhysicalVacuumSectorCylinderTransferLiftData
      hw0 hw1 half) left right]
  rw [CentralPhysicalVacuumSectorCylinderTransferLiftData.completedInner_transfer_eq_global
    (centralPhysicalVacuumSectorCylinderTransferLiftData
      hw0 hw1 half) left left]
  rw [CentralPhysicalVacuumSectorCylinderTransferLiftData.completedInner_transfer_eq_global
    (centralPhysicalVacuumSectorCylinderTransferLiftData
      hw0 hw1 half) right right]
  exact centralPhysicalAdaptiveCompletedMarkovForm_cauchy_schwarz
    hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)
    (centralPhysicalVacuumSectorCylinderCompletionToGlobal left)
    (centralPhysicalVacuumSectorCylinderCompletionToGlobal right)

/-- The previously isolated completed sector positive-form law is now
inhabited without an additional certificate. -/
def centralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
      hw0 hw1 half where
  cauchy_schwarz :=
    centralPhysicalVacuumSectorCylinderCompletedMarkovForm_cauchy_schwarz
      hw0 hw1 half

/-- One supplied sector-local cofinal rate now gives the completed operator
contraction directly; no separate positive-form certificate remains. -/
def centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtRate_of_markovCS
    hw0 hw1 half
    (centralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
      hw0 hw1 half)
    certificate

#print axioms centralPhysicalJointAdaptiveMarkovCrossForm_converges
#print axioms centralPhysicalJointAdaptiveMarkovLeftSelfForm_converges
#print axioms centralPhysicalJointAdaptiveMarkovRightSelfForm_converges
#print axioms centralPhysicalJointAdaptiveMarkovForm_cauchy_schwarz
#print axioms centralPhysicalAdaptiveCompletedMarkovForm_cauchy_schwarz
#print axioms centralPhysicalVacuumSectorCylinderCompletedMarkovForm_cauchy_schwarz
#print axioms centralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
#print axioms centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
