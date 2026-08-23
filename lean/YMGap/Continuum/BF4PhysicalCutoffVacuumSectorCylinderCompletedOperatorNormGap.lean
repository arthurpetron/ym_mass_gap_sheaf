/-
# The cutoff-removed BF4 sector form-to-operator compiler

The actual completed root-sector transfer form is now nonnegative and obeys
the strict upper estimate at every supplied cofinal rate.  A quadratic-form
bound alone does not control the norm of a potentially nonsymmetric map.  The
remaining functional-analytic input is the sharp Cauchy--Schwarz law for the
positive Markov form

  (left,right) |-> <T left,right>

on the same cutoff-removed sector completion.

This file names exactly that one law and proves the constructive,
division-free form-to-operator compiler.  Given the law and a completed form
gap at rate `q`, the actual sector transfer satisfies

  ||T v||^2 <= q^2 ||v||^2

on the completed vacuum complement.  Hence the existing power and
same-object correlation machinery can consume the result directly.

No Markov-form Cauchy--Schwarz certificate and no common cofinal rate are
constructed here.  No thermodynamic or continuum limit, or Clay conclusion,
is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap

/-! ## 1. The exact positive-Markov-form input -/

/-- Sharp Cauchy--Schwarz for the actual cutoff-removed sector Markov form.
This is the sole additional functional-analytic law needed to upgrade the
already constructed strict form interval to a squared-norm contraction. -/
structure CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type 1 where
  cauchy_schwarz : forall
    (left right : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half),
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
            hw0 hw1 half right) right))

/-! ## 2. Division-free square-form cancellation -/

/-- Move a rational scale from the right factor of an `RC` product to its
left factor. -/
private theorem RCmul_scale_right_eq_scale_left
    (scalar : Q') (left right : CReal.RC) :
    CReal.RCmul left (CReal.RCscale scalar right) =
      CReal.RCmul (CReal.RCscale scalar left) right := by
  refine Quotient.inductionOn₂ left right ?_
  intro L R
  exact Quotient.sound
    (YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
      (fun n => by
        change (L.approx n * (scalar * R.approx n)).eqv
          ((scalar * L.approx n) * R.approx n)
        ring_qeqv))

/-- The positive Markov-form Cauchy--Schwarz law and the strict form interval
give the square-form estimate on the actual completed sector.  Cancellation
does not divide by `||T v||^2`, which may vanish. -/
theorem centralPhysicalVacuumSectorCylinderCompletedTransfer_square_form_gap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (markovCS :
      CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
        hw0 hw1 half)
    (gap : CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData
      hw0 hw1 half)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector).1)
      (CReal.RCscale gap.rate
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
            hw0 hw1 half vector).1 vector.1)) := by
  let Tvector :=
    centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
      hw0 hw1 half vector
  let normT := centralPhysicalVacuumSectorCylinderCompletedInner
    hw0 hw1 half Tvector.1 Tvector.1
  let form := centralPhysicalVacuumSectorCylinderCompletedInner
    hw0 hw1 half Tvector.1 vector.1
  let nextForm := centralPhysicalVacuumSectorCylinderCompletedInner
    hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
        hw0 hw1 half Tvector).1 Tvector.1
  have hcs : CReal.RCle
      (CReal.RCmul normT normT)
      (CReal.RCmul form nextForm) := by
    exact markovCS.cauchy_schwarz vector.1 Tvector.1
  have hnext : CReal.RCle nextForm (CReal.RCscale gap.rate normT) :=
    gap.form_gap Tvector
  have hformNonnegative : CReal.RCnonneg form :=
    gap.form_nonnegative vector
  have hproductScaled : CReal.RCle
      (CReal.RCmul form nextForm)
      (CReal.RCmul form (CReal.RCscale gap.rate normT)) :=
    CReal.RCmul_mono_nonnegative_left_local hformNonnegative hnext
  rw [RCmul_scale_right_eq_scale_left] at hproductScaled
  have hnormNonnegative : CReal.RCnonneg normT := by
    unfold normT centralPhysicalVacuumSectorCylinderCompletedInner
    exact centralPhysicalCutoffCompletedInner_self_nonneg hw0 hw1 half _
  have hscaledFormNonnegative :
      CReal.RCnonneg (CReal.RCscale gap.rate form) := by
    have hscaled := CReal.RCscale_mono gap.rate_nonnegative hformNonnegative
    rwa [CReal.RCscale_RCzero] at hscaled
  exact CReal.RCle_of_mul_self_le_mul_right_nonnegative
    hnormNonnegative hscaledFormNonnegative
      (CReal.RCle_trans hcs hproductScaled)

/-! ## 3. Actual completed squared-norm contraction -/

/-- The square-form estimate followed by the original form estimate gives
the genuine squared-norm contraction at rate `q^2`. -/
theorem centralPhysicalVacuumSectorCylinderCompletedTransfer_norm_gap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (markovCS :
      CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
        hw0 hw1 half)
    (gap : CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData
      hw0 hw1 half)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector).1)
      (CReal.RCscale (gap.rate * gap.rate)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          vector.1 vector.1)) := by
  refine CReal.RCle_trans
    (centralPhysicalVacuumSectorCylinderCompletedTransfer_square_form_gap
      markovCS gap vector) ?_
  have hform := gap.form_gap vector
  have hscaled := CReal.RCscale_mono gap.rate_nonnegative hform
  refine CReal.RCle_trans hscaled ?_
  rw [CReal.RCscale_RCscale]
  exact CReal.RCle_refl _

/-- Package the form-to-operator conclusion in the sector contraction datum
already consumed by power and same-object correlation decay. -/
def centralPhysicalVacuumSectorCylinderCompletedStrictContractionData_of_formGap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (markovCS :
      CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
        hw0 hw1 half)
    (gap : CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData
      hw0 hw1 half) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half where
  rate := gap.rate
  rate_nonnegative := gap.rate_nonnegative
  rate_lt_one := gap.rate_lt_one
  contraction :=
    centralPhysicalVacuumSectorCylinderCompletedTransfer_norm_gap markovCS gap

/-- In particular, one supplied cofinal sector rate and the positive
Markov-form law give the literal completed operator contraction with no
separate completion hypothesis. -/
def centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtRate_of_markovCS
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (markovCS :
      CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
        hw0 hw1 half)
    {q : Q'}
    (certificate : FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionData_of_formGap
    markovCS
    (centralPhysicalVacuumSectorCylinderCompletedStrictFormGapDataAtRate
      hw0 hw1 half certificate)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap.centralPhysicalVacuumSectorCylinderCompletedTransfer_square_form_gap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap.centralPhysicalVacuumSectorCylinderCompletedTransfer_norm_gap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap.centralPhysicalVacuumSectorCylinderCompletedStrictContractionData_of_formGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap.centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtRate_of_markovCS
