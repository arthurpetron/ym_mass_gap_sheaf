/-
# Bounded symmetric dyadic derivative on the original Wilson carrier

The explicit dyadic smoothing estimate bounds the derivative limit in the
original norm. Finite quotients are symmetric, so their represented limit is
symmetric and rational-linear as well. The map is evaluated on the original
input but differentiates the positive-time image T(1)x; this is not a bounded
Hamiltonian or a whole-carrier generator. No regularized-log identification,
physical calibration, or removal of the original boundary kernel is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
import YMGap.Continuum.BF4WilsonAllNomeLogOperator

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (full_mesh_time)
open YMGap.Continuum.BF4WilsonAllNomeLogOperator (pairing_limits_eq)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root root_symmetric)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "Q" => differenceQuotient hw0 hw1
local notation "R" => root hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

private theorem quotient_defect_time_commute (depth : Nat) (x : V) :
    T 1 (defect hw0 hw1 depth x) = defect hw0 hw1 depth (T 1 x) := by
  calc
    T 1 (defect hw0 hw1 depth x) =
        meshAction hw0 hw1 0 1 (defect hw0 hw1 depth x) :=
      (full_mesh_time hw0 hw1 0 (defect hw0 hw1 depth x)).symm
    _ = defect hw0 hw1 depth (meshAction hw0 hw1 0 1 x) :=
      time_defect hw0 hw1 0 1 depth x
    _ = defect hw0 hw1 depth (T 1 x) :=
      congrArg (defect hw0 hw1 depth) (full_mesh_time hw0 hw1 0 x)

/-- Each finite quotient is symmetric on the SAME original completion. -/
theorem quotient_symmetric (depth : Nat) (x y : V) :
    B (Q depth x) y = B x (Q depth y) := by
  let c := Q'.ofNat (2^depth)
  calc
    B (Q depth x) y =
        RCscale c (B (defect hw0 hw1 depth (T 1 x)) y) := by
          rw [differenceQuotient, completedInner_smul_left]
    _ = RCscale c (B (T 1 x) (defect hw0 hw1 depth y)) :=
          congrArg (RCscale c) (defect_symmetric hw0 hw1 depth (T 1 x) y)
    _ = RCscale c (B x (T 1 (defect hw0 hw1 depth y))) :=
          congrArg (RCscale c) (completedInner_time_balance hw0 hw1 1 x
            (defect hw0 hw1 depth y))
    _ = RCscale c (B x (defect hw0 hw1 depth (T 1 y))) :=
          congrArg (fun z => RCscale c (B x z))
            (quotient_defect_time_commute hw0 hw1 depth y)
    _ = B x (Q depth y) := by
          rw [differenceQuotient, completedInner_smul_right]

/-- The dyadic derivative is bounded in the original squared norm. -/
theorem quotient_norm_bound (depth : Nat) (x : V) :
    RCle (B (Q depth x) (Q depth x)) (B x x) := by
  let c := Q'.ofNat (2^depth)
  have h := smoothing_bound hw0 hw1 depth (2^depth) 1 x
  have htime :
      meshAction hw0 hw1 depth (2^depth) (defect hw0 hw1 depth x) =
        defect hw0 hw1 depth (T 1 x) := by
    calc
      meshAction hw0 hw1 depth (2^depth) (defect hw0 hw1 depth x) =
          defect hw0 hw1 depth (meshAction hw0 hw1 depth (2^depth) x) :=
        time_defect hw0 hw1 depth (2^depth) depth x
      _ = defect hw0 hw1 depth (T 1 x) :=
        congrArg (defect hw0 hw1 depth) (full_mesh_time hw0 hw1 depth x)
  rw [show defectPower hw0 hw1 depth 1 x = defect hw0 hw1 depth x from rfl,
    Nat.one_mul, htime] at h
  have hcoeff : Q'.eqv (c*c) (c^(1+1)) := by
    rw [Q'.pow_succ, Q'.pow_succ]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv c).symm
  change RCle (B (completedSmul hw0 hw1 c (defect hw0 hw1 depth (T 1 x)))
    (completedSmul hw0 hw1 c (defect hw0 hw1 depth (T 1 x)))) (B x x)
  rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale,
    scale_congr hcoeff]
  exact h

/-- The represented derivative limit obeys the same original norm bound. -/
theorem derivativeAction_norm_bound (x : V) :
    RCle (B (A x) (A x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [derivativeAction_pin]
  apply rowLimit_norm_bound hw0 hw1 (quotientRows hw0 hw1 X)
    (B (Class X) (Class X))
  intro n
  rw [quotientRows_pin]
  exact quotient_norm_bound hw0 hw1 n (Class X)

/-- Symmetry passes through the actual original pairing limits. -/
theorem derivativeAction_symmetric (x y : V) :
    B (A x) y = B x (A y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := pairing_limits_eq hw0 hw1
    (quotientRows hw0 hw1 X) (constantRows hw0 hw1 Y)
    (constantRows hw0 hw1 X) (quotientRows hw0 hw1 Y)
    (fun n => by
      rw [quotientRows_pin, constantRows_point, constantRows_point, quotientRows_pin]
      exact quotient_symmetric hw0 hw1 n (Class X) (Class Y))
  rw [limit_constantRows, limit_constantRows] at h
  rw [derivativeAction_pin, derivativeAction_pin]
  exact h

/-- Symmetry implies additivity without identifying the derivative with F. -/
theorem derivativeAction_add (x y : V) :
    A (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (A x) (A y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [derivativeAction_symmetric, completedInner_add_left,
    completedInner_add_left, derivativeAction_symmetric,
    derivativeAction_symmetric]

/-- Rational homogeneity of the represented dyadic derivative limit. -/
theorem derivativeAction_smul (c : Q') (x : V) :
    A (completedSmul hw0 hw1 c x) = completedSmul hw0 hw1 c (A x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [derivativeAction_symmetric, completedInner_smul_left,
    completedInner_smul_left, derivativeAction_symmetric]

#print axioms quotient_symmetric
#print axioms quotient_norm_bound
#print axioms derivativeAction_norm_bound
#print axioms derivativeAction_symmetric
#print axioms derivativeAction_add
#print axioms derivativeAction_smul

end YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws
