/-
# Finite inverse-sum algebra for the original Wilson derivative graph

All identities below use the actual original one-step time map and its
constructed dyadic derivative. The finite inverse sum is a polynomial, not
an inverse of time. No range-closure or tail conclusion is asserted here.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeCore
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeRange
import YMGap.Continuum.BF4WilsonAllNomeLogSeries

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeDerivativeCore
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws (derivativeAction_add)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeRange
open YMGap.Continuum.BF4WilsonAllNomeLogSeries (defectPowerCauchy defectPowerCauchy_pin)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "Add" => completedAdd hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "DP" => defectPower hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- The constructed derivative commutes with the original one-step defect. -/
theorem derivativeAction_defect (x : V) :
    A (defect hw0 hw1 x) = defect hw0 hw1 (A x) := by
  unfold defect
  rw [derivativeAction_sub,derivativeAction_commutes_time]

theorem derivativeAction_defectPower (n : Nat) (x : V) :
    A (DP n x) = DP n (A x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change A (defect hw0 hw1 (DP n x)) =
        defect hw0 hw1 (DP n (A x))
      rw [derivativeAction_defect,ih]

/-- The finite inverse sum commutes with the constructed derivative. -/
theorem derivativeAction_inverseSum (n : Nat) (x : V) :
    A (inverseSum hw0 hw1 n x) = inverseSum hw0 hw1 n (A x) := by
  induction n with
  | zero =>
      change A Z = Z
      exact derivativeAction_zero hw0 hw1
  | succ n ih =>
      change A (Add (inverseSum hw0 hw1 n x) (DP n x)) =
        Add (inverseSum hw0 hw1 n (A x)) (DP n (A x))
      rw [derivativeAction_add,ih,derivativeAction_defectPower]

theorem time_inverseSum (n : Nat) (x : V) :
    T 1 (inverseSum hw0 hw1 n x) = inverseSum hw0 hw1 n (T 1 x) := by
  induction n with
  | zero =>
      change T 1 Z = Z
      exact completedTime_zero_element hw0 hw1 1
  | succ n ih =>
      change T 1 (Add (inverseSum hw0 hw1 n x) (DP n x)) =
        Add (inverseSum hw0 hw1 n (T 1 x)) (DP n (T 1 x))
      rw [completedTime_additive,ih,time_defectPower]

private theorem add_sub_cancel (x y : V) : Sub (Add x y) y = x := by
  unfold completedSub
  rw [completedAdd_assoc,completedAdd_comm hw0 hw1 y (completedNeg hw0 hw1 y),
    completedNeg_add,completedAdd_zero]

/-- The finite inverse-sum telescope with its exact defect remainder. -/
theorem time_inverseSum_sub (n : Nat) (x : V) :
    T 1 (inverseSum hw0 hw1 n x) = Sub x (DP n x) := by
  have h := congrArg (fun z : V => Sub z (DP n x))
    (inverseSum_identity hw0 hw1 n x)
  dsimp only at h
  rw [add_sub_cancel] at h
  exact h

theorem inverseSum_time_sub (n : Nat) (x : V) :
    inverseSum hw0 hw1 n (T 1 x) = Sub x (DP n x) := by
  rw [← time_inverseSum]
  exact time_inverseSum_sub hw0 hw1 n x

/-- The desired finite graph row under the SAME original graph equation. -/
theorem derivativeAction_inverseSum_of_equation (n : Nat) (u v : V)
    (h : A u = T 1 v) :
    A (inverseSum hw0 hw1 n u) = Sub v (DP n v) := by
  rw [derivativeAction_inverseSum,h]
  exact inverseSum_time_sub hw0 hw1 n v

/-- A supplied original Cauchy input has a concrete finite inverse-sum
representative. Its modulus is assembled from existing finite operations. -/
def inverseSumRepresentative : Nat → (D).Cauchy → (D).Cauchy
  | 0, _ => (D).constant (zero width)
  | n+1, X => (addition hw0 hw1).mapCauchy
      (inverseSumRepresentative n X) (defectPowerCauchy hw0 hw1 n X)

theorem inverseSumRepresentative_pin (n : Nat) (X : (D).Cauchy) :
    Class (inverseSumRepresentative hw0 hw1 n X) =
      inverseSum hw0 hw1 n (Class X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Add (Class (inverseSumRepresentative hw0 hw1 n X))
        (Class (defectPowerCauchy hw0 hw1 n X)) =
        Add (inverseSum hw0 hw1 n (Class X)) (DP n (Class X))
      rw [ih,defectPowerCauchy_pin]

#print axioms derivativeAction_defect
#print axioms derivativeAction_defectPower
#print axioms derivativeAction_inverseSum
#print axioms time_inverseSum
#print axioms time_inverseSum_sub
#print axioms inverseSum_time_sub
#print axioms derivativeAction_inverseSum_of_equation
#print axioms inverseSumRepresentative
#print axioms inverseSumRepresentative_pin

end YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum
