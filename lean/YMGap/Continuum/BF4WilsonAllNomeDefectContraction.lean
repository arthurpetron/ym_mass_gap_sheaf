/-
# Contraction of powers of the actual Wilson time defect

On the original all-nome completion, powers of D=I-T preserve subtraction
and contract the original squared distance.  The proof uses the existing
mixed-moment estimate for D^n, not a spectral representation or a different
carrier.  States in ker(T) are fixed by every defect power.
-/

import YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
import YMGap.Continuum.BF4WilsonAllNomeDistance
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit

namespace YMGap.Continuum.BF4WilsonAllNomeDefectContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit (completedSub_zero)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "DP" => defectPower hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "dist" => completedDist hw0 hw1

/-- Powers of the actual defect preserve subtraction on the original carrier. -/
theorem defectPower_sub (n : Nat) (x y : V) :
    DP n (Sub x y) = Sub (DP n x) (DP n y) := by
  unfold completedSub completedNeg
  rw [defectPower_additive, defectPower_smul]

/-- Every natural power of the actual defect contracts the original squared
distance on the literal Wilson completion. -/
theorem defectPower_distance_contraction (n : Nat) (x y : V) :
    RCle (dist (DP n x) (DP n y)) (dist x y) := by
  unfold completedDist
  rw [← defectPower_sub hw0 hw1 n x y]
  exact defect_pair_bound hw0 hw1 (Sub x y) n n

/-- Defect powers preserve the original zero vector. -/
theorem defectPower_zero (n : Nat) : DP n Z = Z :=
  BF4WilsonAllNomeDefectPolynomialAlgebra.defectPower_zero hw0 hw1 n

/-- On the actual time kernel, D=I-T acts as the identity, hence so do all
natural powers. -/
theorem defectPower_time_kernel (n : Nat) (x : V) (hx : T 1 x = Z) :
    DP n x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change defect hw0 hw1 (DP n x) = x
      rw [ih, defect, hx, completedSub_zero]

#print axioms defectPower_sub
#print axioms defectPower_distance_contraction
#print axioms defectPower_zero
#print axioms defectPower_time_kernel

end YMGap.Continuum.BF4WilsonAllNomeDefectContraction
