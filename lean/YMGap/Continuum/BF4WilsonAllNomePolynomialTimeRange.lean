/-
# Finite original-time range decomposition of a defect polynomial

For a rational polynomial p in D=I-T, each coefficient contributes its
value at 1 times the input, plus an explicit original T(1)-image. The
preimage is a finite signed inverse sum, never an inverse of T. All
Cauchy representatives are assembled by finite modulus-bearing maps.
-/

import YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
import YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum
import YMGap.Continuum.BF4WilsonAllNomeDistance

namespace YMGap.Continuum.BF4WilsonAllNomePolynomialTimeRange

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
open YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeRange (inverseSum inverseSum_identity)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "N" => completedNeg hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "DP" => defectPower hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

private theorem add_interchange (a b c d : V) :
    A (A a b) (A c d) = A (A a c) (A b d) := by
  rw [completedAdd_assoc,← completedAdd_assoc hw0 hw1 b c d,
    completedAdd_comm hw0 hw1 b c,completedAdd_assoc hw0 hw1 c b d,
    ← completedAdd_assoc]

private theorem add_sub_cancel_right (x y : V) : Sub (A x y) y = x := by
  unfold completedSub
  rw [completedAdd_assoc,completedAdd_comm hw0 hw1 y (N y),
    completedNeg_add,completedAdd_zero]

private theorem sub_add_cancel (x y : V) : A (Sub x y) y = x := by
  unfold completedSub
  rw [completedAdd_assoc,completedNeg_add,completedAdd_zero]

private theorem time_neg (x : V) : T 1 (N x) = N (T 1 x) :=
  completedTime_smul hw0 hw1 1 (-1) x

/-- One coefficient's defect monomial splits into a scalar and an exact
time image of a finite inverse sum. -/
theorem monomial_time_pin (a : Q') (i : Nat) (x : V) :
    S a (DP i x) = A (S a x) (T 1 (N (S a (inverseSum hw0 hw1 i x)))) := by
  have h := congrArg (S a) (inverseSum_identity hw0 hw1 i x)
  rw [completedSmul_add,← completedTime_smul] at h
  rw [completedAdd_comm hw0 hw1 (T 1 (S a (inverseSum hw0 hw1 i x))) (S a (DP i x))] at h
  have hs := congrArg (fun z : V => Sub z (T 1 (S a (inverseSum hw0 hw1 i x)))) h
  dsimp only at hs
  rw [add_sub_cancel_right] at hs
  rw [time_neg]
  exact hs

/-- Signed finite preimage, with each monomial at its actual defect degree. -/
def preimageFrom : Poly → Nat → V → V
  | [], _, _ => Z
  | a::p, i, x => A (N (S a (inverseSum hw0 hw1 i x)))
      (preimageFrom p (i+1) x)

def preimage (p : Poly) (x : V) : V := preimageFrom hw0 hw1 p 0 x

private theorem mass_cons (a : Q') (p : Poly) :
    Q'.eqv (eval (a::p) 1) (a+eval p 1) :=
  Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv _)

/-- The shifted coefficient recursion is the constructive finite proof;
the scalar evaluation remains p(1), independent of that shift. -/
theorem actionFrom_time_pin (p : Poly) (i : Nat) (x : V) :
    actionFrom hw0 hw1 p i x =
      A (S (eval p 1) x) (T 1 (preimageFrom hw0 hw1 p i x)) := by
  induction p generalizing i with
  | nil =>
      change Z = A (S 0 x) (T 1 Z)
      rw [completedSmul_zero,completedTime_zero_element,completedZero_add]
  | cons a p ih =>
      change A (S a (DP i x)) (actionFrom hw0 hw1 p (i+1) x) =
        A (S (eval (a::p) 1) x)
          (T 1 (A (N (S a (inverseSum hw0 hw1 i x)))
            (preimageFrom hw0 hw1 p (i+1) x)))
      rw [monomial_time_pin,ih,completedTime_additive,
        add_interchange,completedAdd_smul]
      exact congrArg (fun z : V => A z
        (A (T 1 (N (S a (inverseSum hw0 hw1 i x))))
          (T 1 (preimageFrom hw0 hw1 p (i+1) x))))
        (completedSmul_congr hw0 hw1 (Q'.eqv_symm (mass_cons a p)) x)

theorem polynomial_time_pin (p : Poly) (x : V) :
    action hw0 hw1 p x =
      A (S (eval p 1) x) (T 1 (preimage hw0 hw1 p x)) :=
  actionFrom_time_pin hw0 hw1 p 0 x

/-- Finite Cauchy data for the signed shifted preimage. -/
def preimageFromRepresentative : Poly → Nat → (D).Cauchy → (D).Cauchy
  | [], _, _ => (D).constant (zero width)
  | a::p, i, X => (addition hw0 hw1).mapCauchy
      ((scalarContinuous hw0 hw1 (-1)).mapCauchy
        ((scalarContinuous hw0 hw1 a).mapCauchy
          (inverseSumRepresentative hw0 hw1 i X)))
      (preimageFromRepresentative p (i+1) X)

theorem preimageFromRepresentative_pin (p : Poly) (i : Nat) (X : (D).Cauchy) :
    Class (preimageFromRepresentative hw0 hw1 p i X) =
      preimageFrom hw0 hw1 p i (Class X) := by
  induction p generalizing i with
  | nil => rfl
  | cons a p ih =>
      change A (N (S a (Class (inverseSumRepresentative hw0 hw1 i X))))
        (Class (preimageFromRepresentative hw0 hw1 p (i+1) X)) =
        A (N (S a (inverseSum hw0 hw1 i (Class X))))
          (preimageFrom hw0 hw1 p (i+1) (Class X))
      rw [inverseSumRepresentative_pin,ih]

def preimageRepresentative (p : Poly) (X : (D).Cauchy) : (D).Cauchy :=
  preimageFromRepresentative hw0 hw1 p 0 X

theorem preimageRepresentative_pin (p : Poly) (X : (D).Cauchy) :
    Class (preimageRepresentative hw0 hw1 p X) =
      preimage hw0 hw1 p (Class X) :=
  preimageFromRepresentative_pin hw0 hw1 p 0 X

/-- Exact squared-distance cost: only the scalar mass p(1) obstructs
membership in the original T(1)-range. -/
theorem polynomial_time_error (p : Poly) (x : V) :
    completedDist hw0 hw1 (T 1 (preimage hw0 hw1 p x))
      (action hw0 hw1 p x) =
      RCscale ((eval p 1)*(eval p 1)) (completedInner hw0 hw1 x x) := by
  rw [completedDist_symm,polynomial_time_pin]
  unfold completedDist
  rw [add_sub_cancel_right,completedInner_smul_left,
    completedInner_smul_right,RCscale_RCscale]

#print axioms monomial_time_pin
#print axioms preimageFrom
#print axioms preimage
#print axioms actionFrom_time_pin
#print axioms polynomial_time_pin
#print axioms preimageFromRepresentative
#print axioms preimageFromRepresentative_pin
#print axioms preimageRepresentative
#print axioms preimageRepresentative_pin
#print axioms polynomial_time_error

end YMGap.Continuum.BF4WilsonAllNomePolynomialTimeRange
