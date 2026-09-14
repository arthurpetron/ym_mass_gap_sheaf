/-
# Polynomial algebra of the SAME original completed two-step transfer

Finite polynomial action is the existing original time/scalar/addition
action on every completed vector. Products compose exactly; constants and
the coordinate polynomial recover scalar action and the original T2.
This is an actual operator algebra, not a supplied diagonal spectral model.
Extension to continuous symbols is not asserted here.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference

theorem smul_comm (a b : Q') (x : Completion) :
    completedSmul a (completedSmul b x)=completedSmul b (completedSmul a x) := by
  rw [completedSmul_mul,completedSmul_mul]
  exact completedSmul_congr (Q'.mul_comm_eqv a b) x

theorem vector_base_add (x y : Completion) (p : QPoly.Poly) (r : Nat) :
    polynomialVector (completedAdd x y) p r=
      completedAdd (polynomialVector x p r) (polynomialVector y p r) := by
  induction p generalizing r with
  | nil => exact (completedZero_add _).symm
  | cons c p ih =>
      simp only [polynomialVector,completedTime_add,completedSmul_add,ih]
      exact add_regroup _ _ _ _

theorem vector_base_smul (c : Q') (x : Completion) (p : QPoly.Poly) (r : Nat) :
    polynomialVector (completedSmul c x) p r=completedSmul c (polynomialVector x p r) := by
  induction p generalizing r with
  | nil => exact (smul_zero_state c).symm
  | cons d p ih =>
      simp only [polynomialVector,completedTime_smul,ih,completedSmul_add]
      rw [smul_comm d c]

theorem vector_base_sub (x y : Completion) (p : QPoly.Poly) (r : Nat) :
    polynomialVector (completedSub x y) p r=
      completedSub (polynomialVector x p r) (polynomialVector y p r) := by
  unfold completedSub completedNeg
  rw [vector_base_add,vector_base_smul]

theorem time_vector (x : Completion) (p : QPoly.Poly) (r k : Nat) :
    completedTime (k+k) (polynomialVector x p r)=polynomialVector x p (r+k) := by
  induction p generalizing r with
  | nil => exact completedTime_zeroState _
  | cons c p ih =>
      rw [polynomialVector,completedTime_add,completedTime_smul,completedTime_comp,ih]
      rw [show (r+r)+(k+k)=(r+k)+(r+k) by omega,show (r+1)+k=(r+k)+1 by omega]
      rfl

theorem vector_zero_cons (x : Completion) (p : QPoly.Poly) (r : Nat) :
    polynomialVector x (0::p) r=polynomialVector x p (r+1) := by
  rw [polynomialVector,completedSmul_zero,completedZero_add]

theorem vector_product (x : Completion) (p q : QPoly.Poly) (r s : Nat) :
    polynomialVector (polynomialVector x q s) p r=polynomialVector x (QPoly.pmul p q) (r+s) := by
  induction p generalizing r with
  | nil => rfl
  | cons c p ih =>
      rw [polynomialVector,time_vector,ih,QPoly.pmul,vector_add,vector_scale,vector_zero_cons]
      rw [show s+r=r+s by omega,show (r+1)+s=(r+s)+1 by omega]

theorem vector_symmetric (x y : Completion) (p : QPoly.Poly) (r : Nat) :
    completedInner (polynomialVector x p r) y=completedInner x (polynomialVector y p r) := by
  induction p generalizing r with
  | nil => simp only [polynomialVector,completedInner_zero_left,completedInner_zero_right]
  | cons c p ih =>
      rw [polynomialVector,polynomialVector,completedInner_add_left,completedInner_add_right,
        completedInner_smul_left,completedInner_smul_right,completedTime_symmetric,ih]

def polynomialOperator (p : QPoly.Poly) (x : Completion) : Completion := polynomialVector x p 0

theorem operator_add (p q : QPoly.Poly) (x : Completion) :
    polynomialOperator (QPoly.padd p q) x=completedAdd (polynomialOperator p x) (polynomialOperator q x) :=
  vector_add x p q 0

theorem operator_scale (c : Q') (p : QPoly.Poly) (x : Completion) :
    polynomialOperator (QPoly.pscale c p) x=completedSmul c (polynomialOperator p x) := vector_scale x c p 0

theorem operator_mul (p q : QPoly.Poly) (x : Completion) :
    polynomialOperator (QPoly.pmul p q) x=polynomialOperator p (polynomialOperator q x) :=
  (vector_product x p q 0 0).symm

theorem operator_constant (c : Q') (x : Completion) : polynomialOperator [c] x=completedSmul c x := by
  unfold polynomialOperator
  rw [polynomialVector,polynomialVector,completedTime_zero,completedAdd_zero]

theorem operator_one (x : Completion) : polynomialOperator [1] x=x :=
  (operator_constant 1 x).trans (completedSmul_one x)

theorem operator_coordinate (x : Completion) : polynomialOperator [0,1] x=twoStepTransfer x := by
  unfold polynomialOperator
  rw [vector_zero_cons,polynomialVector,polynomialVector,completedSmul_one,completedAdd_zero]
  rfl

theorem operator_symmetric (p : QPoly.Poly) (x y : Completion) :
    completedInner (polynomialOperator p x) y=completedInner x (polynomialOperator p y) := vector_symmetric x y p 0

end YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.smul_comm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.vector_base_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.vector_base_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.vector_base_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.time_vector
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.vector_zero_cons
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.vector_product
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.vector_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.polynomialOperator
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.operator_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.operator_scale
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.operator_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.operator_constant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.operator_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.operator_coordinate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator.operator_symmetric
