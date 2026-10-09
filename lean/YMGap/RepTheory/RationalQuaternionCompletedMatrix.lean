/-
# The faithful fundamental matrix of the existing quaternion Point

The carrier is exactly RationalQuaternionCauchyGroup.Point. Its four checked
RC coordinates form the usual two-by-two complex matrix. Multiplication and
adjoint are pinned to the original pointwise Hamilton operations through the
existing rational fundamental-matrix identities. The map is faithful, has
determinant one, and satisfies both unitary identities.

Supplied Cauchy rows give explicit represented matrix entries and their
regularity. No representative of an arbitrary quotient point is chosen.
This leaf does not assert compactness, a Haar extension, surjectivity onto
all RC matrices, an interacting estimate, or an every-group realization.
-/

import YMGap.RepTheory.RationalQuaternionCoordinateCompletion
import YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
import YMGap.Continuum.FCLimitContinuity

namespace YMGap.RepTheory.RationalQuaternionCompletedMatrix

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.RepTheory.RationalQuaternionCoordinateCompletion
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Complex values use the existing real quotient, not chosen real rows. -/
abbrev Complex := RC × RC
abbrev Matrix := Bool → Bool → Complex

def complexAdd (z u : Complex) : Complex := (RCadd z.1 u.1, RCadd z.2 u.2)
def complexNeg (z : Complex) : Complex := (RCneg z.1, RCneg z.2)
def complexMul (z u : Complex) : Complex :=
  (RCadd (RCmul z.1 u.1) (RCneg (RCmul z.2 u.2)),
    RCadd (RCmul z.1 u.2) (RCmul z.2 u.1))
def complexConj (z : Complex) : Complex := (z.1,RCneg z.2)
def liftComplex (z : CReal × CReal) : Complex :=
  (Quotient.mk crealSetoid z.1,Quotient.mk crealSetoid z.2)
def rationalComplex (z : RationalComplex) : Complex :=
  liftComplex (ofQ' z.1,ofQ' z.2)
def complexZero : Complex := rationalComplex (0,0)
def complexOne : Complex := rationalComplex (1,0)

def matrixMul (A B : Matrix) : Matrix := fun r c =>
  complexAdd (complexMul (A r false) (B false c)) (complexMul (A r true) (B true c))
def matrixAdjoint (A : Matrix) : Matrix := fun r c => complexConj (A c r)
def matrixDet (A : Matrix) : Complex :=
  complexAdd (complexMul (A false false) (A true true))
    (complexNeg (complexMul (A false true) (A true false)))
def matrixOne : Matrix
  | false,false => complexOne
  | false,true => complexZero
  | true,false => complexZero
  | true,true => complexOne

/-- The standard fundamental matrix on the SAME completed point group. -/
def representation (x : Point) : Matrix
  | false,false => (pointCoordinate 0 x,pointCoordinate 1 x)
  | false,true => (pointCoordinate 2 x,pointCoordinate 3 x)
  | true,false => (RCneg (pointCoordinate 2 x),pointCoordinate 3 x)
  | true,true => (pointCoordinate 0 x,RCneg (pointCoordinate 1 x))

/-- Matrix representatives are constructed only from a SUPPLIED original row. -/
def representedMatrix (X : CauchyPoint) : Bool → Bool → CReal × CReal
  | false,false => (rowCoordinate X 0,rowCoordinate X 1)
  | false,true => (rowCoordinate X 2,rowCoordinate X 3)
  | true,false => (CReal.neg (rowCoordinate X 2),rowCoordinate X 3)
  | true,true => (rowCoordinate X 0,CReal.neg (rowCoordinate X 1))

def representedMatrixRegularity (X : CauchyPoint) (r c : Bool) :
    InnerRegularity (representedMatrix X r c).1 × InnerRegularity (representedMatrix X r c).2 := by
  cases r <;> cases c
  · exact ⟨rowCoordinateRegularity X 0,rowCoordinateRegularity X 1⟩
  · exact ⟨rowCoordinateRegularity X 2,rowCoordinateRegularity X 3⟩
  · exact ⟨(rowCoordinateRegularity X 2).neg,rowCoordinateRegularity X 3⟩
  · exact ⟨rowCoordinateRegularity X 0,(rowCoordinateRegularity X 1).neg⟩

theorem representedMatrix_approx (X : CauchyPoint) (n : Nat) (r c : Bool) :
    ((representedMatrix X r c).1.approx n,(representedMatrix X r c).2.approx n) =
      fundamentalMatrixValue (X.seq n).val r c := by
  cases r <;> cases c <;> rfl

theorem representation_mk (X : CauchyPoint) (r c : Bool) :
    representation (Quotient.mk chordSeminorm.completionSetoid X) r c =
      liftComplex (representedMatrix X r c) := by
  cases r <;> cases c <;> rfl

/-- Literal rational fundamental entries, without a new matrix convention. -/
theorem rational_entry_pin (a : UnitNorm) (r c : Bool) :
    representation (embed a) r c = rationalComplex (fundamentalMatrixValue a.val r c) := by
  cases r <;> cases c <;> rfl

theorem rational_matrix_pin (a : UnitNorm) :
    representation (embed a) = fun r c => rationalComplex (fundamentalMatrixValue a.val r c) := by
  funext r c
  exact rational_entry_pin a r c

/-- The completed law is the checked raw Hamilton/fundamental law on each row. -/
theorem representation_mul (x y : Point) :
    representation (completedMul x y) = matrixMul (representation x) (representation y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  funext r c
  have h (n : Nat) := fundamentalMatrixValue_mul (X.seq n).val (Y.seq n).val
  cases r <;> cases c
  · apply Prod.ext
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n false false).1))
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n false false).2))
  · apply Prod.ext
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n false true).1))
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n false true).2))
  · apply Prod.ext
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n true false).1))
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n true false).2))
  · apply Prod.ext
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n true true).1))
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n true true).2))

theorem representation_one : representation completedOne = matrixOne := by
  funext r c
  cases r <;> cases c <;> apply Prod.ext <;>
    exact Quotient.sound (ofQ'_equiv_of_eqv (by decide))

/-- Completed inversion is the actual matrix adjoint. -/
theorem representation_inv (x : Point) :
    representation (completedInv x) = matrixAdjoint (representation x) := by
  refine Quotient.inductionOn x ?_
  intro X
  funext r c
  have h (n : Nat) := fundamentalMatrixValue_conj (X.seq n).val
  cases r <;> cases c
  · apply Prod.ext
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n false false).1))
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n false false).2))
  · apply Prod.ext
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n false true).1))
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n false true).2))
  · apply Prod.ext
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n true false).1))
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n true false).2))
  · apply Prod.ext
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n true true).1))
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => (h n true true).2))

theorem representation_unitary_left (x : Point) :
    matrixMul (matrixAdjoint (representation x)) (representation x) = matrixOne := by
  rw [← representation_inv,← representation_mul,completedInv_mul,representation_one]

theorem representation_unitary_right (x : Point) :
    matrixMul (representation x) (matrixAdjoint (representation x)) = matrixOne := by
  rw [← representation_inv,← representation_mul,completedMul_inv,representation_one]

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem determinant_real (a : RationalQuaternion) :
    (a.r*a.r + -(a.i*(-a.i))) + -(a.j*(-a.j) + -(a.k*a.k)) ≈ normSq a :=
  poly_identity_of_normal_eq
    ((.var 0*.var 0 + -(.var 1*(-(.var 1)))) + -(.var 2*(-(.var 2)) + -(.var 3*.var 3)))
    ((.var 0*.var 0+.var 1*.var 1)+(.var 2*.var 2+.var 3*.var 3))
    (by decide) (fun | 0 => a.r | 1 => a.i | 2 => a.j | _ => a.k)

private theorem determinant_imag (a : RationalQuaternion) :
    (a.r*(-a.i)+a.i*a.r) + -(a.j*a.k+a.k*(-a.j)) ≈ (0:Q') :=
  poly_identity_of_normal_eq
    ((.var 0*(-(.var 1))+.var 1*.var 0) + -(.var 2*.var 3+.var 3*(-(.var 2))))
    (.const 0) (by decide) (fun | 0 => a.r | 1 => a.i | 2 => a.j | _ => a.k)

theorem representation_determinant (x : Point) : matrixDet (representation x) = complexOne := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Prod.ext
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.eqv_trans _ _ _ (determinant_real (X.seq n).val) (X.seq n).unitNorm))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => determinant_imag (X.seq n).val))

/-- All four coordinates occur in the top row, so no point is identified. -/
theorem representation_injective {x y : Point} (h : representation x = representation y) : x = y := by
  apply pointCoordinate_injective
  intro j
  rcases j with ⟨j,hj⟩
  cases j with
  | zero => exact congrArg (fun A : Matrix => (A false false).1) h
  | succ j => cases j with
    | zero => exact congrArg (fun A : Matrix => (A false false).2) h
    | succ j => cases j with
      | zero => exact congrArg (fun A : Matrix => (A false true).1) h
      | succ j => cases j with
        | zero => exact congrArg (fun A : Matrix => (A false true).2) h
        | succ j =>
          exact False.elim (Nat.not_lt_of_ge
            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ
              (Nat.succ_le_succ (Nat.zero_le j))))) hj)

theorem representation_eq_iff (x y : Point) : representation x = representation y ↔ x = y :=
  ⟨representation_injective,fun h => congrArg representation h⟩

/-! ## Both central signs and an equatorial rational point -/

def matrixNegativeOne : Matrix
  | false,false => rationalComplex (-1,0)
  | false,true => complexZero
  | true,false => complexZero
  | true,true => rationalComplex (-1,0)

theorem representation_negative_one : representation (embed unitNegativeOne) = matrixNegativeOne := by
  funext r c
  rw [rational_entry_pin]
  cases r <;> cases c <;> apply Prod.ext <;>
    exact Quotient.sound (ofQ'_equiv_of_eqv (by decide))

theorem representation_central_signs_distinct :
    representation (embed unitOne) ≠ representation (embed unitNegativeOne) := by
  intro h
  have hp := representation_injective h
  have he := (embed_eq_iff unitOne unitNegativeOne).mp hp
  have hn : ¬ unitOne.Equivalent unitNegativeOne := by
    unfold UnitNorm.Equivalent RationalQuaternion.Equivalent
    decide
  exact hn he

def equatorialUnit : UnitNorm := ⟨RationalQuaternion.basisI,by
  unfold RationalQuaternion.IsUnitNorm
  decide⟩
def equatorialMatrix : Matrix
  | false,false => rationalComplex (0,1)
  | false,true => complexZero
  | true,false => complexZero
  | true,true => rationalComplex (0,-1)

theorem representation_equatorial : representation (embed equatorialUnit) = equatorialMatrix := by
  funext r c
  rw [rational_entry_pin]
  cases r <;> cases c <;> apply Prod.ext <;>
    exact Quotient.sound (ofQ'_equiv_of_eqv (by decide))

theorem equatorial_square :
    matrixMul equatorialMatrix equatorialMatrix = matrixNegativeOne := by
  rw [← representation_equatorial,← representation_mul,← embed_mul]
  have h : (UnitNorm.mul equatorialUnit equatorialUnit).Equivalent unitNegativeOne := by
    unfold UnitNorm.Equivalent RationalQuaternion.Equivalent
    decide
  rw [(embed_eq_iff _ _).mpr h]
  exact representation_negative_one

end YMGap.RepTheory.RationalQuaternionCompletedMatrix

#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representedMatrixRegularity
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representedMatrix_approx
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_mk
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.rational_entry_pin
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.rational_matrix_pin
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_mul
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_one
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_inv
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_unitary_left
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_unitary_right
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_determinant
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_injective
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_eq_iff
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_negative_one
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_central_signs_distinct
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.equatorialUnit
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.representation_equatorial
#print axioms YMGap.RepTheory.RationalQuaternionCompletedMatrix.equatorial_square
