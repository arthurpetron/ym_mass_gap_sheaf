/-
# Inverting a supplied represented special-unitary matrix

The input consists of actual CReal-complex matrix entries, explicit inner
regularity for the four first-row components, and the actual RC equations
M M† = I and det M = 1. The second-row quaternion pattern is DERIVED by
division-free algebra. The first-row norm supplies the checked quaternion
coordinate realization, giving an actual Point and recovery of the WHOLE
input matrix. Uniqueness uses the faithful representation on that same Point.

No representative or modulus is chosen from an arbitrary RC entry. There is
no surjectivity assertion for arbitrary RC matrices without supplied rates,
nor any compactness, Haar, all-group, or physical-gap assertion.
-/

import YMGap.RepTheory.RationalQuaternionCompletedMatrix

namespace YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.RepTheory.RationalQuaternionCoordinateCompletion
open YMGap.RepTheory.RationalQuaternionCompletedMatrix
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem complex_mul_one (z : Complex) : complexMul z complexOne = z := by
  rcases z with ⟨r,i⟩
  refine Quotient.inductionOn₂ r i ?_
  intro R I
  apply Prod.ext
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.var 0*1 + -(.var 1*0)) (.var 0)
        (by decide) (fun | 0 => R.approx n | _ => I.approx n)))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.var 0*0+.var 1*1) (.var 1)
        (by decide) (fun | 0 => R.approx n | _ => I.approx n)))

private theorem complex_one_mul (z : Complex) : complexMul complexOne z = z := by
  rcases z with ⟨r,i⟩
  refine Quotient.inductionOn₂ r i ?_
  intro R I
  apply Prod.ext
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (1*.var 0 + -(0*.var 1)) (.var 0)
        (by decide) (fun | 0 => R.approx n | _ => I.approx n)))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (1*.var 1+0*.var 0) (.var 1)
        (by decide) (fun | 0 => R.approx n | _ => I.approx n)))

private theorem complex_mul_zero (z : Complex) : complexMul z complexZero = complexZero := by
  rcases z with ⟨r,i⟩
  refine Quotient.inductionOn₂ r i ?_
  intro R I
  apply Prod.ext
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.var 0*0 + -(.var 1*0)) (.const 0)
        (by decide) (fun | 0 => R.approx n | _ => I.approx n)))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.var 0*0+.var 1*0) (.const 0)
        (by decide) (fun | 0 => R.approx n | _ => I.approx n)))

private theorem complex_add_zero (z : Complex) : complexAdd z complexZero = z := by
  rcases z with ⟨r,i⟩
  refine Quotient.inductionOn₂ r i ?_
  intro R I
  apply Prod.ext
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (R.approx n)))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (I.approx n)))

private theorem complex_neg_zero : complexNeg complexZero = complexZero := by
  apply Prod.ext <;> exact Quotient.sound (ofQ'_equiv_of_eqv (by decide))

private def rowNorm (a b : Complex) : Complex :=
  complexAdd (complexMul a (complexConj a)) (complexMul b (complexConj b))
private def rowCross (a b c d : Complex) : Complex :=
  complexAdd (complexMul c (complexConj a)) (complexMul d (complexConj b))
private def determinant (a b c d : Complex) : Complex :=
  complexAdd (complexMul a d) (complexNeg (complexMul b c))

/- The following expressions reflect only two finite polynomial identities.
They introduce no abstract complex-algebra law or analytic hypothesis. -/
private abbrev CE := PE × PE
private def ev (n : Nat) : CE := (.var n,.var (n+1))
private def ea (z u : CE) : CE := (z.1+u.1,z.2+u.2)
private def en (z : CE) : CE := (-z.1,-z.2)
private def ec (z : CE) : CE := (z.1,-z.2)
private def em (z u : CE) : CE :=
  (z.1*u.1 + -(z.2*u.2),z.1*u.2+z.2*u.1)
private def eNorm : CE := ea (em (ev 0) (ec (ev 0))) (em (ev 2) (ec (ev 2)))
private def eCross : CE := ea (em (ev 4) (ec (ev 0))) (em (ev 6) (ec (ev 2)))
private def eDet : CE := ea (em (ev 0) (ev 6)) (en (em (ev 2) (ev 4)))

private theorem recovery_identities (a b c d : Complex) :
    complexAdd (complexMul d (rowNorm a b))
        (complexNeg (complexMul b (rowCross a b c d))) =
      complexMul (determinant a b c d) (complexConj a) ∧
    complexAdd (complexMul c (rowNorm a b))
        (complexNeg (complexMul a (rowCross a b c d))) =
      complexNeg (complexMul (determinant a b c d) (complexConj b)) := by
  rcases a with ⟨ar,ai⟩
  rcases b with ⟨br,bi⟩
  rcases c with ⟨cr,ci⟩
  rcases d with ⟨dr,di⟩
  refine Quotient.inductionOn₂ ar ai ?_
  intro AR AI
  refine Quotient.inductionOn₂ br bi ?_
  intro BR BI
  refine Quotient.inductionOn₂ cr ci ?_
  intro CR CI
  refine Quotient.inductionOn₂ dr di ?_
  intro DR DI
  let rho (n : Nat) : Nat → Q' := fun | 0 => AR.approx n | 1 => AI.approx n | 2 => BR.approx n | 3 => BI.approx n | 4 => CR.approx n | 5 => CI.approx n | 6 => DR.approx n | _ => DI.approx n
  constructor
  · apply Prod.ext
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        poly_identity_of_normal_eq (ea (em (ev 6) eNorm) (en (em (ev 2) eCross))).1
          (em eDet (ec (ev 0))).1 (by decide) (rho n)))
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        poly_identity_of_normal_eq (ea (em (ev 6) eNorm) (en (em (ev 2) eCross))).2
          (em eDet (ec (ev 0))).2 (by decide) (rho n)))
  · apply Prod.ext
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        poly_identity_of_normal_eq (ea (em (ev 4) eNorm) (en (em (ev 0) eCross))).1
          (en (em eDet (ec (ev 2)))).1 (by decide) (rho n)))
    · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        poly_identity_of_normal_eq (ea (em (ev 4) eNorm) (en (em (ev 0) eCross))).2
          (en (em eDet (ec (ev 2)))).2 (by decide) (rho n)))

/-- The standard quaternion pattern follows from the ACTUAL matrix equations.
Only the lower-left cross entry is used; no division or chosen row is needed. -/
theorem standard_pattern (A : Matrix)
    (hU : matrixMul A (matrixAdjoint A) = matrixOne)
    (hD : matrixDet A = complexOne) :
    A true false = complexNeg (complexConj (A false true)) ∧
      A true true = complexConj (A false false) := by
  let a := A false false
  let b := A false true
  let c := A true false
  let d := A true true
  have hN : rowNorm a b = complexOne := congrArg (fun B : Matrix => B false false) hU
  have hC : rowCross a b c d = complexZero := congrArg (fun B : Matrix => B true false) hU
  have hdet : determinant a b c d = complexOne := hD
  obtain ⟨hd,hc⟩ := recovery_identities a b c d
  rw [hN,hC,hdet,complex_mul_one,complex_mul_zero,complex_neg_zero,
    complex_add_zero,complex_one_mul] at hd hc
  exact ⟨hc,hd⟩

/-! ## The actual first-row coordinate producer -/

abbrev RepresentedMatrix := Bool → Bool → CReal × CReal

def liftMatrix (M : RepresentedMatrix) : Matrix := fun r c => liftComplex (M r c)

def firstCoordinates (M : RepresentedMatrix) : Fin 4 → CReal
  | ⟨0,_⟩ => (M false false).1
  | ⟨1,_⟩ => (M false false).2
  | ⟨2,_⟩ => (M false true).1
  | ⟨_,_⟩ => (M false true).2

/-- The supplied four rates are retained as data, without extracting a modulus. -/
def firstRegularity (M : RepresentedMatrix)
    (R : ∀ c, InnerRegularity (M false c).1 × InnerRegularity (M false c).2) :
    ∀ j, InnerRegularity (firstCoordinates M j) := by
  intro j
  rcases j with ⟨j,hj⟩
  cases j with
  | zero => exact (R false).1
  | succ j => cases j with
    | zero => exact (R false).2
    | succ j => cases j with
      | zero => exact (R true).1
      | succ j => cases j with
        | zero => exact (R true).2
        | succ j =>
          exact False.elim (Nat.not_lt_of_ge
            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ
              (Nat.succ_le_succ (Nat.zero_le j))))) hj)

private theorem row_norm_real (a b c d : Q') :
    (a*a+b*b)+(c*c+d*d) ≈ (a*a + -(b*(-b)))+(c*c + -(d*(-d))) :=
  poly_identity_of_normal_eq
    ((.var 0*.var 0+.var 1*.var 1)+(.var 2*.var 2+.var 3*.var 3))
    ((.var 0*.var 0 + -(.var 1*(-(.var 1))))+(.var 2*.var 2 + -(.var 3*(-(.var 3)))))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

theorem first_norm (M : RepresentedMatrix)
    (hU : matrixMul (liftMatrix M) (matrixAdjoint (liftMatrix M)) = matrixOne) :
    Equiv (coordinateNorm (firstCoordinates M)) cone := by
  have hN := congrArg (fun B : Matrix => (B false false).1) hU
  have hpin : Quotient.mk crealSetoid (coordinateNorm (firstCoordinates M)) =
      (matrixMul (liftMatrix M) (matrixAdjoint (liftMatrix M)) false false).1 := by
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      row_norm_real ((M false false).1.approx n) ((M false false).2.approx n)
        ((M false true).1.approx n) ((M false true).2.approx n)))
  exact Quotient.exact (Eq.trans hpin hN)

/-- An actual original point-Cauchy row, with the checked coordinate modulus. -/
def preimageRow (M : RepresentedMatrix)
    (R : ∀ c, InnerRegularity (M false c).1 × InnerRegularity (M false c).2)
    (hU : matrixMul (liftMatrix M) (matrixAdjoint (liftMatrix M)) = matrixOne) : CauchyPoint :=
  realizationRow (firstCoordinates M) (firstRegularity M R) (first_norm M hU)

/-- Determinant one is required for matrix recovery, not for this norm-one
first-row construction. No RC representative is selected here. -/
def preimage (M : RepresentedMatrix)
    (R : ∀ c, InnerRegularity (M false c).1 × InnerRegularity (M false c).2)
    (hU : matrixMul (liftMatrix M) (matrixAdjoint (liftMatrix M)) = matrixOne) : Point :=
  Quotient.mk chordSeminorm.completionSetoid (preimageRow M R hU)

theorem preimage_coordinate (M : RepresentedMatrix)
    (R : ∀ c, InnerRegularity (M false c).1 × InnerRegularity (M false c).2)
    (hU : matrixMul (liftMatrix M) (matrixAdjoint (liftMatrix M)) = matrixOne) (j : Fin 4) :
    pointCoordinate j (preimage M R hU) = Quotient.mk crealSetoid (firstCoordinates M j) :=
  pointCoordinate_realization (firstCoordinates M) (firstRegularity M R) (first_norm M hU) j

private theorem rc_neg_neg (r : RC) : r = RCneg (RCneg r) := by
  refine Quotient.inductionOn r ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_symm (Q'.neg_neg_eqv (X.approx n))))

private theorem representation_lower_left (x : Point) :
    representation x true false = complexNeg (complexConj (representation x false true)) := by
  apply Prod.ext
  · rfl
  · exact rc_neg_neg (pointCoordinate 3 x)

/-- Recovery is for the WHOLE supplied matrix, not an assumed standard-pattern input. -/
theorem preimage_recovers (M : RepresentedMatrix)
    (R : ∀ c, InnerRegularity (M false c).1 × InnerRegularity (M false c).2)
    (hU : matrixMul (liftMatrix M) (matrixAdjoint (liftMatrix M)) = matrixOne)
    (hD : matrixDet (liftMatrix M) = complexOne) :
    representation (preimage M R hU) = liftMatrix M := by
  have h00 : representation (preimage M R hU) false false = liftMatrix M false false :=
    Prod.ext (preimage_coordinate M R hU 0) (preimage_coordinate M R hU 1)
  have h01 : representation (preimage M R hU) false true = liftMatrix M false true :=
    Prod.ext (preimage_coordinate M R hU 2) (preimage_coordinate M R hU 3)
  have hp := standard_pattern (liftMatrix M) hU hD
  funext r c
  cases r <;> cases c
  · exact h00
  · exact h01
  · rw [representation_lower_left,h01]
    exact hp.1.symm
  · change complexConj (representation (preimage M R hU) false false) = liftMatrix M true true
    rw [h00]
    exact hp.2.symm

theorem preimage_unique (M : RepresentedMatrix)
    (R : ∀ c, InnerRegularity (M false c).1 × InnerRegularity (M false c).2)
    (hU : matrixMul (liftMatrix M) (matrixAdjoint (liftMatrix M)) = matrixOne)
    (hD : matrixDet (liftMatrix M) = complexOne) (x : Point)
    (hx : representation x = liftMatrix M) : x = preimage M R hU :=
  representation_injective (Eq.trans hx (preimage_recovers M R hU hD).symm)

theorem preimage_change_rates (M : RepresentedMatrix)
    (R S : ∀ c, InnerRegularity (M false c).1 × InnerRegularity (M false c).2)
    (hU hU' : matrixMul (liftMatrix M) (matrixAdjoint (liftMatrix M)) = matrixOne) :
    preimage M R hU = preimage M S hU' :=
  realization_change_rates (firstCoordinates M) (firstRegularity M R) (firstRegularity M S)
    (first_norm M hU) (first_norm M hU')

theorem preimage_congr (M N : RepresentedMatrix)
    (R : ∀ c, InnerRegularity (M false c).1 × InnerRegularity (M false c).2)
    (S : ∀ c, InnerRegularity (N false c).1 × InnerRegularity (N false c).2)
    (hM : matrixMul (liftMatrix M) (matrixAdjoint (liftMatrix M)) = matrixOne)
    (hN : matrixMul (liftMatrix N) (matrixAdjoint (liftMatrix N)) = matrixOne)
    (dM : matrixDet (liftMatrix M) = complexOne) (dN : matrixDet (liftMatrix N) = complexOne)
    (h : liftMatrix M = liftMatrix N) : preimage M R hM = preimage N S hN :=
  representation_injective (Eq.trans (preimage_recovers M R hM dM)
    (Eq.trans h (preimage_recovers N S hN dN).symm))

/-! ## Round trip on supplied rows of the SAME point completion -/

theorem liftMatrix_represented (X : CauchyPoint) :
    liftMatrix (representedMatrix X) = representation (Quotient.mk chordSeminorm.completionSetoid X) := by
  funext r c
  exact (representation_mk X r c).symm

theorem represented_unitary (X : CauchyPoint) :
    matrixMul (liftMatrix (representedMatrix X)) (matrixAdjoint (liftMatrix (representedMatrix X))) = matrixOne := by
  rw [liftMatrix_represented]
  exact representation_unitary_right _

theorem represented_determinant (X : CauchyPoint) : matrixDet (liftMatrix (representedMatrix X)) = complexOne := by
  rw [liftMatrix_represented]
  exact representation_determinant _

theorem preimage_row_roundTrip (X : CauchyPoint) :
    preimage (representedMatrix X) (fun c => representedMatrixRegularity X false c)
      (represented_unitary X) = Quotient.mk chordSeminorm.completionSetoid X := by
  apply representation_injective
  rw [preimage_recovers _ _ _ (represented_determinant X),liftMatrix_represented]

/-- The unused unitary direction follows for the actual lifted input as well. -/
theorem supplied_unitary_left (M : RepresentedMatrix)
    (R : ∀ c, InnerRegularity (M false c).1 × InnerRegularity (M false c).2)
    (hU : matrixMul (liftMatrix M) (matrixAdjoint (liftMatrix M)) = matrixOne)
    (hD : matrixDet (liftMatrix M) = complexOne) :
    matrixMul (matrixAdjoint (liftMatrix M)) (liftMatrix M) = matrixOne := by
  rw [← preimage_recovers M R hU hD]
  exact representation_unitary_left _

/-! ## Rational, central-sign and equatorial regressions -/

theorem preimage_rational (a : UnitNorm) :
    preimage (representedMatrix (chordSeminorm.constant a))
      (fun c => representedMatrixRegularity (chordSeminorm.constant a) false c)
      (represented_unitary (chordSeminorm.constant a)) = embed a :=
  preimage_row_roundTrip (chordSeminorm.constant a)

theorem preimage_one :
    preimage (representedMatrix (chordSeminorm.constant unitOne))
      (fun c => representedMatrixRegularity (chordSeminorm.constant unitOne) false c)
      (represented_unitary (chordSeminorm.constant unitOne)) = completedOne :=
  preimage_rational unitOne

theorem preimage_negative_one :
    preimage (representedMatrix (chordSeminorm.constant unitNegativeOne))
      (fun c => representedMatrixRegularity (chordSeminorm.constant unitNegativeOne) false c)
      (represented_unitary (chordSeminorm.constant unitNegativeOne)) = embed unitNegativeOne :=
  preimage_rational unitNegativeOne

theorem preimage_equatorial :
    preimage (representedMatrix (chordSeminorm.constant equatorialUnit))
      (fun c => representedMatrixRegularity (chordSeminorm.constant equatorialUnit) false c)
      (represented_unitary (chordSeminorm.constant equatorialUnit)) = embed equatorialUnit :=
  preimage_rational equatorialUnit

end YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse

#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.standard_pattern
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.firstRegularity
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.first_norm
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimageRow
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage_coordinate
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage_recovers
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage_unique
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage_change_rates
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage_congr
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.liftMatrix_represented
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.represented_unitary
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.represented_determinant
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage_row_roundTrip
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.supplied_unitary_left
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage_rational
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage_one
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage_negative_one
#print axioms YMGap.RepTheory.RationalQuaternionRepresentedMatrixInverse.preimage_equatorial
