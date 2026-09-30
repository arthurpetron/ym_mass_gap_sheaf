/-
# A positive square root of the ORIGINAL completed Wilson transfer

The represented complement limit H satisfies the finite recursion in
pairings. For R=I-H this gives B(Rx,Ry)=B(x,Ty), hence R^2=T by symmetry
and definiteness. No inverse, lower spectral endpoint or limit of chosen
quotient representatives is needed. The original time kernel is retained.

This constructs an algebraic positive square root on the existing carrier.
Dyadic compatibility, strong continuity, the regularized-log generator
identity, spacing calibration and all continuum/Clay claims remain separate.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootIteration
import YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
import YMGap.Continuum.BF4WilsonAllNomeLogOperator

namespace YMGap.Continuum.BF4WilsonAllNomeSquareRoot

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeLogOperator (pairing_limits_eq)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect defectPower)
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
open YMGap.Continuum.BF4WilsonAllNomeRootIteration
open YMGap.Continuum.ComplementRootPolynomial

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "H" => complementLimit hw0 hw1
local notation "P" => approximant hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Symmetry passes through the existing represented pairing limits. -/
theorem complementLimit_symmetric (x y : V) : B (H x) y = B x (H y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := pairing_limits_eq hw0 hw1 (iterationRows hw0 hw1 X) (constantRows hw0 hw1 Y)
    (constantRows hw0 hw1 X) (iterationRows hw0 hw1 Y) (fun n => by
      rw [iterationRows_point, constantRows_point, constantRows_point, iterationRows_point]
      exact action_symmetric hw0 hw1 (polynomial n) (Class X) (Class Y))
  rw [limit_constantRows, limit_constantRows] at h
  exact h

/-- The computed complement form is bounded above by the ORIGINAL norm. -/
theorem complementLimit_form_le (x : V) : RCle (B x (H x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let R := constantRows hw0 hw1 X
  let S := iterationRows hw0 hw1 X
  let n := pairingModulus hw0 hw1 R S epsilon
  have h := (row_pairing_bound hw0 hw1 R S epsilon he n (Nat.le_refl n)).2
  change RCle (B (limit hw0 hw1 (constantRows hw0 hw1 X))
    (limit hw0 hw1 (iterationRows hw0 hw1 X)))
    (RCadd (B (rowPoint hw0 hw1 (constantRows hw0 hw1 X) n)
      (rowPoint hw0 hw1 (iterationRows hw0 hw1 X) n)) (rat epsilon)) at h
  rw [constantRows_point, iterationRows_point, limit_constantRows] at h
  have hp := actionFrom_defect_pair_bound hw0 hw1 (polynomial n)
    (polynomial_coeffNonnegative n) (Class X) 0 0
  change RCle (B (P n (Class X)) (Class X)) _ at hp
  rw [completedInner_symm hw0 hw1 (P n (Class X)) (Class X),
    RCSignedPairBudget.scale_congr (eval_polynomial_one n)] at hp
  have hle := RCle_trans hp (RCscale_scalar_mono
    (ComplementRootMass.mass_le_one n) (completedInner_nonnegative hw0 hw1 (Class X)))
  rw [RCscale_one] at hle
  exact RCle_trans h (RCadd_le_add hle (RCle_refl _))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (X.approx n)))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (X.approx n))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (X.approx n)))

private theorem rc_sub_nonnegative {a b : RC} (h : RCle b a) : RCnonneg (RCsub a b) := by
  have hs := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at hs
  rwa [rc_sub_self] at hs

private theorem double_half_sub (a b : RC) :
    RCsub (RCadd (RCscale HalfPow.half (RCadd a b))
      (RCscale HalfPow.half (RCadd a b))) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (ExpNeg.two_halves (X.approx n + Y.approx n)))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
        (by decide) (fun | 0 => X.approx n | _ => Y.approx n))))

/-- The full finite recurrence is tested against arbitrary ORIGINAL inputs. -/
theorem approximant_pairing_recurrence (n : Nat) (x y : V) :
    B (P n x) (P n y) =
      RCsub (RCadd (B x (P (n+1) y)) (B x (P (n+1) y))) (B x (defect hw0 hw1 y)) := by
  have hvar : action hw0 hw1 [0,1] y = defect hw0 hw1 y := by
    change completedAdd hw0 hw1 (completedSmul hw0 hw1 0 y)
      (completedAdd hw0 hw1 (completedSmul hw0 hw1 1 (defect hw0 hw1 y))
        (completedZero hw0 hw1 width)) = _
    rw [completedSmul_zero, completedSmul_one, completedAdd_zero, completedZero_add]
  have hrec : P (n+1) y = completedSmul hw0 hw1 HalfPow.half
      (completedAdd hw0 hw1 (defect hw0 hw1 y) (P n (P n y))) := by
    change actionFrom hw0 hw1 (pscale HalfPow.half
      (padd [0,1] (pmul (polynomial n) (polynomial n)))) 0 y = _
    rw [actionFrom_pscale, actionFrom_padd]
    change completedSmul hw0 hw1 HalfPow.half
      (completedAdd hw0 hw1 (action hw0 hw1 [0,1] y)
        (action hw0 hw1 (pmul (polynomial n) (polynomial n)) y)) = _
    rw [hvar, action_pmul]
    rfl
  rw [hrec, completedInner_smul_right, completedInner_add_right]
  rw [double_half_sub]
  exact action_symmetric hw0 hw1 (polynomial n) x (P n y)

private theorem double_error_identity (b d : RC) (e : Q') :
    RCsub (RCadd (RCadd b (rat (HalfPow.half*(HalfPow.half*e))))
      (RCadd b (rat (HalfPow.half*(HalfPow.half*e))))) d =
      RCadd (RCsub (RCadd b b) d) (rat (HalfPow.half*e)) := by
  refine Quotient.inductionOn₂ b d ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 2)) (.add (.var 0) (.var 2))) (.neg (.var 1)))
      (.add (.add (.add (.var 0) (.var 0)) (.neg (.var 1)))
        (.add (.var 2) (.var 2))) (by decide)
      (fun | 0 => X.approx n | 1 => Y.approx n | _ => HalfPow.half*(HalfPow.half*e)))
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves (HalfPow.half*e)))))

private theorem double_sub_error {a b : RC} (d : RC) (e : Q')
    (h : RCle a (RCadd b (rat (HalfPow.half*(HalfPow.half*e))))) :
    RCle (RCsub (RCadd a a) d)
      (RCadd (RCsub (RCadd b b) d) (rat (HalfPow.half*e))) := by
  have hh := RCadd_le_add (RCadd_le_add h h) (RCle_refl (RCneg d))
  change RCle (RCsub (RCadd a a) d)
    (RCsub (RCadd (RCadd b (rat (HalfPow.half*(HalfPow.half*e))))
      (RCadd b (rat (HalfPow.half*(HalfPow.half*e))))) d) at hh
  rwa [double_error_identity] at hh

private theorem two_errors (a : RC) (e : Q') :
    RCadd (RCadd a (rat (HalfPow.half*e))) (rat (HalfPow.half*e)) = RCadd a (rat e) := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves e))))

private theorem scalar_recurrence_errors (a an c cn d : RC) (e : Q')
    (hA : RCle an (RCadd a (rat (HalfPow.half*e))) ∧
      RCle a (RCadd an (rat (HalfPow.half*e))))
    (hC : RCle cn (RCadd c (rat (HalfPow.half*(HalfPow.half*e)))) ∧
      RCle c (RCadd cn (rat (HalfPow.half*(HalfPow.half*e)))))
    (hrec : an = RCsub (RCadd cn cn) d) :
    RCle a (RCadd (RCsub (RCadd c c) d) (rat e)) ∧
      RCle (RCsub (RCadd c c) d) (RCadd a (rat e)) := by
  have ha := double_sub_error d e hC.1
  have hb := double_sub_error d e hC.2
  rw [← hrec] at ha hb
  constructor
  · have hu := RCle_trans hA.2 (RCadd_le_add ha (RCle_refl (rat (HalfPow.half*e))))
    rwa [two_errors] at hu
  · have hl := RCle_trans hb (RCadd_le_add hA.1 (RCle_refl (rat (HalfPow.half*e))))
    rwa [two_errors] at hl

private theorem recurrence_errors (x y : V) (e : Q') (he : (0 : Q') < e) :
    let rhs := RCsub (RCadd (B x (H y)) (B x (H y))) (B x (defect hw0 hw1 y))
    RCle (B (H x) (H y)) (RCadd rhs (rat e)) ∧
      RCle rhs (RCadd (B (H x) (H y)) (rat e)) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  let A := iterationRows hw0 hw1 X
  let C := iterationRows hw0 hw1 Y
  let K := constantRows hw0 hw1 X
  let h := HalfPow.half*e
  let q := HalfPow.half*h
  have hh : (0 : Q') < h := ExpNeg.half_mul_pos e he
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos h hh
  let n := max (pairingModulus hw0 hw1 A C h) (pairingModulus hw0 hw1 K C q)
  have hAC := row_pairing_bound hw0 hw1 A C h hh n (Nat.le_max_left _ _)
  have hKC := row_pairing_bound hw0 hw1 K C q hq (n+1)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ n))
  change (RCle (B (rowPoint hw0 hw1 (iterationRows hw0 hw1 X) n)
    (rowPoint hw0 hw1 (iterationRows hw0 hw1 Y) n))
      (RCadd (B (H (Class X)) (H (Class Y))) (rat h)) ∧
    RCle (B (H (Class X)) (H (Class Y)))
      (RCadd (B (rowPoint hw0 hw1 (iterationRows hw0 hw1 X) n)
        (rowPoint hw0 hw1 (iterationRows hw0 hw1 Y) n)) (rat h))) at hAC
  change (RCle (B (rowPoint hw0 hw1 (constantRows hw0 hw1 X) (n+1))
    (rowPoint hw0 hw1 (iterationRows hw0 hw1 Y) (n+1)))
      (RCadd (B (limit hw0 hw1 (constantRows hw0 hw1 X)) (H (Class Y))) (rat q)) ∧
    RCle (B (limit hw0 hw1 (constantRows hw0 hw1 X)) (H (Class Y)))
      (RCadd (B (rowPoint hw0 hw1 (constantRows hw0 hw1 X) (n+1))
        (rowPoint hw0 hw1 (iterationRows hw0 hw1 Y) (n+1))) (rat q))) at hKC
  rw [iterationRows_point, iterationRows_point] at hAC
  rw [constantRows_point, iterationRows_point, limit_constantRows] at hKC
  exact scalar_recurrence_errors _ _ _ _ _ e hAC hKC
    (approximant_pairing_recurrence hw0 hw1 n (Class X) (Class Y))

/-- The original recurrence survives in pairings; no composition-limit
continuity or representative choice is assumed. -/
theorem complementLimit_pairing_recurrence (x y : V) :
    B (H x) (H y) =
      RCsub (RCadd (B x (H y)) (B x (H y))) (B x (defect hw0 hw1 y)) :=
  RCle_antisymm
    (RationalScalarTwoSidedError.le_of_all_errors _ _ (fun e he =>
      (recurrence_errors hw0 hw1 x y e he).1))
    (RationalScalarTwoSidedError.le_of_all_errors _ _ (fun e he =>
      (recurrence_errors hw0 hw1 x y e he).2))

/-- Constructed from the existing witnessed complement limit, not supplied. -/
def squareRoot (x : V) : V := completedSub hw0 hw1 x (H x)

theorem squareRoot_symmetric (x y : V) :
    B (squareRoot hw0 hw1 x) y = B x (squareRoot hw0 hw1 y) := by
  unfold squareRoot
  rw [completedInner_sub_left, completedInner_sub_right, complementLimit_symmetric]

theorem squareRoot_nonnegative (x : V) : RCnonneg (B x (squareRoot hw0 hw1 x)) := by
  rw [squareRoot, completedInner_sub_right]
  exact rc_sub_nonnegative (complementLimit_form_le hw0 hw1 x)

private theorem square_pairing_cancel (a b c : RC) :
    RCsub (RCsub a b) (RCsub b (RCsub (RCadd b b) (RCsub a c))) = c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro X Y Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg
          (.add (.add (.var 1) (.var 1)) (.neg (.add (.var 0) (.neg (.var 2)))))))))
      (.var 2) (by decide) (fun | 0 => X.approx n | 1 => Y.approx n | _ => Z.approx n)))

/-- The square-root pairing is pinned to the SAME one-step transfer. -/
theorem squareRoot_pairing (x y : V) :
    B (squareRoot hw0 hw1 x) (squareRoot hw0 hw1 y) = B x (T 1 y) := by
  unfold squareRoot
  rw [completedInner_sub_left, completedInner_sub_right, completedInner_sub_right,
    complementLimit_symmetric hw0 hw1 x y, complementLimit_pairing_recurrence,
    defect, completedInner_sub_right]
  exact square_pairing_cancel _ _ _

/-- Exact same-object square equation, including the existing boundary kernel. -/
theorem squareRoot_square (x : V) : squareRoot hw0 hw1 (squareRoot hw0 hw1 x) = T 1 x := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [squareRoot_symmetric, squareRoot_pairing, completedInner_time_balance]

theorem squareRoot_norm_bound (x : V) :
    RCle (B (squareRoot hw0 hw1 x) (squareRoot hw0 hw1 x)) (B x x) := by
  rw [squareRoot_pairing]
  exact BF4WilsonAllNomeTimeDefectMoments.completedTime_form_le hw0 hw1 1 x

theorem squareRoot_add (x y : V) :
    squareRoot hw0 hw1 (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (squareRoot hw0 hw1 x) (squareRoot hw0 hw1 y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [squareRoot_symmetric, completedInner_add_left, completedInner_add_left,
    squareRoot_symmetric, squareRoot_symmetric]

theorem squareRoot_smul (c : Q') (x : V) :
    squareRoot hw0 hw1 (completedSmul hw0 hw1 c x) =
      completedSmul hw0 hw1 c (squareRoot hw0 hw1 x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [squareRoot_symmetric, completedInner_smul_left, completedInner_smul_left,
    squareRoot_symmetric]

theorem squareRoot_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    squareRoot hw0 hw1 (completedRealSmul hw0 hw1 s cs x) =
      completedRealSmul hw0 hw1 s cs (squareRoot hw0 hw1 x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [squareRoot_symmetric, completedInner_realSmul_left, completedInner_realSmul_left,
    squareRoot_symmetric]

theorem squareRoot_sub (x y : V) :
    squareRoot hw0 hw1 (completedSub hw0 hw1 x y) =
      completedSub hw0 hw1 (squareRoot hw0 hw1 x) (squareRoot hw0 hw1 y) := by
  unfold completedSub completedNeg
  rw [squareRoot_add, squareRoot_smul]

theorem squareRoot_distance_bound (x y : V) :
    RCle (completedDist hw0 hw1 (squareRoot hw0 hw1 x) (squareRoot hw0 hw1 y))
      (completedDist hw0 hw1 x y) := by
  unfold completedDist
  rw [← squareRoot_sub]
  exact squareRoot_norm_bound hw0 hw1 (completedSub hw0 hw1 x y)

#print axioms complementLimit_symmetric
#print axioms complementLimit_form_le
#print axioms approximant_pairing_recurrence
#print axioms complementLimit_pairing_recurrence
#print axioms squareRoot
#print axioms squareRoot_symmetric
#print axioms squareRoot_nonnegative
#print axioms squareRoot_pairing
#print axioms squareRoot_square
#print axioms squareRoot_norm_bound
#print axioms squareRoot_add
#print axioms squareRoot_smul
#print axioms squareRoot_realSmul
#print axioms squareRoot_sub
#print axioms squareRoot_distance_bound

end YMGap.Continuum.BF4WilsonAllNomeSquareRoot
