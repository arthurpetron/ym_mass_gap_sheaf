/-
Depth-parametric polynomial forms on the SAME original all-nome completion.
The variable h is I-R_depth, not I-T(1).  Coefficient equivalence is transported
through the actual mixed moments. Their exact split gives multiplication by
u=1-h as a ROOT-TIME shift; multiplication by h is a defect shift.
No scalar-only positivity substitution, functional calculus, operator inverse
or kernel exclusion is assumed. Literal log/quotient pins remain separate.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
import YMGap.Continuum.RCPolynomialFunctional
import YMGap.Constructive.QPolyRootLogPositiveRows

namespace YMGap.Continuum.BF4WilsonAllNomeRootPolynomialForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive
open YMGap.Constructive.QPolyUHRow
open YMGap.Constructive.QPolyRootLogDifference
open YMGap.Constructive.QPolyRootLogInitial
open YMGap.Constructive.QPolyRootLogPositiveRows
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
open YMGap.Continuum.RCPolynomialFunctional

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "M" => moment hw0 hw1

/-- Actual finite diagonal coefficient functional, with both moment indices. -/
def form (depth : Nat) (x : V) (k : Nat) (p : Poly) (l : Nat) : RC :=
  formFrom (fun i => M depth x k i) p l

theorem form_coeffEqv (depth : Nat) (x : V) (k l : Nat) {p q : Poly}
    (h : CoeffEqv p q) : form hw0 hw1 depth x k p l = form hw0 hw1 depth x k q l :=
  formFrom_coeffEqv _ h l

theorem form_padd (depth : Nat) (x : V) (k l : Nat) (p q : Poly) :
    form hw0 hw1 depth x k (padd p q) l =
      RCadd (form hw0 hw1 depth x k p l) (form hw0 hw1 depth x k q l) :=
  formFrom_padd _ p q l

theorem form_pscale (depth : Nat) (x : V) (k l : Nat) (c : Q') (p : Poly) :
    form hw0 hw1 depth x k (pscale c p) l = RCscale c (form hw0 hw1 depth x k p l) :=
  formFrom_pscale _ c p l

private theorem mul_constant (c : Q') (p : Poly) :
    CoeffEqv (pmul [c] p) (pscale c p) := by
  intro i
  change (coeff (padd (pscale c p) [0]) i).eqv (coeff (pscale c p) i)
  have hz : (coeff [0] i).eqv 0 := by
    cases i <;> exact Q'.eqv_refl 0
  exact Q'.eqv_trans _ _ _ (coeff_padd i _ _)
    (Q'.eqv_trans _ _ _ (q_add_congr (Q'.eqv_refl _) hz) (q_add_zero_eqv _))

private theorem coordinate_mul (p : Poly) :
    CoeffEqv (pmul coordinate p) ((0 : Q') :: p) := by
  have hz : CoeffEqv (pscale 0 p) [] := by
    intro i
    exact Q'.eqv_trans _ _ _ (coeff_pscale 0 p i) (q_zero_mul _)
  have ht : CoeffEqv (padd (pscale 0 p) (0 :: pmul [1] p)) (padd [] (0 :: p)) :=
    CoeffEqv.padd hz ((coeffEqv_pmul_one_left p).zeroCons)
  exact ht

private theorem complement_mul (p : Poly) :
    CoeffEqv (pmul complement p) (psub p ((0 : Q') :: p)) := by
  have hn : CoeffEqv ((0 : Q') :: pneg p) (pneg ((0 : Q') :: p)) := by
    intro i
    cases i with
    | zero => exact Q'.eqv_symm (q_mul_zero (-1))
    | succ i => exact Q'.eqv_refl _
  exact (CoeffEqv.padd (coeffEqv_pscale_one p)
    (((mul_constant (-1) p).zeroCons).trans hn))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_zero_add_eqv (A.approx n)))

private theorem rc_add_interchange (a b c d : RC) :
    RCadd (RCadd a b) (RCadd c d) = RCadd (RCadd a c) (RCadd b d) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  refine Quotient.inductionOn d ?_
  exact fun D => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_interchange (A.approx n) (B.approx n) (C.approx n) (D.approx n)))

private theorem rc_add_sub_cancel (a b : RC) : RCsub (RCadd a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (A.approx n) (B.approx n) (-(B.approx n)))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ 0 (Q'.add_neg_self_eqv (B.approx n)))
        (QPoly.q_add_zero_eqv _))))

/-- Multiplication by the actual coordinate shifts the original defect index. -/
theorem form_coordinate (depth : Nat) (x : V) (k l : Nat) (p : Poly) :
    form hw0 hw1 depth x k (pmul coordinate p) l = form hw0 hw1 depth x k p (l+1) :=
  (form_coeffEqv hw0 hw1 depth x k l (coordinate_mul p)).trans
    (formFrom_zeroCons _ p l)

/-- The actual moment split extends linearly to EVERY finite signed polynomial. -/
theorem form_split (depth : Nat) (x : V) (k : Nat) (p : Poly) (l : Nat) :
    form hw0 hw1 depth x k p l =
      RCadd (form hw0 hw1 depth x (k+1) p l) (form hw0 hw1 depth x k p (l+1)) := by
  induction p generalizing l with
  | nil => exact (rc_zero_add RCzero).symm
  | cons a p ih =>
      change RCadd (RCscale a (M depth x k l)) (form hw0 hw1 depth x k p (l+1)) = _
      rw [moment_split hw0 hw1 depth x k l, RCscale_RCadd, ih, rc_add_interchange]
      rfl

/-- Multiplication by u=1-h shifts ROOT time, without cancelling an operator. -/
theorem form_complement (depth : Nat) (x : V) (k l : Nat) (p : Poly) :
    form hw0 hw1 depth x k (pmul complement p) l = form hw0 hw1 depth x (k+1) p l := by
  rw [form_coeffEqv hw0 hw1 depth x k l (complement_mul p)]
  change formFrom _ (psub p (0 :: p)) l = _
  rw [formFrom_psub, formFrom_zeroCons]
  change RCsub (form hw0 hw1 depth x k p l) (form hw0 hw1 depth x k p (l+1)) = _
  rw [form_split hw0 hw1 depth x k p l, rc_add_sub_cancel]

private theorem form_coordinatePower (depth : Nat) (x : V) (k l b : Nat) :
    form hw0 hw1 depth x k (polynomialPower coordinate b) l = M depth x k (l+b) := by
  induction b generalizing l with
  | zero =>
      rw [Nat.add_zero]
      change formFrom _ [1] l = _
      rw [formFrom_singleton, RCscale_one]
  | succ b ih =>
      change form hw0 hw1 depth x k (pmul coordinate (polynomialPower coordinate b)) l = _
      rw [form_coordinate, ih]
      congr 1
      omega

/-- EXACT monomial pin on the original completion, for both shifted indices. -/
theorem form_monomial (depth : Nat) (x : V) (k l a b : Nat) :
    form hw0 hw1 depth x k (monomial a b) l = M depth x (k+a) (l+b) := by
  induction a generalizing k with
  | zero =>
      rw [Nat.add_zero]
      exact (form_coeffEqv hw0 hw1 depth x k l
        (coeffEqv_pmul_one_left _)).trans (form_coordinatePower hw0 hw1 depth x k l b)
  | succ a ih =>
      change form hw0 hw1 depth x k
        (pmul (pmul complement (polynomialPower complement a))
          (polynomialPower coordinate b)) l = _
      rw [form_coeffEqv hw0 hw1 depth x k l (coeffEqv_pmul_assoc _ _ _), form_complement]
      change form hw0 hw1 depth x (k+1) (monomial a b) l = _
      rw [ih]
      congr 1
      omega

/-- Literal finite sum of weights times ORIGINAL mixed moments. -/
def rowForm (depth : Nat) (x : V) (k l : Nat) : Row → RC
  | [] => RCzero
  | t :: r => RCadd (RCscale t.weight (M depth x (k+t.uDegree) (l+t.hDegree)))
      (rowForm depth x k l r)

theorem form_row (depth : Nat) (x : V) (k l : Nat) (r : Row) :
    form hw0 hw1 depth x k (polynomial r) l = rowForm hw0 hw1 depth x k l r := by
  induction r with
  | nil => rfl
  | cons t r ih =>
      change form hw0 hw1 depth x k
        (padd (pscale t.weight (monomial t.uDegree t.hDegree)) (polynomial r)) l = _
      rw [form_padd, form_pscale, form_monomial, ih]
      rfl

theorem rowForm_nonnegative (depth : Nat) (x : V) (k l : Nat) (r : Row)
    (hr : nonnegative r) : RCnonneg (rowForm hw0 hw1 depth x k l r) := by
  induction r with
  | nil => exact RCle_refl _
  | cons t r ih =>
      have ht : RCnonneg (RCscale t.weight (M depth x (k+t.uDegree) (l+t.hDegree))) := by
        change RCle RCzero (RCscale t.weight (M depth x (k+t.uDegree) (l+t.hDegree)))
        rw [← RCscale_RCzero t.weight]
        exact RCscale_mono hr.1 (moment_nonnegative hw0 hw1 _ _ _ _)
      simpa only [rowForm, rc_zero_add] using RCadd_le_add ht (ih hr.2)

/-- ORIGINAL S is nonnegative in EVERY actual root/defect moment form. -/
theorem original_s_nonnegative (depth : Nat) (x : V) (k l n m : Nat) :
    RCnonneg (form hw0 hw1 depth x k (rootLogDifference n m) l) := by
  rw [← form_coeffEqv hw0 hw1 depth x k l (original_sRow n m), form_row]
  exact rowForm_nonnegative hw0 hw1 depth x k l _ (nonnegative_sRow n m)

/-- ORIGINAL F is nonnegative in EVERY actual root/defect moment form. -/
theorem original_f_nonnegative (depth : Nat) (x : V) (k l n m : Nat) :
    RCnonneg (form hw0 hw1 depth x k (rootLogRemainder n m) l) := by
  rw [← form_coeffEqv hw0 hw1 depth x k l (original_fRow n m), form_row]
  exact rowForm_nonnegative hw0 hw1 depth x k l _ (nonnegative_fRow n m)

#print axioms form
#print axioms form_coeffEqv
#print axioms form_padd
#print axioms form_pscale
#print axioms form_coordinate
#print axioms form_split
#print axioms form_complement
#print axioms form_monomial
#print axioms rowForm
#print axioms form_row
#print axioms rowForm_nonnegative
#print axioms original_s_nonnegative
#print axioms original_f_nonnegative

end YMGap.Continuum.BF4WilsonAllNomeRootPolynomialForm
