/-
Basic linear and order laws for the fixed-depth nested roots on the original
completed Wilson carrier. Square compatibility is proved separately.
-/

import YMGap.Continuum.BF4WilsonAllNomeNestedRootIteration
import YMGap.Continuum.BF4WilsonAllNomeNestedRootSquareError
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Constructive.CRealArtanhEulerPositiveCompanion (CoeffNonnegative)
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor (pvar)
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
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect time_add_defect)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defectPower)
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
open YMGap.Continuum.BF4WilsonAllNomeNestedRootIteration
open YMGap.Continuum.BF4WilsonAllNomeNestedRootSquareError
open YMGap.Continuum.ComplementRootComposition

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "H" => nestedLimit hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- A fixed-depth root, retaining the original transfer's boundary kernel. -/
def root (k : Nat) (x : V) : V := completedSub hw0 hw1 x (H k x)

def finiteRoot (k n : Nat) (x : V) : V :=
  action hw0 hw1 (rootPolynomial k n) x

theorem finiteRoot_eq_sub (k n : Nat) (x : V) :
    finiteRoot hw0 hw1 k n x =
      completedSub hw0 hw1 x (approximant hw0 hw1 k n x) := by
  unfold finiteRoot rootPolynomial approximant
  rw [action_sub]
  change completedSub hw0 hw1 (action hw0 hw1 [1] x)
    (action hw0 hw1 (nested k n) x) = _
  have hunit : action hw0 hw1 ([1] : Poly) x = x := by
    change A (S 1 x) Z = x
    rw [completedSmul_one, completedAdd_zero]
  rw [hunit]

theorem root_symmetric (k : Nat) (x y : V) :
    B (root hw0 hw1 k x) y = B x (root hw0 hw1 k y) := by
  unfold root
  rw [completedInner_sub_left, completedInner_sub_right,
    nestedLimit_symmetric]

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (X.approx n)))

private theorem rc_sub_nonnegative {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have hs := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at hs
  rwa [rc_sub_self] at hs

theorem root_nonnegative (k : Nat) (x : V) :
    RCnonneg (B x (root hw0 hw1 k x)) := by
  rw [root, completedInner_sub_right]
  exact rc_sub_nonnegative (nestedLimit_form_le hw0 hw1 k x)

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (X.approx n))))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (X.approx n)))

private theorem rc_add_nonnegative {a b : RC}
    (ha : RCnonneg a) (hb : RCnonneg b) : RCnonneg (RCadd a b) := by
  have h := RCadd_le_add ha hb
  rw [rc_zero_add] at h
  exact h

private theorem rc_scale_nonnegative {c : Q'} (hc : (0 : Q') ≤ c)
    {a : RC} (ha : RCnonneg a) : RCnonneg (RCscale c a) := by
  have h := RCscale_mono hc ha
  rw [RCscale_RCzero] at h
  exact h

/-- A positive-coefficient finite polynomial has nonnegative pairing with
every original defect power on the same input. -/
theorem actionFrom_defect_form_nonnegative (p : Poly)
    (hp : CoeffNonnegative p) (x : V) (i j : Nat) :
    RCnonneg (B (actionFrom hw0 hw1 p i x) (defectPower hw0 hw1 j x)) := by
  induction p generalizing i with
  | nil =>
      change RCnonneg (B Z (defectPower hw0 hw1 j x))
      rw [completedInner_zero_left]
      exact RCle_refl _
  | cons a p ih =>
      change RCnonneg
        (B (A (S a (defectPower hw0 hw1 i x))
          (actionFrom hw0 hw1 p (i+1) x))
          (defectPower hw0 hw1 j x))
      rw [completedInner_add_left, completedInner_smul_left]
      exact rc_add_nonnegative
        (rc_scale_nonnegative (hp 0)
          (defect_pair_nonnegative hw0 hw1 x i j))
        (ih (fun index => hp (index+1)) (i+1))

theorem action_form_nonnegative (p : Poly) (hp : CoeffNonnegative p) (x : V) :
    RCnonneg (B x (action hw0 hw1 p x)) := by
  have h := actionFrom_defect_form_nonnegative hw0 hw1 p hp x 0 0
  change RCnonneg (B (action hw0 hw1 p x) x) at h
  rwa [completedInner_symm hw0 hw1 (action hw0 hw1 p x) x] at h

/-- Positivity of the original-carrier nested limit follows by the explicit
represented-row pairing modulus, not by a new spectral premise. -/
theorem nestedLimit_nonnegative (k : Nat) (x : V) :
    RCnonneg (B x (H k x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let R := constantRows hw0 hw1 X
  let U := iterationRows hw0 hw1 k X
  let n := pairingModulus hw0 hw1 R U epsilon
  have h := (row_pairing_bound hw0 hw1 R U epsilon he n (Nat.le_refl n)).1
  change RCle (B (rowPoint hw0 hw1 (constantRows hw0 hw1 X) n)
    (rowPoint hw0 hw1 (iterationRows hw0 hw1 k X) n))
      (RCadd (B (limit hw0 hw1 (constantRows hw0 hw1 X))
        (limit hw0 hw1 (iterationRows hw0 hw1 k X))) (Rq epsilon)) at h
  rw [constantRows_point, iterationRows_point, limit_constantRows] at h
  exact RCle_trans
    (action_form_nonnegative hw0 hw1 (nested k n)
      (nested_coeffNonnegative k n) (Class X)) h

private theorem rc_sub_add (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (X.approx n) (Y.approx n)))

theorem root_form_le (k : Nat) (x : V) :
    RCle (B x (root hw0 hw1 k x)) (B x x) := by
  rw [root, completedInner_sub_right]
  have h := RCadd_le_add
    (RCle_refl (RCsub (B x x) (B x (H k x))))
    (nestedLimit_nonnegative hw0 hw1 k x)
  rw [rc_add_zero, rc_sub_add] at h
  exact h

theorem root_add (k : Nat) (x y : V) :
    root hw0 hw1 k (A x y) =
      A (root hw0 hw1 k x) (root hw0 hw1 k y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [root_symmetric, completedInner_add_left, completedInner_add_left,
    root_symmetric, root_symmetric]

theorem root_smul (k : Nat) (c : Q') (x : V) :
    root hw0 hw1 k (S c x) = S c (root hw0 hw1 k x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [root_symmetric, completedInner_smul_left, completedInner_smul_left,
    root_symmetric]

theorem root_realSmul (k : Nat) (s : CReal) (cs : QCauchy s.approx) (x : V) :
    root hw0 hw1 k (completedRealSmul hw0 hw1 s cs x) =
      completedRealSmul hw0 hw1 s cs (root hw0 hw1 k x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [root_symmetric, completedInner_realSmul_left, completedInner_realSmul_left,
    root_symmetric]

theorem root_sub (k : Nat) (x y : V) :
    root hw0 hw1 k (completedSub hw0 hw1 x y) =
      completedSub hw0 hw1 (root hw0 hw1 k x) (root hw0 hw1 k y) := by
  unfold completedSub completedNeg
  rw [root_add, root_smul]

private theorem action_pvar (x : V) :
    action hw0 hw1 pvar x = defect hw0 hw1 x := by
  change A (S 0 x) (A (S 1 (defect hw0 hw1 x)) Z) = _
  rw [completedSmul_zero, completedSmul_one, completedAdd_zero, completedZero_add]

/-- At depth zero every finite row is exactly the original time defect. -/
theorem nestedLimit_zero_depth (x : V) :
    H 0 x = defect hw0 hw1 x := by
  refine Quotient.inductionOn x ?_
  intro X
  let Y := BF4WilsonAllNomeRootIteration.polynomialCauchy hw0 hw1 pvar 0 X
  have h := limit_independent hw0 hw1
    (iterationRows hw0 hw1 0 X) (constantRows hw0 hw1 Y) (fun n => by
      rw [iterationRows_point, constantRows_point,
        BF4WilsonAllNomeRootIteration.polynomialCauchy_pin]
      rfl)
  change H 0 (Class X) = defect hw0 hw1 (Class X)
  change limit hw0 hw1 (iterationRows hw0 hw1 0 X) = _
  rw [h, limit_constantRows,
    BF4WilsonAllNomeRootIteration.polynomialCauchy_pin]
  exact action_pvar hw0 hw1 (Class X)

/-- The first dyadic row is exactly the original one-step transfer. -/
theorem root_zero_depth (x : V) : root hw0 hw1 0 x = T 1 x := by
  rw [root, nestedLimit_zero_depth]
  let d := defect hw0 hw1 x
  change completedSub hw0 hw1 x d = T 1 x
  unfold completedSub
  calc
    A x (completedNeg hw0 hw1 d) =
        A (A (T 1 x) d) (completedNeg hw0 hw1 d) :=
      congrArg (fun z => A z (completedNeg hw0 hw1 d))
        (time_add_defect hw0 hw1 x).symm
    _ = A (T 1 x) (A d (completedNeg hw0 hw1 d)) :=
      completedAdd_assoc hw0 hw1 _ _ _
    _ = A (T 1 x) Z := by
      rw [completedAdd_comm hw0 hw1 d (completedNeg hw0 hw1 d),
        completedNeg_add]
    _ = T 1 x := completedAdd_zero hw0 hw1 _

#print axioms finiteRoot_eq_sub
#print axioms root_symmetric
#print axioms root_nonnegative
#print axioms actionFrom_defect_form_nonnegative
#print axioms action_form_nonnegative
#print axioms nestedLimit_nonnegative
#print axioms root_form_le
#print axioms root_add
#print axioms root_smul
#print axioms root_realSmul
#print axioms root_sub
#print axioms nestedLimit_zero_depth
#print axioms root_zero_depth

end YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
