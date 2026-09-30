/-
# Compatible positive roots of the ORIGINAL completed Wilson transfer

The explicit finite square error tends to zero in original pairings. The
represented limits therefore satisfy R_(k+1)^2=R_k, with R_0 exactly T.
No inverse, spectral theorem, replacement carrier or quotient representative
selection is used. Continuous time and its generator remain separate.
-/

import YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
import YMGap.Continuum.BF4WilsonAllNomeNestedRootErrorSmall
import YMGap.Continuum.BF4WilsonAllNomeGraphDistance

namespace YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (completedDist_sub_le)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeRootIteration (polynomialCauchy polynomialCauchy_pin)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootIteration
open YMGap.Continuum.BF4WilsonAllNomeNestedRootSquareError
open YMGap.Continuum.BF4WilsonAllNomeNestedRootErrorSmall
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "R" => root hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem zero_two_halves (e : Q') :
    RCadd (RCadd RCzero RCzero)
      (RCadd (rat (HalfPow.half*e)) (rat (HalfPow.half*e))) = rat e := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) (ExpNeg.two_halves e)))

private theorem constant_sub_distance_small (x a b : V) (e : Q')
    (h : RCle (completedDist hw0 hw1 a b) (rat (HalfPow.half*e))) :
    RCle (completedDist hw0 hw1 (completedSub hw0 hw1 x a) (completedSub hw0 hw1 x b))
      (rat e) := by
  have ht := completedDist_sub_le hw0 hw1 x x a b
  rw [(completedDist_zero_iff hw0 hw1 x x).mpr rfl] at ht
  have hh := RCle_trans ht (RCadd_le_add (RCle_refl (RCadd RCzero RCzero))
    (RCadd_le_add h h))
  rwa [zero_two_halves] at hh

/-- Explicit finite root representatives, still polynomials in the ORIGINAL D. -/
def rootRows (k : Nat) (X : (D).Cauchy) : RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => polynomialCauchy hw0 hw1 (rootPolynomial k n) 0 X
  modulus := fun e => iterationModulus hw0 hw1 k X (HalfPow.half*e)
  isCauchy := by
    intro epsilon he m n hm hn
    have h := (iterationRows hw0 hw1 k X).isCauchy
      (HalfPow.half*epsilon) (ExpNeg.half_mul_pos epsilon he) m n hm hn
    change RCle (completedDist hw0 hw1 (rowPoint hw0 hw1 (iterationRows hw0 hw1 k X) m)
      (rowPoint hw0 hw1 (iterationRows hw0 hw1 k X) n)) (rat (HalfPow.half*epsilon)) at h
    rw [iterationRows_point, iterationRows_point] at h
    change RCle (completedDist hw0 hw1
      (Class (polynomialCauchy hw0 hw1 (rootPolynomial k m) 0 X))
      (Class (polynomialCauchy hw0 hw1 (rootPolynomial k n) 0 X))) _
    rw [polynomialCauchy_pin, polynomialCauchy_pin]
    change RCle (completedDist hw0 hw1 (finiteRoot hw0 hw1 k m (Class X))
      (finiteRoot hw0 hw1 k n (Class X))) _
    rw [finiteRoot_eq_sub, finiteRoot_eq_sub]
    exact constant_sub_distance_small hw0 hw1 (Class X) _ _ epsilon h

theorem rootRows_point (k : Nat) (X : (D).Cauchy) (n : Nat) :
    rowPoint hw0 hw1 (rootRows hw0 hw1 k X) n = finiteRoot hw0 hw1 k n (Class X) :=
  polynomialCauchy_pin hw0 hw1 (rootPolynomial k n) 0 X

theorem limit_rootRows (k : Nat) (X : (D).Cauchy) :
    limit hw0 hw1 (rootRows hw0 hw1 k X) = R k (Class X) := by
  apply limit_unique hw0 hw1 (rootRows hw0 hw1 k X) (R k (Class X))
    (fun e => convergenceModulus hw0 hw1 k X (HalfPow.half*e))
  intro epsilon he n hn
  rw [rootRows_point, finiteRoot_eq_sub, root]
  exact constant_sub_distance_small hw0 hw1 (Class X) _ _ epsilon
    (nestedLimit_approximation hw0 hw1 k X (HalfPow.half*epsilon)
      (ExpNeg.half_mul_pos epsilon he) n hn)

private def third (e : Q') : Q' := Q'.invSucc 2 * e

private theorem three_thirds (e : Q') : Q'.eqv (3 * third e) e :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (3*Q'.invSucc 2) (1 : Q')))
      (Q'.one_mul_eqv e))

private theorem three_errors (a : RC) (e : Q') :
    RCadd (RCadd (RCadd a (rat (third e))) (rat (third e))) (rat (third e)) =
      RCadd a (rat e) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.add (.var 0) (.var 1)) (.var 1)) (.var 1))
        (.add (.var 0) (.mul (.const 3) (.var 1)))
        (by decide) (fun | 0 => A.approx n | _ => third e))
      (Q'.add_eqv_congr_left _ _ _ (three_thirds e))))

private theorem add_negative_cancel (a b : RC) : RCadd (RCadd a b) (RCneg b) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (B'.approx n)))
        (QPoly.q_add_zero_eqv _))))

private theorem scalar_square_errors (a an c cn err : RC) (e : Q')
    (hA : RCle an (RCadd a (rat (third e))) ∧ RCle a (RCadd an (rat (third e))))
    (hC : RCle cn (RCadd c (rat (third e))) ∧ RCle c (RCadd cn (rat (third e))))
    (hE : RCle err (rat (third e)) ∧ RCle (RCneg err) (rat (third e)))
    (hrec : an = RCadd cn err) :
    RCle a (RCadd c (rat e)) ∧ RCle c (RCadd a (rat e)) := by
  have hb : RCle an (RCadd cn (rat (third e))) ∧
      RCle cn (RCadd an (rat (third e))) := by
    constructor
    · rw [hrec]
      exact RCadd_le_add (RCle_refl cn) hE.1
    · have h := RCadd_le_add (RCle_refl an) hE.2
      have hc : RCadd an (RCneg err) = cn := by
        rw [hrec, add_negative_cancel]
      rwa [hc] at h
  constructor
  · have h := RCle_trans hA.2 (RCadd_le_add hb.1 (RCle_refl (rat (third e))))
    have hh := RCle_trans h
      (RCadd_le_add (RCadd_le_add hC.1 (RCle_refl (rat (third e))))
        (RCle_refl (rat (third e))))
    rwa [three_errors] at hh
  · have h := RCle_trans hC.2 (RCadd_le_add hb.2 (RCle_refl (rat (third e))))
    have hh := RCle_trans h
      (RCadd_le_add (RCadd_le_add hA.1 (RCle_refl (rat (third e))))
        (RCle_refl (rat (third e))))
    rwa [three_errors] at hh

private theorem root_pairing_errors (k : Nat) (x y : V) (e : Q') (he : (0 : Q') < e) :
    RCle (B (R (k+1) x) (R (k+1) y)) (RCadd (B x (R k y)) (rat e)) ∧
      RCle (B x (R k y)) (RCadd (B (R (k+1) x) (R (k+1) y)) (rat e)) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  let q := third e
  have hq : (0 : Q') < q := Q'.mul_pos (Q'.invSucc_pos 2) he
  let a := pairingModulus hw0 hw1 (rootRows hw0 hw1 (k+1) X) (rootRows hw0 hw1 (k+1) Y) q
  let b := pairingModulus hw0 hw1 (constantRows hw0 hw1 X) (rootRows hw0 hw1 k Y) q
  let c := errorPairingModulus hw0 hw1 X Y q
  let n := max a (max b c)
  have hA := row_pairing_bound hw0 hw1 (rootRows hw0 hw1 (k+1) X)
    (rootRows hw0 hw1 (k+1) Y) q hq n (Nat.le_max_left _ _)
  have hC := row_pairing_bound hw0 hw1 (constantRows hw0 hw1 X)
    (rootRows hw0 hw1 k Y) q hq n (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  have hE := nestedError_pairing_small hw0 hw1 k X Y q hq n
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  rw [rootRows_point, rootRows_point, limit_rootRows, limit_rootRows] at hA
  rw [constantRows_point, rootRows_point, limit_constantRows, limit_rootRows] at hC
  exact scalar_square_errors _ _ _ _ _ e hA hC hE
    (finite_square_pairing_identity hw0 hw1 k n (Class X) (Class Y))

/-- The controlled finite error disappears in the SAME original pairing. -/
theorem root_pairing (k : Nat) (x y : V) :
    B (R (k+1) x) (R (k+1) y) = B x (R k y) :=
  RCle_antisymm
    (RationalScalarTwoSidedError.le_of_all_errors _ _ (fun e he =>
      (root_pairing_errors hw0 hw1 k x y e he).1))
    (RationalScalarTwoSidedError.le_of_all_errors _ _ (fun e he =>
      (root_pairing_errors hw0 hw1 k x y e he).2))

/-- Compatible square laws for the constructed roots, with no invertibility hypothesis. -/
theorem root_square (k : Nat) (x : V) : R (k+1) (R (k+1) x) = R k x := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [root_symmetric hw0 hw1 (k+1), root_pairing, root_symmetric hw0 hw1 k]

theorem root_norm_bound (k : Nat) (x : V) :
    RCle (B (R k x) (R k x)) (B x x) := by
  cases k with
  | zero =>
      rw [root_zero_depth]
      exact completedInner_time_contraction hw0 hw1 1 x
  | succ k =>
      rw [root_pairing]
      exact root_form_le hw0 hw1 k x

theorem root_distance_bound (k : Nat) (x y : V) :
    RCle (completedDist hw0 hw1 (R k x) (R k y)) (completedDist hw0 hw1 x y) := by
  unfold completedDist
  rw [← root_sub]
  exact root_norm_bound hw0 hw1 k (completedSub hw0 hw1 x y)

theorem root_zero (k : Nat) : R k (completedZero hw0 hw1 width) = completedZero hw0 hw1 width := by
  have h := root_smul hw0 hw1 k 0 (completedZero hw0 hw1 width)
  rw [BF4WilsonAllNomeLinearLaws.completedSmul_zero,
    BF4WilsonAllNomeLinearLaws.completedSmul_zero] at h
  exact h

/-- Every constructed root retains exactly the ORIGINAL transfer kernel. -/
theorem root_zero_iff_time_zero (k : Nat) (x : V) :
    R k x = completedZero hw0 hw1 width ↔
      completedTime hw0 hw1 1 x = completedZero hw0 hw1 width := by
  induction k with
  | zero => rw [root_zero_depth]
  | succ k ih =>
      constructor
      · intro h
        apply ih.mp
        rw [← root_square hw0 hw1 k x, h, root_zero]
      · intro h
        apply (BF4WilsonAllNomeGeometry.completedInner_posdef hw0 hw1 width (R (k+1) x)).mp
        rw [root_pairing, ih.mpr h, completedInner_zero_right]

#print axioms rootRows
#print axioms limit_rootRows
#print axioms root_pairing
#print axioms root_square
#print axioms root_norm_bound
#print axioms root_distance_bound
#print axioms root_zero
#print axioms root_zero_iff_time_zero

end YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
