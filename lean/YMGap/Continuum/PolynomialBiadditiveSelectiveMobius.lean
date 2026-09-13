/-
# Selective two-slot finite differences, with the actual insertion costs

A selected factor enters the left slot always and the right slot precisely
when its Boolean test passes. The exact finite-difference coefficient is
computed by a one-term or three-term insertion recursion. Its bound retains
one remainder cost d or the paired cost d+d+d*d at each respective step.
No positivity of the two-slot form or independence of variables is assumed.
-/

import YMGap.Continuum.PolynomialBiadditiveMobius

namespace YMGap.Continuum.PolynomialBiadditiveSelectiveMobius

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.PolynomialBiadditive
open YMGap.Continuum.PolynomialBiadditiveMobius
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem insert_pin (h r p : RatPoly)
    (hh : RatPolyCoeffEqv h (polyAdd polyOne r)) :
    RatPolyCoeffEqv (polyMul h p) (polyAdd p (polyMul r p)) := by
  have he := hh.mul (RatPolyCoeffEqv.refl p)
  rw [polyMul_add_left_exact] at he
  exact he.trans ((RatPolyCoeffEqv.one_mul p).add (RatPolyCoeffEqv.refl _))

theorem left_increment (B : Biadditive) (h r p q : RatPoly)
    (hh : RatPolyCoeffEqv h (polyAdd polyOne r)) :
    B.value (polyMul h p) q + -(B.value p q) ≈ (B.left r).value p q :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _
      (B.congr (insert_pin h r p hh) (RatPolyCoeffEqv.refl q)) (B.add_left _ _ _))
      (Q'.eqv_refl _))
    (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun i => if i = 0 then B.value p q else B.value (polyMul r p) q))

/-- The two starting polynomials may differ; only the inserted factor agrees. -/
theorem mixed_increment (B : Biadditive) (h r p q : RatPoly)
    (hh : RatPolyCoeffEqv h (polyAdd polyOne r)) :
    B.value (polyMul h p) (polyMul h q) + -(B.value p q) ≈ (B.increment r).value p q := by
  have he := Q'.eqv_trans _ _ _ (B.congr (insert_pin h r p hh) (insert_pin h r q hh))
    (Q'.eqv_trans _ _ _ (B.add_left _ _ _)
      (Q'.add_eqv_congr' (B.add_right _ _ _) (B.add_right _ _ _)))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' he (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3))) (.neg (.var 0)))
      (.add (.add (.var 2) (.var 1)) (.var 3)) (by decide)
      (fun i => if i = 0 then B.value p q else if i = 1 then B.value p (polyMul r q)
        else if i = 2 then B.value (polyMul r p) q else B.value (polyMul r p) (polyMul r q)))

def step (B : Biadditive) (r : RatPoly) : Bool → Biadditive
  | false => B.left r
  | true => B.increment r

def stepRate (d : Q') : Bool → Q'
  | false => d
  | true => pairedRate d

def selectiveCoefficient {A : Type} (B : Biadditive) (r : A → RatPoly) (keep : A → Bool) : List A → Q'
  | [] => B.value polyOne polyOne
  | a :: xs => selectiveCoefficient (step B (r a) (keep a)) r keep xs

def rateProduct {A : Type} (d : Q') (keep : A → Bool) : List A → Q'
  | [] => 1
  | a :: xs => stepRate d (keep a) * rateProduct d keep xs

theorem selectiveCoefficient_pin {A : Type} (B : Biadditive) (f r : A → RatPoly) (keep : A → Bool)
    (h : ∀ a, RatPolyCoeffEqv (f a) (polyAdd polyOne (r a))) : ∀ xs : List A,
    coefficient (fun ys => B.value (polynomialProduct f ys)
      (polynomialProduct f (ys.filter keep))) xs ≈ selectiveCoefficient B r keep xs
  | [] => Q'.eqv_refl _
  | a :: xs => Q'.eqv_trans _ _ _
      (Q'.eqv_symm (coefficient_sub
        (fun ys => B.value (polynomialProduct f (a::ys)) (polynomialProduct f ((a::ys).filter keep)))
        (fun ys => B.value (polynomialProduct f ys) (polynomialProduct f (ys.filter keep))) xs))
      (Q'.eqv_trans _ _ _ (coefficient_congr _ _ xs (fun ys _ => by
        cases hk : keep a with
        | false => simpa only [List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte,
            polynomialProduct, step] using
            left_increment B (f a) (r a) (polynomialProduct f ys) (polynomialProduct f (ys.filter keep)) (h a)
        | true => simpa only [List.filter_cons, hk, ↓reduceIte, polynomialProduct, step] using
            mixed_increment B (f a) (r a) (polynomialProduct f ys) (polynomialProduct f (ys.filter keep)) (h a)))
        (selectiveCoefficient_pin (step B (r a) (keep a)) f r keep h xs))

theorem left_bound {B : Biadditive} {blocks : Nat} {C d : Q'}
    (hB : IntervalBound B blocks C) {r : RatPoly} (R : Interval blocks r d) :
    IntervalBound (B.left r) blocks (C*d) := by
  intro p q a b P Q
  exact Q'.le_trans' _ _ _ (hB (R.mul P) Q)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ b (Q'.eqv_symm (Q'.mul_assoc_eqv C d a))))

theorem step_bound {B : Biadditive} {blocks : Nat} {C d : Q'}
    (hB : IntervalBound B blocks C) {r : RatPoly} (R : Interval blocks r d) (both : Bool) :
    IntervalBound (step B r both) blocks (C*stepRate d both) := by
  cases both with
  | false => exact left_bound hB R
  | true => exact increment_bound hB R

theorem selectiveCoefficient_bound {A : Type} (B : Biadditive) (blocks : Nat) (C d : Q')
    (hB : IntervalBound B blocks C) (r : A → RatPoly) (keep : A → Bool) : ∀ xs : List A,
    (∀ a, a ∈ xs → Interval blocks (r a) d) →
    Q'.abs (selectiveCoefficient B r keep xs) ≤ C*rateProduct d keep xs
  | [], _ => Q'.le_trans' _ _ _ (hB (Interval.one blocks) (Interval.one blocks))
      (Q'.le_of_eqv (Q'.mul_one_eqv (C*1)))
  | a :: xs, h => Q'.le_trans' _ _ _
      (selectiveCoefficient_bound (step B (r a) (keep a)) blocks (C*stepRate d (keep a)) d
        (step_bound hB (h a List.mem_cons_self) (keep a)) r keep xs
        (fun b hb => h b (List.mem_cons_of_mem a hb)))
      (Q'.le_of_eqv (Q'.mul_assoc_eqv C (stepRate d (keep a)) (rateProduct d keep xs)))

theorem pairedRate_nonnegative {d : Q'} (hd : (0 : Q') ≤ d) : (0 : Q') ≤ pairedRate d :=
  Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hd hd) (Q'.mul_nonneg _ _ hd hd)

theorem stepRate_nonnegative {d : Q'} (hd : (0 : Q') ≤ d) (both : Bool) :
    (0 : Q') ≤ stepRate d both := by
  cases both with
  | false => exact hd
  | true => exact pairedRate_nonnegative hd

theorem rateProduct_nonnegative {A : Type} {d : Q'} (hd : (0 : Q') ≤ d) (keep : A → Bool) :
    ∀ xs : List A, (0 : Q') ≤ rateProduct d keep xs
  | [] => by change (0 : Q') ≤ 1; decide
  | a :: xs => Q'.mul_nonneg _ _ (stepRate_nonnegative hd (keep a)) (rateProduct_nonnegative hd keep xs)

theorem stepRate_le_paired {d : Q'} (hd : (0 : Q') ≤ d) (both : Bool) : stepRate d both ≤ pairedRate d := by
  cases both with
  | true => exact Q'.le_refl' _
  | false =>
      apply Q'.le_of_sub_nonneg
      exact Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ hd (Q'.mul_nonneg _ _ hd hd))
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.var 0) (.mul (.var 0) (.var 0)))
          (.add (.add (.add (.var 0) (.var 0)) (.mul (.var 0) (.var 0))) (.neg (.var 0)))
          (by decide) (fun _ => d)))

theorem rateProduct_le_pairedPow {A : Type} {d : Q'} (hd : (0 : Q') ≤ d) (keep : A → Bool) :
    ∀ xs : List A, rateProduct d keep xs ≤ (pairedRate d)^xs.length
  | [] => Q'.le_refl' _
  | a :: xs => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (stepRate_le_paired hd (keep a)) (rateProduct_nonnegative hd keep xs))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (rateProduct_le_pairedPow hd keep xs) (pairedRate_nonnegative hd))

end YMGap.Continuum.PolynomialBiadditiveSelectiveMobius

#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.left_increment
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.mixed_increment
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.step
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.stepRate
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.selectiveCoefficient
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.rateProduct
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.selectiveCoefficient_pin
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.left_bound
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.step_bound
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.selectiveCoefficient_bound
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.pairedRate_nonnegative
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.stepRate_nonnegative
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.rateProduct_nonnegative
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.stepRate_le_paired
#print axioms YMGap.Continuum.PolynomialBiadditiveSelectiveMobius.rateProduct_le_pairedPow
