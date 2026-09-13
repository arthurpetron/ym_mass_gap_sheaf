/-
# Exact two-slot inclusion-exclusion and its retained small factors

The iterated difference of B(product(1+r), product(1+r)) equals the
computed three-term insertion recursion. If r has a two-sided Haar
interval cap d, each step costs d+d+d*d. This bounds the ACTUAL Mobius
coefficient, not just the original single-copy remainder activity.
-/

import YMGap.Continuum.PolynomialBiadditive
import YMGap.Continuum.FiniteSelectionMobius

namespace YMGap.Continuum.PolynomialBiadditiveMobius

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.PolynomialBiadditive
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

theorem coefficient_sub {A : Type} (f g : List A → Q') : ∀ xs : List A,
    coefficient (fun ys => f ys + -(g ys)) xs ≈ coefficient f xs + -(coefficient g xs)
  | [] => Q'.eqv_refl _
  | a :: xs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (coefficient_sub (fun ys => f (a::ys)) (fun ys => g (a::ys)) xs)
        (Q'.neg_eqv_congr _ _ (coefficient_sub f g xs)))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
        (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 3))))) (by decide)
        (fun i => if i = 0 then coefficient (fun ys => f (a::ys)) xs
          else if i = 1 then coefficient (fun ys => g (a::ys)) xs
          else if i = 2 then coefficient f xs else coefficient g xs))

def pairedCoefficient {A : Type} (B : Biadditive) (r : A → RatPoly) : List A → Q'
  | [] => B.value polyOne polyOne
  | a :: xs => pairedCoefficient (B.increment (r a)) r xs

theorem pairedCoefficient_pin {A : Type} (B : Biadditive) (f r : A → RatPoly)
    (h : ∀ a, RatPolyCoeffEqv (f a) (polyAdd polyOne (r a))) : ∀ xs : List A,
    coefficient (fun ys => B.value (polynomialProduct f ys) (polynomialProduct f ys)) xs ≈
      pairedCoefficient B r xs
  | [] => Q'.eqv_refl _
  | a :: xs => Q'.eqv_trans _ _ _
      (Q'.eqv_symm (coefficient_sub
        (fun ys => B.value (polynomialProduct f (a::ys)) (polynomialProduct f (a::ys)))
        (fun ys => B.value (polynomialProduct f ys) (polynomialProduct f ys)) xs))
      (Q'.eqv_trans _ _ _ (coefficient_congr _ _ xs
        (fun ys _ => B.diagonal_increment (f a) (r a) (polynomialProduct f ys) (h a)))
        (pairedCoefficient_pin (B.increment (r a)) f r h xs))

def pairedRate (d : Q') : Q' := d+d+d*d

def IntervalBound (B : Biadditive) (blocks : Nat) (C : Q') : Prop :=
  ∀ {p q : RatPoly} {a b : Q'}, Interval blocks p a → Interval blocks q b →
    Q'.abs (B.value p q) ≤ C*a*b

theorem increment_bound {B : Biadditive} {blocks : Nat} {C d : Q'}
    (hB : IntervalBound B blocks C) {r : RatPoly} (R : Interval blocks r d) :
    IntervalBound (B.increment r) blocks (C*pairedRate d) := by
  intro p q a b P Q
  have h1 := hB (R.mul P) Q
  have h2 := hB P (R.mul Q)
  have h3 := hB (R.mul P) (R.mul Q)
  have ht := Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
    (Q'.add_le_add (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) (Q'.add_le_add h1 h2)) h3)
  exact Q'.le_trans' _ _ _ ht (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.add (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 3))))
    (.mul (.mul (.mul (.var 0) (.add (.add (.var 1) (.var 1)) (.mul (.var 1) (.var 1)))) (.var 2)) (.var 3))
    (by decide) (fun i => if i = 0 then C else if i = 1 then d else if i = 2 then a else b)))

theorem pairedCoefficient_bound {A : Type} (B : Biadditive) (blocks : Nat) (C d : Q')
    (hB : IntervalBound B blocks C) (r : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → Interval blocks (r a) d) →
    Q'.abs (pairedCoefficient B r xs) ≤ C*(pairedRate d)^xs.length
  | [], _ => Q'.le_trans' _ _ _ (hB (Interval.one blocks) (Interval.one blocks))
      (Q'.le_of_eqv (Q'.mul_one_eqv (C*1)))
  | a :: xs, h => Q'.le_trans' _ _ _
      (pairedCoefficient_bound (B.increment (r a)) blocks (C*pairedRate d) d
        (increment_bound hB (h a List.mem_cons_self)) r xs
        (fun b hb => h b (List.mem_cons_of_mem a hb)))
      (Q'.le_of_eqv (Q'.mul_assoc_eqv C (pairedRate d) ((pairedRate d)^xs.length)))

/-- Direct bound on the iterated finite difference of the two-copy moment. -/
theorem diagonal_coefficient_bound {A : Type} (B : Biadditive) (blocks : Nat) (C d : Q')
    (hB : IntervalBound B blocks C) (f r : A → RatPoly)
    (h : ∀ a, RatPolyCoeffEqv (f a) (polyAdd polyOne (r a))) (xs : List A)
    (hr : ∀ a, a ∈ xs → Interval blocks (r a) d) :
    Q'.abs (coefficient (fun ys => B.value (polynomialProduct f ys) (polynomialProduct f ys)) xs) ≤
      C*(pairedRate d)^xs.length :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (pairedCoefficient_pin B f r h xs)))
    (pairedCoefficient_bound B blocks C d hB r xs hr)

end YMGap.Continuum.PolynomialBiadditiveMobius

#print axioms YMGap.Continuum.PolynomialBiadditiveMobius.coefficient_sub
#print axioms YMGap.Continuum.PolynomialBiadditiveMobius.pairedCoefficient
#print axioms YMGap.Continuum.PolynomialBiadditiveMobius.pairedCoefficient_pin
#print axioms YMGap.Continuum.PolynomialBiadditiveMobius.pairedRate
#print axioms YMGap.Continuum.PolynomialBiadditiveMobius.IntervalBound
#print axioms YMGap.Continuum.PolynomialBiadditiveMobius.increment_bound
#print axioms YMGap.Continuum.PolynomialBiadditiveMobius.pairedCoefficient_bound
#print axioms YMGap.Continuum.PolynomialBiadditiveMobius.diagonal_coefficient_bound
