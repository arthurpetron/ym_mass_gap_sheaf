/-
# Finite two-slot polynomial algebra for original moment products

The interface records only coefficient congruence and additivity in each
slot. Its constructors prove those laws. A simultaneous insertion of
1+r in both slots, minus the old value, has exactly three terms: r on the
left, r on the right, and r on both. No independent-link law is asserted.
-/

import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.PolynomialBiadditive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

structure Biadditive : Type where
  value : RatPoly → RatPoly → Q'
  congr : ∀ {p p' q q'}, RatPolyCoeffEqv p p' → RatPolyCoeffEqv q q' → value p q ≈ value p' q'
  add_left : ∀ p q r, value (polyAdd p q) r ≈ value p r + value q r
  add_right : ∀ p q r, value p (polyAdd q r) ≈ value p q + value p r

namespace Biadditive

def add (B C : Biadditive) : Biadditive where
  value := fun p q => B.value p q + C.value p q
  congr := fun hp hq => Q'.add_eqv_congr' (B.congr hp hq) (C.congr hp hq)
  add_left := fun p q r => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (B.add_left p q r) (C.add_left p q r))
    (Q'.add_swap_inner _ _ _ _)
  add_right := fun p q r => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (B.add_right p q r) (C.add_right p q r))
    (Q'.add_swap_inner _ _ _ _)

def neg (B : Biadditive) : Biadditive where
  value := fun p q => -(B.value p q)
  congr := fun hp hq => Q'.neg_eqv_congr _ _ (B.congr hp hq)
  add_left := fun p q r => Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (B.add_left p q r)) (Q'.neg_add_eqv_split _ _)
  add_right := fun p q r => Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (B.add_right p q r)) (Q'.neg_add_eqv_split _ _)

def left (B : Biadditive) (r : RatPoly) : Biadditive where
  value := fun p q => B.value (polyMul r p) q
  congr := fun hp hq => B.congr ((RatPolyCoeffEqv.refl r).mul hp) hq
  add_left := fun p q s => Q'.eqv_trans _ _ _
    (B.congr (RatPolyCoeffEqv.mul_add_right r p q) (RatPolyCoeffEqv.refl s)) (B.add_left _ _ _)
  add_right := fun p q s => B.add_right (polyMul r p) q s

def right (B : Biadditive) (r : RatPoly) : Biadditive where
  value := fun p q => B.value p (polyMul r q)
  congr := fun hp hq => B.congr hp ((RatPolyCoeffEqv.refl r).mul hq)
  add_left := fun p q s => B.add_left p q (polyMul r s)
  add_right := fun p q s => Q'.eqv_trans _ _ _
    (B.congr (RatPolyCoeffEqv.refl p) (RatPolyCoeffEqv.mul_add_right r q s)) (B.add_right _ _ _)

def increment (B : Biadditive) (r : RatPoly) : Biadditive :=
  ((B.left r).add (B.right r)).add ((B.left r).right r)

/-- Both copies of the SAME action are expanded; the constant term cancels. -/
theorem diagonal_increment (B : Biadditive) (h r p : RatPoly)
    (hh : RatPolyCoeffEqv h (polyAdd polyOne r)) :
    B.value (polyMul h p) (polyMul h p) + -(B.value p p) ≈ (B.increment r).value p p := by
  have hp : RatPolyCoeffEqv (polyMul h p) (polyAdd p (polyMul r p)) := by
    have he := hh.mul (RatPolyCoeffEqv.refl p)
    rw [polyMul_add_left_exact] at he
    exact he.trans ((RatPolyCoeffEqv.one_mul p).add (RatPolyCoeffEqv.refl _))
  have he := Q'.eqv_trans _ _ _ (B.congr hp hp)
    (Q'.eqv_trans _ _ _ (B.add_left _ _ _) (Q'.add_eqv_congr' (B.add_right _ _ _) (B.add_right _ _ _)))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' he (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3))) (.neg (.var 0)))
      (.add (.add (.var 2) (.var 1)) (.var 3)) (by decide)
      (fun i => if i = 0 then B.value p p else if i = 1 then B.value p (polyMul r p)
        else if i = 2 then B.value (polyMul r p) p else B.value (polyMul r p) (polyMul r p)))

end Biadditive
end YMGap.Continuum.PolynomialBiadditive

#print axioms YMGap.Continuum.PolynomialBiadditive.Biadditive
#print axioms YMGap.Continuum.PolynomialBiadditive.Biadditive.add
#print axioms YMGap.Continuum.PolynomialBiadditive.Biadditive.neg
#print axioms YMGap.Continuum.PolynomialBiadditive.Biadditive.left
#print axioms YMGap.Continuum.PolynomialBiadditive.Biadditive.right
#print axioms YMGap.Continuum.PolynomialBiadditive.Biadditive.increment
#print axioms YMGap.Continuum.PolynomialBiadditive.Biadditive.diagonal_increment
