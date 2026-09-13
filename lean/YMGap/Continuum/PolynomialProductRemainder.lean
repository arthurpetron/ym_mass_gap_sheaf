/-
# Constructive polynomial product remainders on shared variables

An explicit telescoping polynomial turns factorwise prefix-plus-remainder
certificates into a product certificate. Computed product and sensitivity
bounds control its syntactic coefficient L1 norm. All factors stay in the
same polynomial algebra; no disjointness or factorization of Haar integrals
is assumed. The bounds are finite-list computations, not analytic inputs.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
import YMGap.Continuum.SU2HeatCharacterPolynomialMajorant

namespace YMGap.Continuum.PolynomialProductRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2HeatCharacterPolynomialMajorant

local infix:50 " ≈ " => Q'.eqv

def productBound {A : Type} (B : A → Q') : List A → Q'
  | [] => 1
  | i :: ids => B i * productBound B ids

/-- Sum of the products with one factor omitted, computed recursively. -/
def productSensitivity {A : Type} (B : A → Q') : List A → Q'
  | [] => 0
  | i :: ids => B i * productSensitivity B ids + productBound B ids

theorem productBound_nonnegative {A : Type} (B : A → Q') (hB : ∀ i, (0 : Q') ≤ B i) :
    ∀ ids : List A, (0 : Q') ≤ productBound B ids
  | [] => Q'.zero_le_one
  | i :: ids => Q'.mul_nonneg _ _ (hB i) (productBound_nonnegative B hB ids)

theorem productSensitivity_nonnegative {A : Type} (B : A → Q') (hB : ∀ i, (0 : Q') ≤ B i) :
    ∀ ids : List A, (0 : Q') ≤ productSensitivity B ids
  | [] => Q'.le_refl' 0
  | i :: ids => Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (hB i) (productSensitivity_nonnegative B hB ids)) (productBound_nonnegative B hB ids)

theorem polynomialProduct_coefficientL1 {A : Type} (f : A → RatPoly) (B : A → Q')
    (hB : ∀ i, (0 : Q') ≤ B i) (hf : ∀ i, polynomialCoefficientL1 (f i) ≤ B i) :
    ∀ ids : List A, polynomialCoefficientL1 (polynomialProduct f ids) ≤ productBound B ids
  | [] => by change polynomialCoefficientL1 polyOne ≤ (1 : Q'); decide
  | i :: ids => Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (hf i) (polynomialCoefficientL1_nonnegative _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (polynomialProduct_coefficientL1 f B hB hf ids) (hB i)))

/-- The telescoping remainder uses the actual earlier/later factors. -/
def productRemainder {A : Type} (earlier later remainder : A → RatPoly) : List A → RatPoly
  | [] => polyZero
  | i :: ids => polyAdd
    (polyMul (earlier i) (productRemainder earlier later remainder ids))
    (polyMul (remainder i) (polynomialProduct later ids))

theorem polynomialProduct_remainder {A : Type} (f g r : A → RatPoly)
    (h : ∀ i, RatPolyCoeffEqv (g i) (polyAdd (f i) (r i))) : ∀ ids : List A,
    RatPolyCoeffEqv (polynomialProduct g ids)
      (polyAdd (polynomialProduct f ids) (productRemainder f g r ids))
  | [] => (RatPolyCoeffEqv.add_zero polyOne).symm
  | i :: ids => by
    have hfirst := (h i).mul_right (polynomialProduct g ids)
    rw [polyMul_add_left_exact] at hfirst
    have htail := ((polynomialProduct_remainder f g r h ids).mul_left (f i)).trans
      (RatPolyCoeffEqv.mul_add_right _ _ _)
    exact hfirst.trans ((htail.add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.add_assoc _ _ _))

private theorem left_swap (a b c : Q') : a * (b * c) ≈ b * (a * c) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) (Q'.mul_assoc_eqv b a c))

/-- A common per-factor remainder tolerance is amplified by the computed sensitivity. -/
theorem productRemainder_coefficientL1 {A : Type} (f g r : A → RatPoly) (B : A → Q')
    (hB : ∀ i, (0 : Q') ≤ B i)
    (hf : ∀ i, polynomialCoefficientL1 (f i) ≤ B i)
    (hg : ∀ i, polynomialCoefficientL1 (g i) ≤ B i)
    (δ : Q') (hδ : (0 : Q') ≤ δ) : ∀ ids : List A,
    (∀ i, i ∈ ids → polynomialCoefficientL1 (r i) ≤ δ) →
      polynomialCoefficientL1 (productRemainder f g r ids) ≤ δ * productSensitivity B ids
  | [], _ => Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv δ))
  | i :: ids, hr => by
    have hfirst := Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (hf i) (polynomialCoefficientL1_nonnegative _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (productRemainder_coefficientL1 f g r B hB hf hg δ hδ ids
            (fun j hj => hr j (List.mem_cons_of_mem i hj))) (hB i)))
    have hlast := Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (hr i List.mem_cons_self) (polynomialCoefficientL1_nonnegative _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (polynomialProduct_coefficientL1 g B hB hg ids) hδ))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (coefficientL1_add _ _))
      (Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 hfirst hlast)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (left_swap _ _ _) (Q'.eqv_refl _))
          (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)))))

end YMGap.Continuum.PolynomialProductRemainder

#print axioms YMGap.Continuum.PolynomialProductRemainder.productBound
#print axioms YMGap.Continuum.PolynomialProductRemainder.productSensitivity
#print axioms YMGap.Continuum.PolynomialProductRemainder.productBound_nonnegative
#print axioms YMGap.Continuum.PolynomialProductRemainder.productSensitivity_nonnegative
#print axioms YMGap.Continuum.PolynomialProductRemainder.polynomialProduct_coefficientL1
#print axioms YMGap.Continuum.PolynomialProductRemainder.productRemainder
#print axioms YMGap.Continuum.PolynomialProductRemainder.polynomialProduct_remainder
#print axioms YMGap.Continuum.PolynomialProductRemainder.productRemainder_coefficientL1
