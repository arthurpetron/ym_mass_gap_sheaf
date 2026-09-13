/-
# Literal weighted polynomial sums: exact recombination and coefficient bounds

Splitting a coefficient into a and 1-a gives a coefficient-level identity.
The deficit is represented by its actual weighted terms, not an unreduced
syntactic subtraction containing two copies of the original polynomial.
Termwise absolute weight bounds control the syntactic coefficient L1 of
the sum. All variables are retained; no Haar factorization is used.
-/

import YMGap.Continuum.PolynomialProductRemainder

namespace YMGap.Continuum.PolynomialWeightedSumBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2HeatCharacterPolynomialMajorant

local infix:50 " ≈ " => Q'.eqv

theorem sum_append {A : Type} (f : A → RatPoly) : ∀ xs ys : List A,
    finitePolySum f (xs ++ ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | _ :: xs, ys => by simp only [List.cons_append, finitePolySum, sum_append f xs ys, polyAdd, List.append_assoc]

theorem sum_map {A B : Type} (f : B → RatPoly) (g : A → B) : ∀ xs : List A,
    finitePolySum f (xs.map g) = finitePolySum (fun x => f (g x)) xs
  | [] => rfl
  | _ :: xs => by simp only [List.map_cons, finitePolySum, sum_map f g xs]

theorem sum_range_add (f : Nat → RatPoly) (J L : Nat) :
    finitePolySum f (List.range (J + L)) =
      polyAdd (finitePolySum f (List.range J)) (finitePolySum (fun i => f (J + i)) (List.range L)) := by
  rw [List.range_add, sum_append, sum_map]

private theorem weight_deficit (a : Q') : a + (1 + -a) ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
      (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv a))
          (QPoly.q_add_zero_eqv 1))))

/-- Exact coefficient recombination, for arbitrary rational weights. -/
theorem weighted_recombine {A : Type} (f : A → RatPoly) (a : A → Q') : ∀ ids : List A,
    RatPolyCoeffEqv
      (polyAdd (finitePolySum (fun i => polySmul (a i) (f i)) ids)
        (finitePolySum (fun i => polySmul (1 + -(a i)) (f i)) ids))
      (finitePolySum f ids)
  | [] => RatPolyCoeffEqv.refl _
  | i :: ids => (RatPolyCoeffEqv.four_add_swap _ _ _ _).trans
      (((RatPolyCoeffEqv.add_smul_same _ _ _).trans
        ((RatPolyCoeffEqv.smul_coefficient (weight_deficit (a i)) (f i)).trans
          (RatPolyCoeffEqv.one_smul _))).add (weighted_recombine f a ids))

/-- Coefficient-L1 control on the actual weighted sum, including overlapping
variables and repeated monomials. It is not a norm of a quotient class. -/
theorem weighted_coefficientL1_le {A : Type} (f : A → RatPoly) (a : A → Q') (c : Q') :
    ∀ ids : List A, (∀ i, i ∈ ids → Q'.abs (a i) ≤ c) →
    polynomialCoefficientL1 (finitePolySum (fun i => polySmul (a i) (f i)) ids)
      ≤ c * polynomialCoefficientL1 (finitePolySum f ids)
  | [], _ => Q'.ge_of_eqv (Q'.mul_zero_eqv c)
  | i :: ids, ha => by
      have hh : polynomialCoefficientL1 (polySmul (a i) (f i)) ≤ c * polynomialCoefficientL1 (f i) :=
        Q'.le_trans' _ _ _ (polynomialCoefficientL1_smul_le _ _)
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (ha i List.mem_cons_self) (polynomialCoefficientL1_nonnegative _))
      have ht := weighted_coefficientL1_le f a c ids (fun j hj => ha j (List.mem_cons_of_mem i hj))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (coefficientL1_add _ _))
        (Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 hh ht)
          (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (coefficientL1_add _ _))))))

theorem weighted_coefficientL1_le_one {A : Type} (f : A → RatPoly) (a : A → Q')
    (ids : List A) (ha : ∀ i, i ∈ ids → Q'.abs (a i) ≤ (1 : Q')) :
    polynomialCoefficientL1 (finitePolySum (fun i => polySmul (a i) (f i)) ids)
      ≤ polynomialCoefficientL1 (finitePolySum f ids) :=
  Q'.le_trans' _ _ _ (weighted_coefficientL1_le f a 1 ids ha) (Q'.le_of_eqv (Q'.one_mul_eqv _))

end YMGap.Continuum.PolynomialWeightedSumBounds

#print axioms YMGap.Continuum.PolynomialWeightedSumBounds.sum_append
#print axioms YMGap.Continuum.PolynomialWeightedSumBounds.sum_map
#print axioms YMGap.Continuum.PolynomialWeightedSumBounds.sum_range_add
#print axioms YMGap.Continuum.PolynomialWeightedSumBounds.weighted_recombine
#print axioms YMGap.Continuum.PolynomialWeightedSumBounds.weighted_coefficientL1_le
#print axioms YMGap.Continuum.PolynomialWeightedSumBounds.weighted_coefficientL1_le_one
