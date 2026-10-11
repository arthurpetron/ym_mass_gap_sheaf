/-
# Actual regularized-series values and their product law

The value here is the limit of the literal rational partial sums
  p_N(t) = sum_{k=1}^N t*(1-t)^k/k,
including both endpoints. Its approximation modulus is retained as Type-level
data. The finite product defect is between zero and 1/(N+1); this computes
the limit product law and its halving specialization without assuming a
logarithm identity or extracting a cutoff from a propositional existential.

The direct-window identification with CRealLog.logRat, and the resulting
computed binary range reduction, are separate obligations. In particular
this file does not identify its half-value with half*log2. The consumer is
the original finite entropy polynomial route, not a physical gap theorem.
-/

import YMGap.Continuum.RegularizedLogPolynomialProductDefect
import YMGap.Constructive.CRealInnerRegularity
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.RegularizedLogRationalAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RegularizedLogPolynomial
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

/-- The actual partial sums, with the existing uniform denominator modulus. -/
def value (t : Q') (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ 1) : CReal where
  approx := partialSum t
  cauchy := fun epsilon he => ⟨modulus epsilon,
    fun m n hm hn => partial_uniformCauchy epsilon he m n hm hn t ht0 ht1⟩

/-- Recoverable modulus data, not an extraction from `CReal.cauchy`. -/
def valueRegularity (t : Q') (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ 1) :
    CReal.InnerRegularity (value t ht0 ht1) where
  rate := modulus
  regular := fun epsilon he m n hm hn =>
    partial_uniformCauchy epsilon he m n hm hn t ht0 ht1

theorem value_approx (t : Q') (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ 1) (n : Nat) :
    (value t ht0 ht1).approx n = partialSum t n := rfl

theorem value_approx_bounds (t : Q') (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ 1)
    (n : Nat) :
    (0 : Q') ≤ (value t ht0 ht1).approx n ∧ (value t ht0 ht1).approx n ≤ 1 :=
  ⟨partial_nonnegative t ht0 ht1 n, partial_le_one t ht0 ht1 n⟩

private theorem partial_zero (n : Nat) : Q'.eqv (partialSum 0 n) 0 := by
  induction n with
  | zero => exact Q'.eqv_refl _
  | succ n ih =>
      have hz : Q'.eqv (term 0 n) 0 :=
        poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.const 0) (.var 1))) (.const 0) (by decide)
          (fun | 0 => Q'.invSucc n | _ => ((1 : Q')-0)^(n+1))
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ih hz) (by decide)

theorem value_zero : CReal.Equiv (value 0 (by decide) (by decide)) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv partial_zero

theorem value_one : CReal.Equiv (value 1 (by decide) (by decide)) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv partial_one

theorem product_le_one {a b : Q'} (ha1 : a ≤ 1) (hb0 : (0 : Q') ≤ b)
    (hb1 : b ≤ 1) : a*b ≤ 1 :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ b ha1 hb0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv b)) hb1)

/-- The computed approximation index for the limit product law. -/
def productLawRate (epsilon : Q') : Nat := modulus epsilon

/-- The finite defect directly supplies both limit-equality inequalities.
No convergence or product-law hypothesis is an input. -/
theorem productLaw_approx (a b : Q')
    (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1)
    (hb0 : (0 : Q') ≤ b) (hb1 : b ≤ 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : productLawRate epsilon ≤ n) :
    partialSum (a*b) n ≤ b*partialSum a n + a*partialSum b n + epsilon ∧
    b*partialSum a n + a*partialSum b n ≤ partialSum (a*b) n + epsilon := by
  have hd := RegularizedLogPolynomialProductDefect.product_defect_bounds
    a b ha0 ha1 hb0 hb1 n
  have hsmall : Q'.invSucc n ≤ epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
      (HalfPow.invSucc_den_le epsilon he)
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_sub_nonneg hd.1)
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)),
    CReal.le_add_of_sub_le (Q'.le_trans' _ _ _ hd.2 hsmall)⟩

/-- f(ab) = b*f(a) + a*f(b) for the actual regularized-series values. -/
theorem productLaw (a b : Q')
    (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1)
    (hb0 : (0 : Q') ≤ b) (hb1 : b ≤ 1) :
    CReal.Equiv
      (value (a*b) (Q'.mul_nonneg _ _ ha0 hb0) (product_le_one ha1 hb0 hb1))
      (CReal.add (CReal.mul (CReal.ofQ' b) (value a ha0 ha1))
        (CReal.mul (CReal.ofQ' a) (value b hb0 hb1))) := by
  intro epsilon he
  exact ⟨productLawRate epsilon,
    fun n hn => productLaw_approx a b ha0 ha1 hb0 hb1 epsilon he n hn⟩

/-- Actual halving law, including zero. Its half-value is not a log oracle. -/
theorem halvingLaw (t : Q') (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ 1) :
    CReal.Equiv
      (value (HalfPow.half*t) (Q'.mul_nonneg _ _ HalfPow.half_nonneg ht0)
        (product_le_one (by decide) ht0 ht1))
      (CReal.add
        (CReal.mul (CReal.ofQ' t) (value HalfPow.half HalfPow.half_nonneg (by decide)))
        (CReal.mul (CReal.ofQ' HalfPow.half) (value t ht0 ht1))) :=
  productLaw HalfPow.half t HalfPow.half_nonneg (by decide) ht0 ht1

end YMGap.Continuum.RegularizedLogRationalAlgebra

#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.value
#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.valueRegularity
#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.value_approx
#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.value_approx_bounds
#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.value_zero
#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.value_one
#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.product_le_one
#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.productLawRate
#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.productLaw_approx
#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.productLaw
#print axioms YMGap.Continuum.RegularizedLogRationalAlgebra.halvingLaw
