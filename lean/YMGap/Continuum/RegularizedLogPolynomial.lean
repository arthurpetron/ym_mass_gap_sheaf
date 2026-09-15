/-
# Uniform rational polynomials for the regularized logarithm series

p_N(t) = sum_{k=1}^N t*(1-t)^k/k, including t=0 and t=1.
The retained remainder (1-t)^(N+1)/(N+1) makes p_N+remainder
decrease, whereas p_N increases. Hence every later partial sum differs
from p_N by at most 1/(N+1), uniformly on [0,1]. The degree modulus
is the denominator of the positive rational tolerance.

This constructs actual UniformSequence data for the ORIGINAL transfer
calculus. No inverse or lower spectral floor is used. Identification
with an existing scalar logarithm and with the positive-time derivative
is not assumed or asserted here. The intended next operator is the
bounded regularized logarithm, not a bounded Hamiltonian -log(T2).
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear

namespace YMGap.Continuum.RegularizedLogPolynomial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BernsteinSequenceWrap (eval01 eval1m eval_ppow pow_eqv_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction (UniformSequence)

def term (t : Q') (n : Nat) : Q' := Q'.invSucc n * (t * (1-t)^(n+1))

def partialSum (t : Q') : Nat → Q'
  | 0 => 0
  | n+1 => partialSum t n + term t n

def remainder (t : Q') (n : Nat) : Q' := Q'.invSucc n * (1-t)^(n+1)

private theorem complement_le_one {t : Q'} (ht : (0 : Q') ≤ t) : 1-t ≤ 1 :=
  Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ ht (Q'.ge_of_eqv
    (poly_identity_of_normal_eq (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) (fun _ => t))))

private theorem remainder_nonnegative (t : Q') (h1 : t ≤ 1) (n : Nat) :
    (0 : Q') ≤ remainder t n :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos n))
    (Q'.pow_nonneg _ (Q'.sub_nonneg_of_le h1) _)

theorem partial_nonnegative (t : Q') (ht : (0 : Q') ≤ t) (h1 : t ≤ 1) (n : Nat) :
    (0 : Q') ≤ partialSum t n := by
  induction n with
  | zero => exact Q'.le_refl' _
  | succ n ih =>
      exact Q'.zero_le_add _ _ ih
        (Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos n))
          (Q'.mul_nonneg _ _ ht (Q'.pow_nonneg _ (Q'.sub_nonneg_of_le h1) _)))

private theorem partial_step_mono (t : Q') (ht : (0 : Q') ≤ t) (h1 : t ≤ 1) (n : Nat) :
    partialSum t n ≤ partialSum t (n+1) :=
  Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos n))
    (Q'.mul_nonneg _ _ ht (Q'.pow_nonneg _ (Q'.sub_nonneg_of_le h1) _)))

theorem partial_mono (t : Q') (ht : (0 : Q') ≤ t) (h1 : t ≤ 1) {m n : Nat} (hmn : m ≤ n) :
    partialSum t m ≤ partialSum t n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => exact Q'.le_refl' _
  | succ k ih => exact Q'.le_trans' _ _ _ ih (partial_step_mono t ht h1 (m+k))

/-- A finite cancellation, valid also at the spectral endpoint zero. -/
theorem step_remainder (t : Q') (h1 : t ≤ 1) (n : Nat) :
    term t n + remainder t (n+1) ≤ remainder t n := by
  have h := Q'.add_le_add_left (term t n) _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ ((1-t)^(n+1+1))
      (ExpNeg.invSucc_le_of_le (Nat.le_succ n))
      (Q'.pow_nonneg _ (Q'.sub_nonneg_of_le h1) _))
  refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_)
  change Q'.eqv (Q'.invSucc n * (t * (1-t)^(n+1)) +
    Q'.invSucc n * ((1-t)*(1-t)^(n+1))) (Q'.invSucc n * (1-t)^(n+1))
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 0) (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))))
    (.mul (.var 0) (.var 2)) (by decide)
    (fun | 0 => Q'.invSucc n | 1 => t | _ => (1-t)^(n+1))

private theorem decorated_step (t : Q') (h1 : t ≤ 1) (n : Nat) :
    partialSum t (n+1) + remainder t (n+1) ≤ partialSum t n + remainder t n :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _))
    (Q'.add_le_add_left _ _ _ (step_remainder t h1 n))

private theorem decorated_antitone (t : Q') (h1 : t ≤ 1) {m n : Nat} (hmn : m ≤ n) :
    partialSum t n + remainder t n ≤ partialSum t m + remainder t m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => exact Q'.le_refl' _
  | succ k ih => exact Q'.le_trans' _ _ _ (decorated_step t h1 (m+k)) ih

theorem remainder_bound (t : Q') (ht : (0 : Q') ≤ t) (h1 : t ≤ 1) (n : Nat) :
    remainder t n ≤ Q'.invSucc n :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
    (HKPos.pow_le_one (Q'.sub_nonneg_of_le h1) (complement_le_one ht) (n+1))
    (Q'.le_of_lt (Q'.invSucc_pos n))) (Q'.le_of_eqv (Q'.mul_one_eqv _))

/-- Uniform tail control, not a positive-lower-spectrum estimate. -/
theorem partial_tail (t : Q') (ht : (0 : Q') ≤ t) (h1 : t ≤ 1) {m n : Nat} (hmn : m ≤ n) :
    partialSum t n ≤ partialSum t m + Q'.invSucc m :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (remainder_nonnegative t h1 n))
    (Q'.le_trans' _ _ _ (decorated_antitone t h1 hmn)
      (Q'.add_le_add_left _ _ _ (remainder_bound t ht h1 m)))

theorem partial_le_one (t : Q') (ht : (0 : Q') ≤ t) (h1 : t ≤ 1) (n : Nat) :
    partialSum t n ≤ 1 := Q'.le_trans' _ _ _ (partial_tail t ht h1 (Nat.zero_le n))
      (by change (0 : Q') + Q'.invSucc 0 ≤ 1; decide)

def modulus (epsilon : Q') : Nat := epsilon.den

theorem partial_uniformCauchy (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hm : modulus epsilon ≤ m) (hn : modulus epsilon ≤ n)
    (t : Q') (ht : (0 : Q') ≤ t) (h1 : t ≤ 1) :
    partialSum t m ≤ partialSum t n + epsilon ∧ partialSum t n ≤ partialSum t m + epsilon := by
  have hsmall (k : Nat) (hk : modulus epsilon ≤ k) : Q'.invSucc k ≤ epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hk) (HalfPow.invSucc_den_le epsilon he)
  rcases Nat.le_total m n with hmn | hnm
  · exact ⟨Q'.le_trans' _ _ _ (partial_mono t ht h1 hmn) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)),
      Q'.le_trans' _ _ _ (partial_tail t ht h1 hmn) (Q'.add_le_add_left _ _ _ (hsmall m hm))⟩
  · exact ⟨Q'.le_trans' _ _ _ (partial_tail t ht h1 hnm) (Q'.add_le_add_left _ _ _ (hsmall n hn)),
      Q'.le_trans' _ _ _ (partial_mono t ht h1 hnm) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

def termPolynomial (n : Nat) : QPoly.Poly :=
  QPoly.pscale (Q'.invSucc n) (QPoly.pmul [0,1] (ppow [1,-1] (n+1)))

def polynomial : Nat → QPoly.Poly
  | 0 => []
  | n+1 => QPoly.padd (polynomial n) (termPolynomial n)

private theorem termPolynomial_eval (n : Nat) (t : Q') :
    Q'.eqv (QPoly.eval (termPolynomial n) t) (term t n) :=
  Q'.eqv_trans _ _ _ (QPoly.eval_pscale _ _ _) (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (QPoly.eval_pmul _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (eval01 t))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (eval_ppow _ _ _) (pow_eqv_congr (eval1m t) _))))))

theorem polynomial_eval (n : Nat) (t : Q') : Q'.eqv (QPoly.eval (polynomial n) t) (partialSum t n) := by
  induction n with
  | zero => exact Q'.eqv_refl _
  | succ n ih =>
      exact Q'.eqv_trans _ _ _ (QPoly.eval_padd _ _ _)
        (Q'.add_eqv_congr' ih (termPolynomial_eval n t))

theorem partial_one (n : Nat) : Q'.eqv (partialSum 1 n) 0 := by
  induction n with
  | zero => exact Q'.eqv_refl _
  | succ n ih =>
      have hz : Q'.eqv (term 1 n) 0 :=
        poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.const 1) (.mul (.add (.const 1) (.neg (.const 1))) (.var 1))))
          (.const 0) (by decide) (fun | 0 => Q'.invSucc n | _ => ((1 : Q')-1)^n)
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ih hz) (by decide)

theorem polynomial_one (n : Nat) : Q'.eqv (QPoly.eval (polynomial n) 1) 0 :=
  Q'.eqv_trans _ _ _ (polynomial_eval n 1) (partial_one n)

theorem polynomial_bounds (n : Nat) (t : Q') (ht : (0 : Q') ≤ t) (h1 : t ≤ 1) :
    (0 : Q') ≤ QPoly.eval (polynomial n) t ∧ QPoly.eval (polynomial n) t ≤ 1 :=
  ⟨Q'.le_trans' _ _ _ (partial_nonnegative t ht h1 n) (Q'.ge_of_eqv (polynomial_eval n t)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (polynomial_eval n t)) (partial_le_one t ht h1 n)⟩

theorem polynomial_uniformCauchy (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hm : modulus epsilon ≤ m) (hn : modulus epsilon ≤ n)
    (t : Q') (ht : (0 : Q') ≤ t) (h1 : t ≤ 1) :
    QPoly.eval (polynomial m) t ≤ QPoly.eval (polynomial n) t + epsilon ∧
    QPoly.eval (polynomial n) t ≤ QPoly.eval (polynomial m) t + epsilon := by
  have h := partial_uniformCauchy epsilon he m n hm hn t ht h1
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (polynomial_eval m t))
      (Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (polynomial_eval n t)))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (polynomial_eval n t))
      (Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (polynomial_eval m t))))⟩

/-- Actual polynomial coefficients and a uniform rate; no logarithm oracle. -/
def regularizedSequence : UniformSequence := ⟨polynomial, modulus, polynomial_uniformCauchy⟩

end YMGap.Continuum.RegularizedLogPolynomial

#print axioms YMGap.Continuum.RegularizedLogPolynomial.term
#print axioms YMGap.Continuum.RegularizedLogPolynomial.partialSum
#print axioms YMGap.Continuum.RegularizedLogPolynomial.remainder
#print axioms YMGap.Continuum.RegularizedLogPolynomial.partial_nonnegative
#print axioms YMGap.Continuum.RegularizedLogPolynomial.partial_mono
#print axioms YMGap.Continuum.RegularizedLogPolynomial.step_remainder
#print axioms YMGap.Continuum.RegularizedLogPolynomial.remainder_bound
#print axioms YMGap.Continuum.RegularizedLogPolynomial.partial_tail
#print axioms YMGap.Continuum.RegularizedLogPolynomial.partial_le_one
#print axioms YMGap.Continuum.RegularizedLogPolynomial.modulus
#print axioms YMGap.Continuum.RegularizedLogPolynomial.partial_uniformCauchy
#print axioms YMGap.Continuum.RegularizedLogPolynomial.termPolynomial
#print axioms YMGap.Continuum.RegularizedLogPolynomial.polynomial
#print axioms YMGap.Continuum.RegularizedLogPolynomial.polynomial_eval
#print axioms YMGap.Continuum.RegularizedLogPolynomial.partial_one
#print axioms YMGap.Continuum.RegularizedLogPolynomial.polynomial_one
#print axioms YMGap.Continuum.RegularizedLogPolynomial.polynomial_bounds
#print axioms YMGap.Continuum.RegularizedLogPolynomial.polynomial_uniformCauchy
#print axioms YMGap.Continuum.RegularizedLogPolynomial.regularizedSequence
