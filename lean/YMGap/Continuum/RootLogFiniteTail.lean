/-
# Endpoint-safe finite tail for the original root/log comparison

The scalar partial sums here are the EXISTING rational regularized-log
polynomials.  Retaining a positive geometric remainder gives

  p_(m+1)(u) + (1-u)^(m+2)/2 <= u*(1-u) + (1-u)^2/2.

The complementary power telescope also factors the numerator of the
S-polynomial derivative into positive monomials, without a binomial row.
Multiplication by N*u^(N-1) pays the root-series side of the proposed
original derivative/log sandwich.  This is finite algebra on [0,1],
including u=0; no inverse, spectral theorem or different carrier is used.
The root-power comparison and actual completed-operator lift remain open.
-/

import YMGap.Continuum.RegularizedLogPolynomial

namespace YMGap.Continuum.RootLogFiniteTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RegularizedLogPolynomial
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

private theorem first_partial (u : Q') :
    Q'.eqv (partialSum u 1) (u*(1-u)) := by
  change Q'.eqv (0 + 1*(u*((1-u)*1))) (u*(1-u))
  exact poly_identity_of_normal_eq
    (.add (.const 0) (.mul (.const 1)
      (.mul (.var 0) (.mul (.add (.const 1) (.neg (.var 0))) (.const 1)))))
    (.mul (.var 0) (.add (.const 1) (.neg (.var 0))))
    (by decide) (fun _ => u)

private theorem half_step (u : Q') (hu : (0 : Q') ≤ u)
    (h1 : u ≤ 1) (m : Nat) :
    term u (m+1) + half*(1-u)^(m+3) ≤ half*(1-u)^(m+2) := by
  have hp := Q'.pow_nonneg (1-u) (Q'.sub_nonneg_of_le h1) (m+2)
  have ht := Q'.mul_le_mul_of_nonneg_right _ _ (u*(1-u)^(m+2))
    (ExpNeg.invSucc_le_of_le (show 1 ≤ m+1 by omega))
    (Q'.mul_nonneg _ _ hu hp)
  change term u (m+1) ≤ half*(u*(1-u)^(m+2)) at ht
  have h := Q'.add_le_add_right _ _ (half*(1-u)^(m+3)) ht
  refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_)
  rw [show m+3 = (m+2)+1 by omega, Q'.pow_succ]
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 0) (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))))
    (.mul (.var 0) (.var 2)) (by decide)
    (fun | 0 => half | 1 => u | _ => (1-u)^(m+2))

/-- A retained finite remainder, with neither a strict endpoint guard nor
an infinite-series/logarithm assumption. -/
theorem partial_retained_tail (u : Q') (hu : (0 : Q') ≤ u)
    (h1 : u ≤ 1) (m : Nat) :
    partialSum u (m+1) + half*(1-u)^(m+2) ≤
      u*(1-u) + half*(1-u)^2 := by
  induction m with
  | zero =>
      exact Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ _ (first_partial u))
  | succ m ih =>
      change (partialSum u (m+1) + term u (m+1)) +
        half*(1-u)^(m+1+2) ≤ _
      have he : m+1+2 = m+3 := by omega
      rw [he]
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _))
        (Q'.le_trans' _ _ _
          (Q'.add_le_add_left _ _ _ (half_step u hu h1 m)) ih)

/-- Removing only the NONNEGATIVE retained remainder gives the quadratic
root-series tail used in the finite sandwich. -/
theorem partial_quadratic_tail (u : Q') (hu : (0 : Q') ≤ u)
    (h1 : u ≤ 1) (m : Nat) :
    partialSum u (m+1) ≤ u*(1-u) + half*(1-u)^2 :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ half_nonneg
        (Q'.pow_nonneg _ (Q'.sub_nonneg_of_le h1) _)))
    (partial_retained_tail u hu h1 m)

/-- The computed finite positive row after cancelling the polynomial
coordinate factor in the S-derivative numerator. -/
def complementaryPowerSum (u : Q') (n : Nat) : Q' :=
  finSum (fun k => u^k+(1-u)^k) n

theorem complementaryPowerSum_nonnegative (u : Q') (hu : (0 : Q') ≤ u)
    (h1 : u ≤ 1) (n : Nat) : (0 : Q') ≤ complementaryPowerSum u n := by
  induction n with
  | zero => exact Q'.le_refl' 0
  | succ n ih =>
      exact Q'.zero_le_add _ _ ih
        (Q'.zero_le_add _ _ (Q'.pow_nonneg _ hu n)
          (Q'.pow_nonneg _ (Q'.sub_nonneg_of_le h1) n))

/-- Exact finite factorization, including the EMPTY sum at n=0 and both
endpoints. No division by u or binomial expansion is used. -/
theorem complementary_power_defect (u : Q') (n : Nat) :
    Q'.eqv (1-u^(n+1)-(1-u)^(n+1))
      (u*(1-u)*complementaryPowerSum u n) := by
  induction n with
  | zero =>
      change Q'.eqv (1-u*1-(1-u)*1) (u*(1-u)*0)
      exact poly_identity_of_normal_eq
        (.add (.add (.const 1) (.neg (.mul (.var 0) (.const 1))))
          (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.const 1))))
        (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 0)))) (.const 0))
        (by decide) (fun _ => u)
  | succ n ih =>
      have hs : Q'.eqv (1-u^(n+1+1)-(1-u)^(n+1+1))
          ((1-u^(n+1)-(1-u)^(n+1))+u*(1-u)*(u^n+(1-u)^n)) := by
        change Q'.eqv (1-u*(u*u^n)-(1-u)*((1-u)*(1-u)^n))
          ((1-u*u^n-(1-u)*(1-u)^n)+u*(1-u)*(u^n+(1-u)^n))
        exact poly_identity_of_normal_eq
          (.add (.add (.const 1) (.neg (.mul (.var 0) (.mul (.var 0) (.var 1)))))
            (.neg (.mul (.add (.const 1) (.neg (.var 0)))
              (.mul (.add (.const 1) (.neg (.var 0))) (.var 2)))))
          (.add
            (.add (.add (.const 1) (.neg (.mul (.var 0) (.var 1))))
              (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.var 2))))
            (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 0))))
              (.add (.var 1) (.var 2))))
          (by decide) (fun | 0 => u | 1 => u^n | _ => (1-u)^n)
      exact Q'.eqv_trans _ _ _ hs (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih)
        (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)))

end YMGap.Continuum.RootLogFiniteTail

#print axioms YMGap.Continuum.RootLogFiniteTail.partial_retained_tail
#print axioms YMGap.Continuum.RootLogFiniteTail.partial_quadratic_tail
#print axioms YMGap.Continuum.RootLogFiniteTail.complementaryPowerSum
#print axioms YMGap.Continuum.RootLogFiniteTail.complementaryPowerSum_nonnegative
#print axioms YMGap.Continuum.RootLogFiniteTail.complementary_power_defect
