/-
# All-order closed formula for monomial Cayley transvectants

This module completes the symbolic induction from the exact two-branch
monomial recurrence and the universal factorial/Pascal recurrence.  Every
order and every natural label is covered; the two truncating-natural
boundaries are handled explicitly rather than hidden behind positivity
assumptions.
-/

import YMGap.Continuum.SU2TransvectantFactorialRecurrence

namespace YMGap.Continuum.SU2TransvectantAllOrder

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantMonomialRecurrence
open YMGap.Continuum.SU2TransvectantFactorialRecurrence

/-- On its unique output shell, the actual order-`k` Cayley transvectant of
two monomials is exactly the closed alternating falling-factorial
coefficient. -/
theorem transvect_monomial_matches_factorial_on_shell :
    ∀ k m n i j : Nat, k ≤ i + j →
      (transvect m n k (tprod (mono i) (mono j)) (i + j - k)).eqv
        (transvectFactorialCoeff m n k i j) := by
  intro k
  induction k with
  | zero =>
      intro m n i j _
      simpa using transvect_zero_matches_factorial m n i j
  | succ k ih =>
      intro m n i j hk
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ j =>
              have hrec := transvect_succ_monomial m n k 0 (j + 1)
                (j + 1 - (k + 1))
              have hfirst :
                  (Q'.ofNat (0 * (n - (j + 1))) *
                    transvect (m - 1) (n - 1) k
                      (tprod (mono (0 - 1)) (mono (j + 1)))
                      (j + 1 - (k + 1))).eqv
                  (Q'.ofNat (0 * (n - (j + 1))) *
                    transvectFactorialCoeff (m - 1) (n - 1) k (0 - 1) (j + 1)) := by
                simp only [Nat.zero_mul, Nat.zero_sub]
                refine Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _) ?_
                exact Q'.eqv_symm (Q'.zero_mul_eqv _)
              have hsecond0 := ih (m - 1) (n - 1) 0 j (by omega)
              have hsecond :
                  (transvect (m - 1) (n - 1) k
                    (tprod (mono 0) (mono j)) (j + 1 - (k + 1))).eqv
                    (transvectFactorialCoeff (m - 1) (n - 1) k 0 j) := by
                rw [show j + 1 - (k + 1) = j - k by omega]
                simpa using hsecond0
              have hscaled := Q'.mul_eqv_congr_left
                (-(Q'.ofNat ((m - 0) * (j + 1)))) _ _ hsecond
              have hbranches := Q'.add_eqv_congr' hfirst hscaled
              refine Q'.eqv_trans _ _ _ (by simpa using hrec) ?_
              refine Q'.eqv_trans _ _ _ (by simpa using hbranches) ?_
              simpa using transvectFactorialCoeff_succ m n k 0 (j + 1)
      | succ i =>
          cases j with
          | zero =>
              have hrec := transvect_succ_monomial m n k (i + 1) 0
                (i + 1 - (k + 1))
              have hfirst0 := ih (m - 1) (n - 1) i 0 (by omega)
              have hfirst :
                  (transvect (m - 1) (n - 1) k
                    (tprod (mono i) (mono 0)) (i + 1 - (k + 1))).eqv
                    (transvectFactorialCoeff (m - 1) (n - 1) k i 0) := by
                rw [show i + 1 - (k + 1) = i - k by omega]
                exact hfirst0
              have hscaled := Q'.mul_eqv_congr_left
                (Q'.ofNat ((i + 1) * (n - 0))) _ _ hfirst
              have hsecond :
                  ((-(Q'.ofNat ((m - (i + 1)) * 0))) *
                    transvect (m - 1) (n - 1) k
                      (tprod (mono (i + 1)) (mono (0 - 1)))
                      (i + 1 - (k + 1))).eqv
                  ((-(Q'.ofNat ((m - (i + 1)) * 0))) *
                    transvectFactorialCoeff (m - 1) (n - 1) k (i + 1) (0 - 1)) := by
                simp only [Nat.mul_zero, Nat.zero_sub]
                refine Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _) ?_
                exact Q'.eqv_symm (Q'.zero_mul_eqv _)
              have hbranches := Q'.add_eqv_congr' hscaled hsecond
              refine Q'.eqv_trans _ _ _ (by simpa using hrec) ?_
              refine Q'.eqv_trans _ _ _ (by simpa using hbranches) ?_
              exact transvectFactorialCoeff_succ m n k (i + 1) 0
          | succ j =>
              have hrec := transvect_succ_monomial m n k (i + 1) (j + 1)
                ((i + 1) + (j + 1) - (k + 1))
              have hfirst0 := ih (m - 1) (n - 1) i (j + 1) (by omega)
              have hfirst :
                  (transvect (m - 1) (n - 1) k
                    (tprod (mono i) (mono (j + 1)))
                    ((i + 1) + (j + 1) - (k + 1))).eqv
                    (transvectFactorialCoeff (m - 1) (n - 1) k i (j + 1)) := by
                rw [show (i + 1) + (j + 1) - (k + 1) = i + (j + 1) - k by omega]
                exact hfirst0
              have hsecond0 := ih (m - 1) (n - 1) (i + 1) j (by omega)
              have hsecond :
                  (transvect (m - 1) (n - 1) k
                    (tprod (mono (i + 1)) (mono j))
                    ((i + 1) + (j + 1) - (k + 1))).eqv
                    (transvectFactorialCoeff (m - 1) (n - 1) k (i + 1) j) := by
                rw [show (i + 1) + (j + 1) - (k + 1) = (i + 1) + j - k by omega]
                exact hsecond0
              have hbranches := Q'.add_eqv_congr'
                (Q'.mul_eqv_congr_left (Q'.ofNat ((i + 1) * (n - (j + 1))))
                  _ _ hfirst)
                (Q'.mul_eqv_congr_left (-(Q'.ofNat ((m - (i + 1)) * (j + 1))))
                  _ _ hsecond)
              refine Q'.eqv_trans _ _ _ (by simpa using hrec) ?_
              refine Q'.eqv_trans _ _ _ hbranches ?_
              exact transvectFactorialCoeff_succ m n k (i + 1) (j + 1)

/-- Full coefficient formula, including every off-shell output index. -/
theorem transvect_monomial_factorial_formula (m n k i j s : Nat) :
    (transvect m n k (tprod (mono i) (mono j)) s).eqv
      (if s + k = i + j then transvectFactorialCoeff m n k i j else 0) := by
  by_cases hs : s + k = i + j
  · rw [if_pos hs]
    have hk : k ≤ i + j := by omega
    have hs' : s = i + j - k := by omega
    rw [hs']
    exact transvect_monomial_matches_factorial_on_shell k m n i j hk
  · rw [if_neg hs]
    exact YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_monomial_zero_offshell
      m n k i j s hs

end YMGap.Continuum.SU2TransvectantAllOrder

#print axioms YMGap.Continuum.SU2TransvectantAllOrder.transvect_monomial_matches_factorial_on_shell
#print axioms YMGap.Continuum.SU2TransvectantAllOrder.transvect_monomial_factorial_formula
