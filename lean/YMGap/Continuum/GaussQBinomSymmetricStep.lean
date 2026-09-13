/-
# The two-sided q-Pascal step for a finite symmetric Jacobi product

The complementary-index symmetry proved from the exact Euler formula turns
the original q-Pascal recurrence into its opposite orientation. Using one
step in each orientation gives

  [N+2 choose k+2]_Q = Q^(k+2) [N choose k+2]_Q
    + (1+Q^(N+1)) [N choose k+1]_Q + Q^(N-k) [N choose k]_Q.

This is the finite three-neighbor recurrence needed by the symmetric Jacobi
polynomial. The restrictions `0<Q<1` justify the previously proved
complementary-index symmetry; they are not an analytic identity assumption.
The finite symmetric product identity and quantitative limit passage are
not claimed in this module.
-/

import YMGap.Continuum.GaussQBinomEulerQuotient

namespace YMGap.Continuum.GaussQBinomSymmetricStep

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.GaussQBinom
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.GaussQBinomEulerQuotient

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

private theorem add_num (a b : Q') :
    (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl

private theorem mul_num (a b : Q') : (a * b).num = a.num * b.num := rfl

local macro "mul_add_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [add_num, Q'.add_den_cast, mul_num,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Opposite q-Pascal orientation for the ORIGINAL recursive q-binomial,
including its diagonal boundary. -/
theorem qbin_pascal_opposite {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (N k : Nat) (hk : k ≤ N) :
    qbin Q (N + 1) (k + 1)
      ≈ Q ^ (k + 1) * qbin Q N (k + 1) + qbin Q N k := by
  by_cases hd : k = N
  · subst k
    calc qbin Q (N + 1) (N + 1)
        ≈ (1 : Q') := qbin_diagonal Q (N + 1)
      _ ≈ Q ^ (N + 1) * 0 + 1 := Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _))
          (Q'.eqv_of_eq (Q'.zero_add' _)))
      _ ≈ Q ^ (N + 1) * qbin Q N (N + 1) + qbin Q N N :=
        Cheb.add_eqv_congr _ _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (qbin_out_of_range Q N (N + 1) (by omega))))
          (Q'.eqv_symm (qbin_diagonal Q N))
  · have hk' : k + 1 ≤ N := by omega
    have hm : N - k = (N - (k + 1)) + 1 := by omega
    have hleft := qbin_complement hQ0 hQ1 (N + 1) (k + 1) (by omega)
    rw [Nat.succ_sub_succ_eq_sub] at hleft
    calc qbin Q (N + 1) (k + 1)
        ≈ qbin Q (N + 1) (N - k) := hleft
      _ ≈ qbin Q N (N - k) + Q ^ (k + 1) * qbin Q N (N - (k + 1)) := by
        calc qbin Q (N + 1) (N - k)
            ≈ qbin Q (N + 1) ((N - (k + 1)) + 1) := by rw [hm]; exact Q'.eqv_refl _
          _ ≈ qbin Q N (N - k) + Q ^ (k + 1) * qbin Q N (N - (k + 1)) := by
            rw [qbin_succ_succ, ← hm, show N - (N - (k + 1)) = k + 1 by omega]
            exact Q'.eqv_refl _
      _ ≈ qbin Q N k + Q ^ (k + 1) * qbin Q N (k + 1) :=
        Cheb.add_eqv_congr _ _ _ _
          (Q'.eqv_symm (qbin_complement hQ0 hQ1 N k hk))
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (qbin_complement hQ0 hQ1 N (k + 1) hk')))
      _ ≈ Q ^ (k + 1) * qbin Q N (k + 1) + qbin Q N k := Q'.add_comm_eqv _ _

/-- Two Pascal steps, one in each orientation. The resulting middle factor
is independent of the column index k. -/
theorem qbin_two_sided_step {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (N k : Nat) (hk : k + 1 ≤ N) :
    qbin Q (N + 2) (k + 2)
      ≈ Q ^ (k + 2) * qbin Q N (k + 2)
        + (1 + Q ^ (N + 1)) * qbin Q N (k + 1)
        + Q ^ (N - k) * qbin Q N k := by
  have hpow : Q ^ (k + 2) * Q ^ (N - (k + 1)) ≈ Q ^ (N + 1) := by
    calc Q ^ (k + 2) * Q ^ (N - (k + 1))
        ≈ Q ^ ((k + 2) + (N - (k + 1))) := pow_add_eqv Q _ _
      _ ≈ Q ^ (N + 1) := by
        rw [show k + 2 + (N - (k + 1)) = N + 1 by omega]
        exact Q'.eqv_refl _
  calc qbin Q (N + 2) (k + 2)
      ≈ Q ^ (k + 2) * qbin Q (N + 1) (k + 2) + qbin Q (N + 1) (k + 1) :=
        qbin_pascal_opposite hQ0 hQ1 (N + 1) (k + 1) (by omega)
    _ ≈ Q ^ (k + 2) * (qbin Q N (k + 2) + Q ^ (N - (k + 1)) * qbin Q N (k + 1))
          + (qbin Q N (k + 1) + Q ^ (N - k) * qbin Q N k) := Q'.eqv_refl _
    _ ≈ Q ^ (k + 2) * qbin Q N (k + 2)
          + (1 + Q ^ (k + 2) * Q ^ (N - (k + 1))) * qbin Q N (k + 1)
          + Q ^ (N - k) * qbin Q N k := by mul_add_ring
    _ ≈ Q ^ (k + 2) * qbin Q N (k + 2)
          + (1 + Q ^ (N + 1)) * qbin Q N (k + 1)
          + Q ^ (N - k) * qbin Q N k :=
      Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ hpow)))

/-- Centered indices expose the three neighbors used by multiplication
with the next Jacobi quadratic. The center N=0 is a separate base case. -/
theorem centered_qbin_step {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (N j : Nat) (hN : 0 < N) (hj : j ≤ N) :
    qbin Q ((N + 1) + (N + 1)) ((N + 1) + j)
      ≈ Q ^ (N + j + 1) * qbin Q (N + N) (N + j + 1)
        + (1 + Q ^ (N + N + 1)) * qbin Q (N + N) (N + j)
        + Q ^ (N + 1 - j) * qbin Q (N + N) (N + j - 1) := by
  have h := qbin_two_sided_step hQ0 hQ1 (N + N) (N + j - 1) (by omega)
  rw [show N + j - 1 + 1 = N + j by omega,
    show N + j - 1 + 2 = N + j + 1 by omega,
    show N + N - (N + j - 1) = N + 1 - j by omega] at h
  rw [show (N + 1) + (N + 1) = N + N + 2 by omega,
    show (N + 1) + j = N + j + 1 by omega]
  exact h

end YMGap.Continuum.GaussQBinomSymmetricStep

#print axioms YMGap.Continuum.GaussQBinomSymmetricStep.qbin_pascal_opposite
#print axioms YMGap.Continuum.GaussQBinomSymmetricStep.qbin_two_sided_step
#print axioms YMGap.Continuum.GaussQBinomSymmetricStep.centered_qbin_step
