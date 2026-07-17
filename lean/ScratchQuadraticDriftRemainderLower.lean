/-
Constructive second-order Bernoulli lower bound for an increasing rational
power.  This scratch module is intentionally outside the production import
graph.
-/

import YMGap.Continuum.BulkModeCrux

namespace YMGap.Continuum.ScratchQuadraticDriftRemainderLower

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BulkModeCrux

local infix:50 " ≈ " => Q'.eqv

private theorem quadratic_lower_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "quadratic_lower_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               quadratic_lower_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one, Int.ofNat_zero];
             ac_rfl))

/-- The exact second-order Bernoulli lower bound over the constructive
rationals.  `triSum m` is the division-free binomial coefficient
`choose(m,2)`: `BulkModeCrux.triSum_closed` proves
`2 * triSum m + m ≈ m * m`.

The induction keeps the nonnegative cubic remainder
`triSum n * u^2 * u` instead of discarding it by an equality. -/
theorem qpow_one_add_quadratic_lower {u : Q'}
    (hu0 : (0 : Q') ≤ u) : ∀ m : Nat,
    (1 : Q') + Q'.ofNat m * u + triSum m * (u * u) ≤
      qpow ((1 : Q') + u) m
  | 0 => by
      exact Q'.le_of_eqv (by
        unfold triSum qpow
        quadratic_lower_ring)
  | n + 1 => by
      have hbase0 : (0 : Q') ≤ (1 : Q') + u :=
        Q'.zero_le_add _ _ (by decide) hu0
      have hmul := Q'.mul_le_mul_of_nonneg_right
        ((1 : Q') + Q'.ofNat n * u + triSum n * (u * u))
        (qpow ((1 : Q') + u) n) ((1 : Q') + u)
        (qpow_one_add_quadratic_lower hu0 n) hbase0
      have hcubic0 : (0 : Q') ≤ (triSum n * (u * u)) * u := by
        exact Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (triSum_nonneg n)
            (Q'.mul_nonneg _ _ hu0 hu0)) hu0
      have hsucc : Q'.ofNat (n + 1) ≈ Q'.ofNat n + (1 : Q') :=
        Q'.ofNat_add_eqv n 1
      have hlinear :
          Q'.ofNat (n + 1) * u ≈ (Q'.ofNat n + (1 : Q')) * u :=
        Q'.mul_eqv_congr_right _ _ u hsucc
      have htarget :
          ((1 : Q') + Q'.ofNat (n + 1) * u +
              triSum (n + 1) * (u * u)) ≈
            (1 : Q') + (Q'.ofNat n + (1 : Q')) * u +
              (triSum n + Q'.ofNat n) * (u * u) := by
        exact Q'.add_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_left (1 : Q') _ _ hlinear)
      have hexpand :
          (((1 : Q') + Q'.ofNat n * u + triSum n * (u * u)) *
              ((1 : Q') + u)) ≈
            ((1 : Q') + (Q'.ofNat n + (1 : Q')) * u +
              (triSum n + Q'.ofNat n) * (u * u)) +
                (triSum n * (u * u)) * u := by
        quadratic_lower_ring
      have hadd :
          (1 : Q') + (Q'.ofNat n + (1 : Q')) * u +
              (triSum n + Q'.ofNat n) * (u * u) ≤
            ((1 : Q') + (Q'.ofNat n + (1 : Q')) * u +
              (triSum n + Q'.ofNat n) * (u * u)) +
                (triSum n * (u * u)) * u :=
        Q'.add_le_self_of_nonneg _ _ hcubic0
      exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _
          (Q'.le_of_eqv htarget) hadd)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hexpand)) hmul)

#print axioms qpow_one_add_quadratic_lower

end YMGap.Continuum.ScratchQuadraticDriftRemainderLower
