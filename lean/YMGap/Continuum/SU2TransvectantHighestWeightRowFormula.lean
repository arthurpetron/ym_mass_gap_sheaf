/-
# Uniform highest-weight row formula for Cayley transvectants

For an order-`k` transvectant, the inputs contributing to the highest output
monomial are indexed by

  i = m-u,  j = n-k+u,  0 <= u <= k.

In the defining alternating factorial sum, the factor `(u)_r` kills every
`r>u`, while `(k-u)_(k-r)` kills every `r<u`.  Hence exactly the `r=u`
summand survives.  This file proves that support collapse uniformly and then
transfers it to the actual recursively defined Cayley transvectant using the
all-order coefficient theorem.
-/

import YMGap.Continuum.SU2TransvectantAllOrder
import YMGap.Continuum.SU2TransvectantRisingVandermonde
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.SU2TransvectantHighestWeightRowFormula

set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantAllOrder

local infix:50 " ≈ " => Q'.eqv

theorem tvFallQ_eqv_zero_of_lt (n r : Nat) (h : n < r) :
    tvFallQ n r ≈ 0 := by
  unfold tvFallQ
  rw [if_neg (by omega : ¬ r ≤ n)]
  exact Q'.eqv_refl 0

theorem tvFallQ_self_factorial (n : Nat) :
    tvFallQ n n ≈ Q'.ofNat (tvFact n) := by
  unfold tvFallQ
  rw [if_pos (Nat.le_refl n), Nat.sub_self]
  rfl

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int) =
    (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

/-- The binomial denominator is cancelled exactly by the two endpoint falling
factorials; no division or normalization choice is used. -/
theorem tvBinomQ_mul_endpoint_factorials (k u : Nat) (hu : u ≤ k) :
    tvBinomQ k u * tvFallQ u u * tvFallQ (k - u) (k - u) ≈
      Q'.ofNat (tvFact k) := by
  have hbin := tvBinomQ_eqv_choose k u hu
  have h0 := tvFallQ_self_factorial u
  have h1 := tvFallQ_self_factorial (k - u)
  have hprod :
      tvBinomQ k u * tvFallQ u u * tvFallQ (k - u) (k - u) ≈
        Q'.ofNat (PNPaths.choose k u) * Q'.ofNat (tvFact u) *
          Q'.ofNat (tvFact (k - u)) := by
    have hfirst :
        tvBinomQ k u * tvFallQ u u ≈
          Q'.ofNat (PNPaths.choose k u) * Q'.ofNat (tvFact u) :=
      Q'.eqv_trans _
        (Q'.ofNat (PNPaths.choose k u) * tvFallQ u u) _
        (Q'.mul_eqv_congr_right _ _ _ hbin)
        (Q'.mul_eqv_congr_left _ _ _ h0)
    exact Q'.eqv_trans _
      ((Q'.ofNat (PNPaths.choose k u) * Q'.ofNat (tvFact u)) *
        tvFallQ (k - u) (k - u)) _
      (Q'.mul_eqv_congr_right _ _ _ hfirst)
      (Q'.mul_eqv_congr_left _ _ _ h1)
  refine Q'.eqv_trans _ _ _ hprod ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (PNPaths.choose k u * tvFact u) *
      Q'.ofNat (tvFact (k - u))) _
    (Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_eqv _ _)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat ((PNPaths.choose k u * tvFact u) * tvFact (k - u))) _
    (ofNat_mul_eqv _ _) ?_
  have hnat : (PNPaths.choose k u * tvFact u) * tvFact (k - u) = tvFact k := by
    calc
      (PNPaths.choose k u * tvFact u) * tvFact (k - u) =
          PNPaths.choose k u * (tvFact u * tvFact (k - u)) := by ac_rfl
      _ = tvFact k := choose_mul_factorial_den k u hu
  rw [hnat]
  exact Q'.eqv_refl _

private theorem six_factor_reorder (p x A y B z : Q') :
    p * x * A * y * B * z ≈ p * (x * y * z) * A * B := by
  show (p * x * A * y * B * z).num * ((p * (x * y * z) * A * B).den : Int) =
    (p * (x * y * z) * A * B).num * ((p * x * A * y * B * z).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

private theorem finSum_all_zero (f : Nat → Q') : ∀ N,
    (∀ i, i < N → f i ≈ 0) → finSum f N ≈ 0
  | 0, _ => Q'.eqv_refl 0
  | N + 1, h => by
      change (finSum f N + f N).eqv 0
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (finSum_all_zero f N (fun i hi => h i (by omega)))
          (h N (by omega))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- A finite constructive rational sum with exactly one nonzero supported
index is equivalent to that summand. -/
theorem finSum_eqv_single (f : Nat → Q') : ∀ N u,
    u < N → (∀ r, r < N → r ≠ u → f r ≈ 0) → finSum f N ≈ f u
  | 0, u, hu, _ => by omega
  | N + 1, u, hu, hzero => by
      by_cases hutop : u = N
      · subst u
        change (finSum f N + f N).eqv (f N)
        refine Q'.eqv_trans _ (0 + f N) _
          (Q'.add_eqv_congr_right _ _ _
            (finSum_all_zero f N (fun r hr =>
              hzero r (by omega) (by omega)))) ?_
        exact Q'.eqv_of_eq (Q'.zero_add' (f N))
      · change (finSum f N + f N).eqv (f u)
        refine Q'.eqv_trans _ (f u + 0) _
          (Q'.add_eqv_congr'
            (finSum_eqv_single f N u (by omega)
              (fun r hr hru => hzero r (by omega) hru))
            (hzero N (by omega) (by omega))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' (f u))

private theorem highestRowTerm_zero_above
    (m n k u r : Nat) (hur : u < r) :
    (tvPhase r * tvBinomQ k r * tvFallQ (m - u) (k - r) *
      tvFallQ (m - (m - u)) r * tvFallQ (n - k + u) r *
      tvFallQ (n - (n - k + u)) (k - r)) ≈ 0 := by
  have hm : m - (m - u) ≤ u := by omega
  have hz : tvFallQ (m - (m - u)) r ≈ 0 :=
    tvFallQ_eqv_zero_of_lt _ _ (by omega)
  let p := tvPhase r * tvBinomQ k r * tvFallQ (m - u) (k - r)
  have h0 : p * tvFallQ (m - (m - u)) r ≈ 0 :=
    Q'.eqv_trans _ (p * 0) _
      (Q'.mul_eqv_congr_left p _ _ hz) (Q'.mul_zero_eqv p)
  have h1 : (p * tvFallQ (m - (m - u)) r) * tvFallQ (n - k + u) r ≈ 0 :=
    Q'.eqv_trans _ (0 * tvFallQ (n - k + u) r) _
      (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _ (0 * tvFallQ (n - (n - k + u)) (k - r)) _
    (Q'.mul_eqv_congr_right _ _ _ h1) (Q'.zero_mul_eqv _)

private theorem highestRowTerm_zero_below
    (m n k u r : Nat) (hn : k ≤ n) (hu : u ≤ k) (hru : r < u) :
    (tvPhase r * tvBinomQ k r * tvFallQ (m - u) (k - r) *
      tvFallQ (m - (m - u)) r * tvFallQ (n - k + u) r *
      tvFallQ (n - (n - k + u)) (k - r)) ≈ 0 := by
  have htail : n - (n - k + u) = k - u := by omega
  rw [htail]
  have hz : tvFallQ (k - u) (k - r) ≈ 0 :=
    tvFallQ_eqv_zero_of_lt _ _ (by omega)
  let p := tvPhase r * tvBinomQ k r * tvFallQ (m - u) (k - r) *
    tvFallQ (m - (m - u)) r * tvFallQ (n - k + u) r
  exact Q'.eqv_trans _ (p * 0) _
    (Q'.mul_eqv_congr_left p _ _ hz) (Q'.mul_zero_eqv p)

/-- **Single-support collapse of the all-order factorial coefficient.** -/
theorem transvectFactorialCoeff_highest_row_single
    (m n k u : Nat) (hm : k ≤ m) (hn : k ≤ n) (hu : u ≤ k) :
    transvectFactorialCoeff m n k (m - u) (n - k + u) ≈
      tvPhase u * tvBinomQ k u * tvFallQ (m - u) (k - u) *
        tvFallQ u u * tvFallQ (n - k + u) u * tvFallQ (k - u) (k - u) := by
  unfold transvectFactorialCoeff
  have hmi : m - (m - u) = u := by omega
  have hnj : n - (n - k + u) = k - u := by omega
  have hsingle := finSum_eqv_single
    (fun r =>
      tvPhase r * tvBinomQ k r * tvFallQ (m - u) (k - r) *
        tvFallQ (m - (m - u)) r * tvFallQ (n - k + u) r *
        tvFallQ (n - (n - k + u)) (k - r))
    (k + 1) u (by omega)
    (fun r hr hru => by
      rcases Nat.lt_or_gt_of_ne hru with hru' | hur
      · exact highestRowTerm_zero_below m n k u r hn hu hru'
      · exact highestRowTerm_zero_above m n k u r hur)
  simpa only [hmi, hnj] using hsingle

/-- Closed factorial-product form of the surviving highest-row coefficient. -/
theorem transvectFactorialCoeff_highest_row_closed
    (m n k u : Nat) (hm : k ≤ m) (hn : k ≤ n) (hu : u ≤ k) :
    transvectFactorialCoeff m n k (m - u) (n - k + u) ≈
      tvPhase u * Q'.ofNat (tvFact k) * tvFallQ (m - u) (k - u) *
        tvFallQ (n - k + u) u := by
  have hsingle :=
    transvectFactorialCoeff_highest_row_single m n k u hm hn hu
  have hreorder := six_factor_reorder
    (tvPhase u) (tvBinomQ k u) (tvFallQ (m - u) (k - u))
    (tvFallQ u u) (tvFallQ (n - k + u) u) (tvFallQ (k - u) (k - u))
  have hcancel := tvBinomQ_mul_endpoint_factorials k u hu
  have h0 :
      tvPhase u *
          (tvBinomQ k u * tvFallQ u u * tvFallQ (k - u) (k - u)) ≈
        tvPhase u * Q'.ofNat (tvFact k) :=
    Q'.mul_eqv_congr_left _ _ _ hcancel
  have h1 := Q'.mul_eqv_congr_right _ _ (tvFallQ (m - u) (k - u)) h0
  have h2 := Q'.mul_eqv_congr_right _ _ (tvFallQ (n - k + u) u) h1
  exact Q'.eqv_trans _ _ _ hsingle (Q'.eqv_trans _ _ _ hreorder h2)

/-- The actual Cayley map has the same uniform single-summand coefficient on
the highest output monomial. -/
theorem transvect_highest_weight_row
    (m n k u : Nat) (hm : k ≤ m) (hn : k ≤ n) (hu : u ≤ k) :
    transvect m n k (tprod (mono (m - u)) (mono (n - k + u)))
        (m + n - 2 * k) ≈
      tvPhase u * tvBinomQ k u * tvFallQ (m - u) (k - u) *
        tvFallQ u u * tvFallQ (n - k + u) u * tvFallQ (k - u) (k - u) := by
  have hshell : (m + n - 2 * k) + k = (m - u) + (n - k + u) := by omega
  have hall := transvect_monomial_factorial_formula
    m n k (m - u) (n - k + u) (m + n - 2 * k)
  rw [if_pos hshell] at hall
  exact Q'.eqv_trans _ _ _ hall
    (transvectFactorialCoeff_highest_row_single m n k u hm hn hu)

/-- Closed factorial-product coefficient for the actual Cayley map. -/
theorem transvect_highest_weight_row_closed
    (m n k u : Nat) (hm : k ≤ m) (hn : k ≤ n) (hu : u ≤ k) :
    transvect m n k (tprod (mono (m - u)) (mono (n - k + u)))
        (m + n - 2 * k) ≈
      tvPhase u * Q'.ofNat (tvFact k) * tvFallQ (m - u) (k - u) *
        tvFallQ (n - k + u) u := by
  exact Q'.eqv_trans _ _ _ (transvect_highest_weight_row m n k u hm hn hu)
    (Q'.eqv_trans _ _ _
      (six_factor_reorder
        (tvPhase u) (tvBinomQ k u) (tvFallQ (m - u) (k - u))
        (tvFallQ u u) (tvFallQ (n - k + u) u) (tvFallQ (k - u) (k - u)))
      (Q'.mul_eqv_congr_right _ _ (tvFallQ (n - k + u) u)
        (Q'.mul_eqv_congr_right _ _ (tvFallQ (m - u) (k - u))
          (Q'.mul_eqv_congr_left _ _ _
            (tvBinomQ_mul_endpoint_factorials k u hu)))))

end YMGap.Continuum.SU2TransvectantHighestWeightRowFormula

#print axioms YMGap.Continuum.SU2TransvectantHighestWeightRowFormula.tvFallQ_eqv_zero_of_lt
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightRowFormula.finSum_eqv_single
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightRowFormula.transvectFactorialCoeff_highest_row_single
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightRowFormula.transvectFactorialCoeff_highest_row_closed
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightRowFormula.transvect_highest_weight_row
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightRowFormula.transvect_highest_weight_row_closed
