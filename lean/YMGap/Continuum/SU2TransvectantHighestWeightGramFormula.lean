/-
# Normalized highest-weight Gram row for all Cayley transvectants

This module combines the actual highest-row Cayley coefficient with the exact
input monomial normalization.  The squared normalized summand factors as

  (m)_k (n)_k (k!)^2 C(m-u,k-u) C(n-k+u,u).

Thus the only `u`-dependence is precisely the Chu kernel already collapsed by
`SU2TransvectantRisingVandermonde`.
-/

import YMGap.Continuum.SU2TransvectantHighestWeightRowFormula
import YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.SU2TransvectantHighestWeightGramFormula

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2TransvectantRisingVandermonde
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula

local infix:50 " ≈ " => Q'.eqv

private theorem pred_succ_of_pos (d : Nat) (hd : 0 < d) : d - 1 + 1 = d := by
  omega

/-- Every Cayley sign squares to one. -/
theorem tvPhase_mul_self (u : Nat) : tvPhase u * tvPhase u ≈ 1 := by
  unfold tvPhase
  by_cases h : u % 2 = 0
  · rw [if_pos h]
    exact Q'.mul_one_eqv 1
  · rw [if_neg h]
    decide

/-! ## Pointwise normalized factorial cancellation -/

/-- The unsigned factorial carrier of the normalized highest-row square. -/
def highestRowUnsignedTerm (m n k u : Nat) : Q' :=
  tvBinomQ m (m - u) * tvBinomQ n (n - k + u) *
    ((Q'.ofNat (tvFact k) * tvFallQ (m - u) (k - u) *
        tvFallQ (n - k + u) u) *
      (Q'.ofNat (tvFact k) * tvFallQ (m - u) (k - u) *
        tvFallQ (n - k + u) u))

/-- The `u`-independent factorial constant multiplying the Chu kernel. -/
def highestRowConstant (m n k : Nat) : Q' :=
  tvFallQ m k * tvFallQ n k *
    (Q'.ofNat (tvFact k) * Q'.ofNat (tvFact k))

/-- **Exact pointwise normalized row factorization.**  This is proved by
cross-multiplying the positive factorial denominators. -/
theorem highestRowUnsignedTerm_factor (m n k u : Nat)
    (hm : k ≤ m) (hn : k ≤ n) (hu : u ≤ k) :
    highestRowUnsignedTerm m n k u ≈
      highestRowConstant m n k *
        (tvBinomQ (m - u) (k - u) * tvBinomQ (n - k + u) u) := by
  unfold highestRowUnsignedTerm highestRowConstant tvBinomQ tvFallQ
  rw [if_pos (by omega : m - u ≤ m)]
  rw [if_pos (by omega : n - k + u ≤ n)]
  rw [if_pos (by omega : k - u ≤ m - u)]
  rw [if_pos (by omega : u ≤ n - k + u)]
  rw [if_pos hm, if_pos hn]
  rw [if_pos (by omega : k - u ≤ m - u)]
  rw [if_pos (by omega : u ≤ n - k + u)]
  have h1 := Nat.mul_pos (tvFact_pos (m - u)) (tvFact_pos (m - (m - u)))
  have h2 := Nat.mul_pos (tvFact_pos (n - k + u))
    (tvFact_pos (n - (n - k + u)))
  have h3 := tvFact_pos (m - u - (k - u))
  have h4 := tvFact_pos (n - k + u - u)
  have h5 := tvFact_pos (m - k)
  have h6 := tvFact_pos (n - k)
  have h7 := Nat.mul_pos (tvFact_pos (k - u))
    (tvFact_pos (m - u - (k - u)))
  have h8 := Nat.mul_pos (tvFact_pos u) (tvFact_pos (n - k + u - u))
  show
    (Q'.mkN (tvFact m) (tvFact (m - u) * tvFact (m - (m - u)) - 1) *
        Q'.mkN (tvFact n)
          (tvFact (n - k + u) * tvFact (n - (n - k + u)) - 1) *
        ((Q'.ofNat (tvFact k) *
            Q'.mkN (tvFact (m - u)) (tvFact (m - u - (k - u)) - 1) *
            Q'.mkN (tvFact (n - k + u)) (tvFact (n - k + u - u) - 1)) *
          (Q'.ofNat (tvFact k) *
            Q'.mkN (tvFact (m - u)) (tvFact (m - u - (k - u)) - 1) *
            Q'.mkN (tvFact (n - k + u)) (tvFact (n - k + u - u) - 1)))).num *
      ((Q'.mkN (tvFact m) (tvFact (m - k) - 1) *
          Q'.mkN (tvFact n) (tvFact (n - k) - 1) *
          (Q'.ofNat (tvFact k) * Q'.ofNat (tvFact k)) *
          (Q'.mkN (tvFact (m - u))
              (tvFact (k - u) * tvFact (m - u - (k - u)) - 1) *
            Q'.mkN (tvFact (n - k + u))
              (tvFact u * tvFact (n - k + u - u) - 1))).den : Int) =
    (Q'.mkN (tvFact m) (tvFact (m - k) - 1) *
        Q'.mkN (tvFact n) (tvFact (n - k) - 1) *
        (Q'.ofNat (tvFact k) * Q'.ofNat (tvFact k)) *
        (Q'.mkN (tvFact (m - u))
            (tvFact (k - u) * tvFact (m - u - (k - u)) - 1) *
          Q'.mkN (tvFact (n - k + u))
            (tvFact u * tvFact (n - k + u - u) - 1))).num *
      ((Q'.mkN (tvFact m) (tvFact (m - u) * tvFact (m - (m - u)) - 1) *
          Q'.mkN (tvFact n)
            (tvFact (n - k + u) * tvFact (n - (n - k + u)) - 1) *
          ((Q'.ofNat (tvFact k) *
              Q'.mkN (tvFact (m - u)) (tvFact (m - u - (k - u)) - 1) *
              Q'.mkN (tvFact (n - k + u)) (tvFact (n - k + u - u) - 1)) *
            (Q'.ofNat (tvFact k) *
              Q'.mkN (tvFact (m - u)) (tvFact (m - u - (k - u)) - 1) *
              Q'.mkN (tvFact (n - k + u)) (tvFact (n - k + u - u) - 1)))).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  simp only [Q'.mkN, Q'.den]
  rw [pred_succ_of_pos _ h3, pred_succ_of_pos _ h4,
    pred_succ_of_pos _ h5, pred_succ_of_pos _ h6,
    pred_succ_of_pos _ h1, pred_succ_of_pos _ h2,
    pred_succ_of_pos _ h7, pred_succ_of_pos _ h8]
  have hm0 : m - (m - u) = u := by omega
  have hn0 : n - (n - k + u) = k - u := by omega
  have hm1 : m - u - (k - u) = m - k := by omega
  have hn1 : n - k + u - u = n - k := by omega
  rw [hm0, hn0, hm1, hn1]
  push_cast
  simp only [Int.ofNat_eq_natCast, Int.one_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-! ## The actual normalized row and its Chu collapse -/

def highestRowActualCoeff (m n k u : Nat) : Q' :=
  transvect m n k (tprod (mono (m - u)) (mono (n - k + u)))
    (m + n - 2 * k)

def highestRowActualTerm (m n k u : Nat) : Q' :=
  tvBinomQ m (m - u) * tvBinomQ n (n - k + u) *
    (highestRowActualCoeff m n k u * highestRowActualCoeff m n k u)

def highestRowNorm (m n k : Nat) : Q' :=
  finSum (highestRowActualTerm m n k) (k + 1)

private theorem signed_square_eq_unsigned (u : Nat) (F : Q') :
    (tvPhase u * F) * (tvPhase u * F) ≈ F * F := by
  refine Q'.eqv_trans _ ((tvPhase u * tvPhase u) * (F * F)) _
    (YMGap.Continuum.RingNormaliser.q_mul4_swap _ _ _ _) ?_
  refine Q'.eqv_trans _ (1 * (F * F)) _
    (Q'.mul_eqv_congr_right _ _ _ (tvPhase_mul_self u)) ?_
  exact Q'.one_mul_eqv _

/-- The coefficient theorem removes the Cayley sign after squaring, so the
actual normalized summand is the unsigned factorial carrier above. -/
theorem highestRowActualTerm_eq_unsigned (m n k u : Nat)
    (hm : k ≤ m) (hn : k ≤ n) (hu : u ≤ k) :
    highestRowActualTerm m n k u ≈ highestRowUnsignedTerm m n k u := by
  let F := Q'.ofNat (tvFact k) * tvFallQ (m - u) (k - u) *
    tvFallQ (n - k + u) u
  have hc : highestRowActualCoeff m n k u ≈ tvPhase u * F := by
    have hbase : highestRowActualCoeff m n k u ≈
        tvPhase u * Q'.ofNat (tvFact k) * tvFallQ (m - u) (k - u) *
          tvFallQ (n - k + u) u := by
      simpa only [highestRowActualCoeff] using
        transvect_highest_weight_row_closed m n k u hm hn hu
    have hfirst :
        tvPhase u * Q'.ofNat (tvFact k) * tvFallQ (m - u) (k - u) ≈
          tvPhase u * (Q'.ofNat (tvFact k) * tvFallQ (m - u) (k - u)) :=
      Q'.mul_assoc_eqv _ _ _
    refine Q'.eqv_trans _ _ _ hbase ?_
    refine Q'.eqv_trans _
      (tvPhase u * (Q'.ofNat (tvFact k) * tvFallQ (m - u) (k - u)) *
        tvFallQ (n - k + u) u) _
      (Q'.mul_eqv_congr_right _ _ _ hfirst) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hs0 :
      highestRowActualCoeff m n k u * highestRowActualCoeff m n k u ≈
        (tvPhase u * F) * (tvPhase u * F) := by
    exact Q'.eqv_trans _
      ((tvPhase u * F) * highestRowActualCoeff m n k u) _
      (Q'.mul_eqv_congr_right _ _ _ hc)
      (Q'.mul_eqv_congr_left _ _ _ hc)
  have hs :
      highestRowActualCoeff m n k u * highestRowActualCoeff m n k u ≈ F * F :=
    Q'.eqv_trans _ _ _ hs0 (signed_square_eq_unsigned u F)
  unfold highestRowActualTerm highestRowUnsignedTerm
  exact Q'.mul_eqv_congr_left
    (tvBinomQ m (m - u) * tvBinomQ n (n - k + u)) _ _ hs

/-- **Actual pointwise Gram summand factorization.** -/
theorem highestRowActualTerm_factor (m n k u : Nat)
    (hm : k ≤ m) (hn : k ≤ n) (hu : u ≤ k) :
    highestRowActualTerm m n k u ≈
      highestRowConstant m n k *
        (tvBinomQ (m - u) (k - u) * tvBinomQ (n - k + u) u) :=
  Q'.eqv_trans _ _ _
    (highestRowActualTerm_eq_unsigned m n k u hm hn hu)
    (highestRowUnsignedTerm_factor m n k u hm hn hu)

/-- **Closed normalized highest-row Gram norm.**  The full finite row of the
actual Cayley transvectant collapses to one factorial product times one
binomial coefficient. -/
theorem highestRowNorm_closed (m n k : Nat) (hm : k ≤ m) (hn : k ≤ n) :
    highestRowNorm m n k ≈
      highestRowConstant m n k * tvBinomQ (m + n - k + 1) k := by
  unfold highestRowNorm
  have hterms :
      finSum (highestRowActualTerm m n k) (k + 1) ≈
        finSum (fun u => highestRowConstant m n k *
          (tvBinomQ (m - u) (k - u) * tvBinomQ (n - k + u) u)) (k + 1) := by
    refine finSum_eqv_congr_lt _ _ (k + 1) (fun u hu => ?_)
    exact highestRowActualTerm_factor m n k u hm hn (by omega)
  refine Q'.eqv_trans _ _ _ hterms ?_
  refine Q'.eqv_trans _
    (highestRowConstant m n k * transvectChuSumQ m n k) _
    (Q'.eqv_symm (const_mul_finSum
      (fun u => tvBinomQ (m - u) (k - u) * tvBinomQ (n - k + u) u)
      (highestRowConstant m n k) (k + 1))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (transvectChuVandermondeQ m n k hm hn)

theorem highestRowNorm_closed_expanded (m n k : Nat) (hm : k ≤ m) (hn : k ≤ n) :
    highestRowNorm m n k ≈
      tvFallQ m k * tvFallQ n k *
        (Q'.ofNat (tvFact k) * Q'.ofNat (tvFact k)) *
          tvBinomQ (m + n - k + 1) k := by
  simpa only [highestRowConstant] using highestRowNorm_closed m n k hm hn

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int) =
    (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

theorem tvFallQ_eqv_fallingNat (N r : Nat) (hr : r ≤ N) :
    tvFallQ N r ≈ Q'.ofNat (tvFallingNat N r) := by
  unfold tvFallQ
  rw [if_pos hr]
  have hD : 0 < tvFact (N - r) := tvFact_pos _
  have hpred : tvFact (N - r) - 1 + 1 = tvFact (N - r) := by omega
  show (tvFact N : Int) * (1 : Int) =
    (tvFallingNat N r : Int) * (((tvFact (N - r) - 1) + 1 : Nat) : Int)
  rw [hpred, Int.mul_one]
  have hnat := tvFallingNat_mul_tailFact r N hr
  have hint := congrArg Int.ofNat hnat
  push_cast at hint
  exact hint.symm

/-- Multiplying a factorial binomial by `r!` gives the falling factorial. -/
theorem tvBinomQ_mul_fact_eq_fall (N r : Nat) (hr : r ≤ N) :
    tvBinomQ N r * Q'.ofNat (tvFact r) ≈ tvFallQ N r := by
  have hbin := tvBinomQ_eqv_choose N r hr
  have hprod :
      tvBinomQ N r * Q'.ofNat (tvFact r) ≈
        Q'.ofNat (PNPaths.choose N r * tvFact r) :=
    Q'.eqv_trans _
      (Q'.ofNat (PNPaths.choose N r) * Q'.ofNat (tvFact r)) _
      (Q'.mul_eqv_congr_right _ _ _ hbin) (ofNat_mul_eqv _ _)
  refine Q'.eqv_trans _ _ _ hprod ?_
  have hnat : PNPaths.choose N r * tvFact r = tvFallingNat N r := by
    rw [Nat.mul_comm]
    exact tvFact_mul_choose_eq_falling r N hr
  rw [hnat]
  exact Q'.eqv_symm (tvFallQ_eqv_fallingNat N r hr)

/-- **Single factorial-product form of the normalized highest row.** -/
theorem highestRowNorm_factorial_product (m n k : Nat)
    (hm : k ≤ m) (hn : k ≤ n) :
    highestRowNorm m n k ≈
      tvFallQ m k * tvFallQ n k * Q'.ofNat (tvFact k) *
        tvFallQ (m + n - k + 1) k := by
  have hclosed := highestRowNorm_closed_expanded m n k hm hn
  let A := tvFallQ m k * tvFallQ n k
  let f := Q'.ofNat (tvFact k)
  let b := tvBinomQ (m + n - k + 1) k
  have hb : b * f ≈ tvFallQ (m + n - k + 1) k :=
    tvBinomQ_mul_fact_eq_fall _ _ (by omega)
  have hreorder : A * (f * f) * b ≈ A * f * (b * f) := by
    refine Q'.eqv_trans _ (A * ((f * f) * b)) _
      (Q'.mul_assoc_eqv A (f * f) b) ?_
    refine Q'.eqv_trans _ (A * (f * (f * b))) _
      (Q'.mul_eqv_congr_left A _ _ (Q'.mul_assoc_eqv f f b)) ?_
    refine Q'.eqv_trans _ (A * (f * (b * f))) _
      (Q'.mul_eqv_congr_left A _ _
        (Q'.mul_eqv_congr_left f _ _ (Q'.mul_comm_eqv f b))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv A f (b * f))
  refine Q'.eqv_trans _ (A * (f * f) * b) _ hclosed ?_
  refine Q'.eqv_trans _ (A * f * (b * f)) _ hreorder ?_
  exact Q'.mul_eqv_congr_left (A * f) _ _ hb

end YMGap.Continuum.SU2TransvectantHighestWeightGramFormula

#print axioms YMGap.Continuum.SU2TransvectantHighestWeightGramFormula.tvPhase_mul_self
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightGramFormula.highestRowUnsignedTerm_factor
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightGramFormula.highestRowActualTerm_eq_unsigned
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightGramFormula.highestRowActualTerm_factor
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightGramFormula.highestRowNorm_closed
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightGramFormula.tvBinomQ_mul_fact_eq_fall
#print axioms YMGap.Continuum.SU2TransvectantHighestWeightGramFormula.highestRowNorm_factorial_product
