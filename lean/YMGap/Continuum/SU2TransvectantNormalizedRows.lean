/-
# Normalized output-row constancy and the binary Gram multiplier

The raw row recurrence becomes exact row constancy after multiplying by the
invariant output monomial norm.  This module proves the adjacent factorial
normalization identity, cancels the positive successor factor, propagates
constancy across the whole output degree, and sums the rows.
-/

import YMGap.Continuum.SU2TransvectantRowNormConstancy
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.SU2TransvectantNormalizedRows

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantRowNormConstancy

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

private theorem pred_succ_of_pos (d : Nat) (hd : 0 < d) : d - 1 + 1 = d := by
  omega

private theorem mkN_den_of_pred (n d : Nat) (hd : 0 < d) :
    (Q'.mkN n (d - 1)).den = d := by
  change d - 1 + 1 = d
  omega

/-- Adjacent invariant monomial norms have the exact reciprocal-binomial
cross relation. -/
theorem symMonomialNormSq_adjacent_cross (d s : Nat) (hs : s < d) :
    symMonomialNormSq d (s + 1) * Q'.ofNat (d - s) ≈
      symMonomialNormSq d s * Q'.ofNat (s + 1) := by
  unfold symMonomialNormSq
  rw [if_pos (by omega : s + 1 ≤ d), if_pos (by omega : s ≤ d)]
  have hd : 0 < tvFact d := tvFact_pos d
  have hnat :
      (tvFact (s + 1) * tvFact (d - (s + 1))) * (d - s) =
        (tvFact s * tvFact (d - s)) * (s + 1) := by
    have hds : d - s = (d - (s + 1)) + 1 := by omega
    rw [hds]
    simp only [tvFact]
    ac_rfl
  show
    (Q'.mkN (tvFact (s + 1) * tvFact (d - (s + 1))) (tvFact d - 1) *
        Q'.ofNat (d - s)).num *
      ((Q'.mkN (tvFact s * tvFact (d - s)) (tvFact d - 1) *
        Q'.ofNat (s + 1)).den : Int) =
    (Q'.mkN (tvFact s * tvFact (d - s)) (tvFact d - 1) *
        Q'.ofNat (s + 1)).num *
      ((Q'.mkN (tvFact (s + 1) * tvFact (d - (s + 1))) (tvFact d - 1) *
        Q'.ofNat (d - s)).den : Int)
  simp only [Q'.mul_num_cast, Q'.ofNat_num_cast]
  rw [Q'.mul_den_cast, Q'.mul_den_cast,
    mkN_den_of_pred _ _ hd, mkN_den_of_pred _ _ hd,
    Q'.ofNat_den_cast, Q'.ofNat_den_cast]
  simp only [Q'.mkN, Int.mul_one]
  have hint := congrArg Int.ofNat hnat
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one] at hint ⊢
  exact congrArg (fun z : Int => z * (tvFact d : Int)) hint

/-- The invariantly normalized squared norm of output row `s`. -/
def binaryNormalizedRowNorm (m n k s : Nat) : Q' :=
  symMonomialNormSq (m + n - 2 * k) s * binaryRawRowNorm m n k s

/-- Adjacent physical output rows have exactly equal normalized norms. -/
theorem binaryNormalizedRowNorm_adjacent (m n k s : Nat)
    (hm : k ≤ m) (hn : k ≤ n) (hs : s < m + n - 2 * k) :
    binaryNormalizedRowNorm m n k (s + 1) ≈
      binaryNormalizedRowNorm m n k s := by
  let d := m + n - 2 * k
  let A := symMonomialNormSq d (s + 1)
  let B := symMonomialNormSq d s
  let X := binaryRawRowNorm m n k (s + 1)
  let Y := binaryRawRowNorm m n k s
  let a := Q'.ofNat (s + 1)
  let b := Q'.ofNat (d - s)
  have hraw : a * X ≈ b * Y := by
    simpa only [a, b, X, Y, d] using
      binaryRawRowNorm_recurrence m n k s hm hn
  have hnorm : A * b ≈ B * a := by
    simpa only [A, B, a, b, d] using
      symMonomialNormSq_adjacent_cross d s hs
  have hscaled : a * (A * X) ≈ a * (B * Y) := by
    refine Q'.eqv_trans _ (A * (a * X)) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _ (A * (b * Y)) _
      (Q'.mul_eqv_congr_left A _ _ hraw) ?_
    refine Q'.eqv_trans _ ((A * b) * Y) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv A b Y)) ?_
    refine Q'.eqv_trans _ ((B * a) * Y) _
      (Q'.mul_eqv_congr_right _ _ Y hnorm) ?_
    ring_qeqv
  have hcancel := Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos s) hscaled
  simpa only [binaryNormalizedRowNorm, A, B, X, Y, a, d] using hcancel

/-- A normalized row equals every later normalized row within the physical
output window. -/
theorem binaryNormalizedRowNorm_eq_later (m n k s r : Nat)
    (hm : k ≤ m) (hn : k ≤ n)
    (hwindow : s + r ≤ m + n - 2 * k) :
    binaryNormalizedRowNorm m n k s ≈
      binaryNormalizedRowNorm m n k (s + r) := by
  induction r with
  | zero =>
      simp only [Nat.add_zero]
      exact Q'.eqv_refl _
  | succ r ih =>
      have hpre := ih (by omega)
      have hadj := binaryNormalizedRowNorm_adjacent m n k (s + r) hm hn
        (by omega)
      refine Q'.eqv_trans _ _ _ hpre ?_
      simpa only [Nat.add_assoc] using Q'.eqv_symm hadj

/-- Every physical normalized output row equals the terminal row. -/
theorem binaryNormalizedRowNorm_eq_terminal (m n k s : Nat)
    (hm : k ≤ m) (hn : k ≤ n) (hs : s ≤ m + n - 2 * k) :
    binaryNormalizedRowNorm m n k s ≈
      binaryNormalizedRowNorm m n k (m + n - 2 * k) := by
  have h := binaryNormalizedRowNorm_eq_later m n k s
    ((m + n - 2 * k) - s) hm hn (by omega)
  simpa only [show s + ((m + n - 2 * k) - s) = m + n - 2 * k by omega]
    using h

/-- Full invariant Hilbert--Schmidt Gram weight of the binary order-`k`
transvectant. -/
def binaryTransvectantGram (m n k : Nat) : Q' :=
  finSum (fun s => binaryNormalizedRowNorm m n k s)
    (m + n - 2 * k + 1)

private theorem finSum_const_eqv (a : Q') : ∀ N : Nat,
    finSum (fun _ => a) N ≈ Q'.ofNat N * a
  | 0 => by
      refine Q'.eqv_trans _ ((0 : Q') * a) _ ?_ ?_
      · exact Q'.eqv_symm (Q'.zero_mul_eqv a)
      · exact Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv
  | N + 1 => by
      have ih := finSum_const_eqv a N
      refine Q'.eqv_trans _ (Q'.ofNat N * a + a) _
        (Q'.add_eqv_congr_right _ _ a ih) ?_
      refine Q'.eqv_trans _ (Q'.ofNat N * a + 1 * a) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv a))) ?_
      refine Q'.eqv_trans _ ((Q'.ofNat N + 1) * a) _
        (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
      exact Q'.mul_eqv_congr_right _ _ a (Q'.eqv_symm (Q'.ofNat_add_eqv N 1))

/-- The complete binary Gram is the output dimension times any one normalized
row, here chosen to be the terminal row. -/
theorem binaryTransvectantGram_dimension_multiplier (m n k : Nat)
    (hm : k ≤ m) (hn : k ≤ n) :
    binaryTransvectantGram m n k ≈
      Q'.ofNat (m + n - 2 * k + 1) *
        binaryNormalizedRowNorm m n k (m + n - 2 * k) := by
  unfold binaryTransvectantGram
  refine Q'.eqv_trans _
    (finSum (fun _ => binaryNormalizedRowNorm m n k (m + n - 2 * k))
      (m + n - 2 * k + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (m + n - 2 * k + 1)
      (fun s hs => ?_)
    exact binaryNormalizedRowNorm_eq_terminal m n k s hm hn (by omega)
  · exact finSum_const_eqv _ _

end YMGap.Continuum.SU2TransvectantNormalizedRows

#print axioms YMGap.Continuum.SU2TransvectantNormalizedRows.symMonomialNormSq_adjacent_cross
#print axioms YMGap.Continuum.SU2TransvectantNormalizedRows.binaryNormalizedRowNorm_adjacent
#print axioms YMGap.Continuum.SU2TransvectantNormalizedRows.binaryNormalizedRowNorm_eq_terminal
#print axioms YMGap.Continuum.SU2TransvectantNormalizedRows.binaryTransvectantGram_dimension_multiplier
