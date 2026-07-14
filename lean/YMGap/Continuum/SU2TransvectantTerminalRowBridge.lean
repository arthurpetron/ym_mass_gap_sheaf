/-
# Terminal-row shell collapse for the binary transvectant Gram

The terminal output coefficient lies on the unique antidiagonal
`i+j=m+n-k`.  This module collapses the full rectangular tensor-binomial
sum onto that antidiagonal, reverses its final `k+1` entries, and identifies
the result with the already evaluated highest-weight row norm.
-/

import YMGap.Continuum.SU2TransvectantNormalizedRows

namespace YMGap.Continuum.SU2TransvectantTerminalRowBridge

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula
open YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantRowNormConstancy
open YMGap.Continuum.SU2TransvectantNormalizedRows

local infix:50 " ≈ " => Q'.eqv

/-- Pull the first term from a finite rational sum. -/
private theorem finSum_peel_left (f : Nat → Q') : ∀ n : Nat,
    finSum f (n + 1) ≈ f 0 + finSum (fun i => f (i + 1)) n
  | 0 => by
      show (0 + f 0) ≈ (f 0 + 0)
      exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _))
        (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _)))
  | n + 1 => by
      have ih := finSum_peel_left f n
      refine Q'.eqv_trans _
        ((f 0 + finSum (fun i => f (i + 1)) n) + f (n + 1)) _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      exact Q'.add_assoc_eqv _ _ _

/-- Reflection of a finite summation window. -/
private theorem finSum_reflect (f : Nat → Q') : ∀ n : Nat,
    finSum (fun i => f (n - 1 - i)) n ≈ finSum f n
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      have hpeel := finSum_peel_left (fun i => f (n - i)) n
      have htail : (fun i => f (n - (i + 1))) =
          (fun i => f (n - 1 - i)) := by
        funext i
        congr 1
        omega
      rw [htail] at hpeel
      have ih := finSum_reflect f n
      refine Q'.eqv_trans _
        (f n + finSum (fun i => f (n - 1 - i)) n) _ ?_ ?_
      · simpa only [Nat.sub_zero] using hpeel
      · refine Q'.eqv_trans _ (f n + finSum f n) _
          (Q'.add_eqv_congr_left _ _ _ ih) ?_
        exact Q'.add_comm_eqv _ _

/-- The exact summand in the terminal raw tensor-binomial row norm. -/
private def terminalTensorTerm (m n k i j : Nat) : Q' :=
  let c := transvect m n k (tprod (mono i) (mono j)) (m + n - 2 * k)
  tvBinomQ n j * (tvBinomQ m i * (c * c))

private theorem terminalTensorTerm_zero_offshell
    (m n k i j : Nat) (hs : ¬ (m + n - 2 * k) + k = i + j) :
    terminalTensorTerm m n k i j ≈ 0 := by
  have hc := transvect_monomial_zero_offshell
    m n k i j (m + n - 2 * k) hs
  unfold terminalTensorTerm
  let c := transvect m n k (tprod (mono i) (mono j)) (m + n - 2 * k)
  have hsq : c * c ≈ 0 := by
    refine Q'.eqv_trans _ (0 * c) _
      (Q'.mul_eqv_congr_right _ _ _ hc) (Q'.zero_mul_eqv _)
  have hinner : tvBinomQ m i * (c * c) ≈ 0 :=
    Q'.eqv_trans _ (tvBinomQ m i * 0) _
      (Q'.mul_eqv_congr_left _ _ _ hsq) (Q'.mul_zero_eqv _)
  exact Q'.eqv_trans _ (tvBinomQ n j * 0) _
    (Q'.mul_eqv_congr_left _ _ _ hinner) (Q'.mul_zero_eqv _)

/-- For a fixed first input coordinate, the terminal row has at most one
nonzero second coordinate. -/
private theorem terminal_inner_shell (m n k i : Nat)
    (hm : k ≤ m) (hn : k ≤ n) (hi : i < m + 1) :
    finSum (fun j => terminalTensorTerm m n k i j) (n + 1) ≈
      if m - k ≤ i then terminalTensorTerm m n k i (m + n - k - i)
      else 0 := by
  by_cases hlo : m - k ≤ i
  · rw [if_pos hlo]
    let j0 := m + n - k - i
    have hj0 : j0 < n + 1 := by
      dsimp only [j0]
      omega
    apply finSum_eqv_single _ (n + 1) j0 hj0
    intro j hj hne
    apply terminalTensorTerm_zero_offshell
    intro hshell
    apply hne
    dsimp only [j0]
    omega
  · rw [if_neg hlo]
    apply finSum_zero_on
    intro j hj
    apply terminalTensorTerm_zero_offshell
    intro hshell
    omega

private theorem terminalTensorTerm_highest (m n k u : Nat) :
    terminalTensorTerm m n k (m - u) (n - k + u) ≈
      highestRowActualTerm m n k u := by
  unfold terminalTensorTerm highestRowActualTerm highestRowActualCoeff
  let c := transvect m n k
    (tprod (mono (m - u)) (mono (n - k + u))) (m + n - 2 * k)
  have hcomm : tvBinomQ n (n - k + u) * tvBinomQ m (m - u) ≈
      tvBinomQ m (m - u) * tvBinomQ n (n - k + u) :=
    Q'.mul_comm_eqv _ _
  refine Q'.eqv_trans _
    ((tvBinomQ n (n - k + u) * tvBinomQ m (m - u)) * (c * c)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _ _ hcomm

/-- The raw terminal row is exactly the existing highest-weight row norm. -/
theorem binaryRawRowNorm_terminal_eq_highestRowNorm (m n k : Nat)
    (hm : k ≤ m) (hn : k ≤ n) :
    binaryRawRowNorm m n k (m + n - 2 * k) ≈ highestRowNorm m n k := by
  let f : Nat → Q' := fun i =>
    if m - k ≤ i then terminalTensorTerm m n k i (m + n - k - i) else 0
  let g : Nat → Q' := fun u =>
    if u ≤ k then highestRowActualTerm m n k u else 0
  unfold binaryRawRowNorm tensorBinomPair
  refine Q'.eqv_trans _ (finSum f (m + 1)) _ ?_ ?_
  · apply finSum_eqv_congr_lt
    intro i hi
    simpa only [f, terminalTensorTerm] using terminal_inner_shell m n k i hm hn hi
  · refine Q'.eqv_trans _
      (finSum (fun u => f (m + 1 - 1 - u)) (m + 1)) _
      (Q'.eqv_symm (finSum_reflect f (m + 1))) ?_
    refine Q'.eqv_trans _ (finSum g (m + 1)) _ ?_ ?_
    · apply finSum_eqv_congr_lt
      intro u hu
      have hum : u ≤ m := by omega
      by_cases huk : u ≤ k
      · rw [show m + 1 - 1 - u = m - u by omega]
        simp only [f, g, if_pos huk, if_pos (by omega : m - k ≤ m - u)]
        rw [show m + n - k - (m - u) = n - k + u by omega]
        exact terminalTensorTerm_highest m n k u
      · have hnot : ¬ m - k ≤ m - u := by omega
        rw [show m + 1 - 1 - u = m - u by omega]
        simp only [f, g, if_neg huk, if_neg hnot]
        exact Q'.eqv_refl _
    · have hlength : m + 1 = (k + 1) + (m - k) := by omega
      rw [hlength]
      have hstable := finSum_stabilizes_after_K g (k + 1)
        (fun u hu => by
          simp only [g, if_neg (by omega : ¬ u ≤ k)]) (m - k)
      rw [hstable]
      unfold highestRowNorm
      apply finSum_eqv_congr_lt
      intro u hu
      simp only [g, if_pos (by omega : u ≤ k)]
      exact Q'.eqv_refl _

/-- The invariant norm of the terminal output monomial is one. -/
theorem symMonomialNormSq_terminal (d : Nat) :
    symMonomialNormSq d d ≈ 1 := by
  unfold symMonomialNormSq
  rw [if_pos (Nat.le_refl d)]
  simp only [Nat.sub_self, tvFact, Nat.mul_one]
  exact mkN_self_pred_eqv_one (tvFact d) (tvFact_pos d)

/-- The terminal normalized row is the closed highest-weight row norm. -/
theorem binaryNormalizedRowNorm_terminal_eq_highestRowNorm (m n k : Nat)
    (hm : k ≤ m) (hn : k ≤ n) :
    binaryNormalizedRowNorm m n k (m + n - 2 * k) ≈
      highestRowNorm m n k := by
  unfold binaryNormalizedRowNorm
  refine Q'.eqv_trans _ (1 * binaryRawRowNorm m n k (m + n - 2 * k)) _
    (Q'.mul_eqv_congr_right _ _ _
      (symMonomialNormSq_terminal (m + n - 2 * k))) ?_
  refine Q'.eqv_trans _ (binaryRawRowNorm m n k (m + n - 2 * k)) _
    (Q'.one_mul_eqv _) ?_
  exact binaryRawRowNorm_terminal_eq_highestRowNorm m n k hm hn

/-- The complete binary Gram is the output dimension times the explicitly
evaluated highest-weight row. -/
theorem binaryTransvectantGram_highestRow_multiplier (m n k : Nat)
    (hm : k ≤ m) (hn : k ≤ n) :
    binaryTransvectantGram m n k ≈
      Q'.ofNat (m + n - 2 * k + 1) * highestRowNorm m n k := by
  refine Q'.eqv_trans _
    (Q'.ofNat (m + n - 2 * k + 1) *
      binaryNormalizedRowNorm m n k (m + n - 2 * k)) _
    (binaryTransvectantGram_dimension_multiplier m n k hm hn) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (binaryNormalizedRowNorm_terminal_eq_highestRowNorm m n k hm hn)

end YMGap.Continuum.SU2TransvectantTerminalRowBridge

#print axioms YMGap.Continuum.SU2TransvectantTerminalRowBridge.binaryRawRowNorm_terminal_eq_highestRowNorm
#print axioms YMGap.Continuum.SU2TransvectantTerminalRowBridge.symMonomialNormSq_terminal
#print axioms YMGap.Continuum.SU2TransvectantTerminalRowBridge.binaryNormalizedRowNorm_terminal_eq_highestRowNorm
#print axioms YMGap.Continuum.SU2TransvectantTerminalRowBridge.binaryTransvectantGram_highestRow_multiplier
