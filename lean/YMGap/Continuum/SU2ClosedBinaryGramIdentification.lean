/-
# Identification of analytic and closed factorial binary Grams

The binary transvectant Gram was derived from exact normalized coefficient
rows, while `closedBinaryGram` was introduced independently as the factorial
normalization used by the signed Racah square.  This file proves that the two
objects are the same on every physical Clebsch--Gordan channel.
-/

import YMGap.Continuum.SU2OrderedRightNestedGramFactorization
import YMGap.Continuum.SU2SignedRacahSquareNormalization

namespace YMGap.Continuum.SU2ClosedBinaryGramIdentification

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantNormalizedRows
open YMGap.Continuum.SU2TransvectantClosedBinaryGram
open YMGap.Continuum.SU2SignedRacahSquareNormalization
open YMGap.Continuum.TreeGraphBoundProgress

local infix:50 " ≈ " => Q'.eqv

/-- The two independently introduced natural factorial functions coincide. -/
theorem tvFact_eq_fact : ∀ n : Nat, tvFact n = fact n
  | 0 => rfl
  | n + 1 => by
      change (n + 1) * tvFact n = (n + 1) * fact n
      rw [tvFact_eq_fact n]

/-- **All-label binary Gram identification.** -/
theorem binaryTransvectantGram_eq_closedBinaryGram
    (m n k : Nat) (hm : k ≤ m) (hn : k ≤ n) :
    binaryTransvectantGram m n k ≈
      closedBinaryGram m n (m + n - 2 * k) := by
  have hgram := binaryTransvectantGram_factorial_product m n k hm hn
  refine Q'.eqv_trans _
    (Q'.ofNat (m + n - 2 * k + 1) *
      binaryRowFactorialProduct m n k) _ hgram ?_
  have hcoupling : couplingOrder m n (m + n - 2 * k) = k := by
    unfold couplingOrder
    omega
  have hkSum : k ≤ m + n - k + 1 := by omega
  have hp0 : 0 < tvFact (m - k) := tvFact_pos _
  have hp1 : 0 < tvFact (n - k) := tvFact_pos _
  have hp2 : 0 < tvFact (m + n - 2 * k + 1) := tvFact_pos _
  unfold binaryRowFactorialProduct closedBinaryGram closedBinaryGramNum
    closedBinaryGramDen
  simp only [hcoupling]
  unfold tvFallQ
  rw [if_pos hm, if_pos hn, if_pos hkSum]
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  simp only [Q'.mkN, Q'.den]
  rw [show tvFact (m - k) - 1 + 1 = tvFact (m - k) by omega,
    show tvFact (n - k) - 1 + 1 = tvFact (n - k) by omega,
    show tvFact (m + n - k + 1 - k) - 1 + 1 =
        tvFact (m + n - k + 1 - k) by
      have := tvFact_pos (m + n - k + 1 - k)
      omega]
  rw [show m + n - k + 1 - k = m + n - 2 * k + 1 by omega]
  rw [tvFact_eq_fact m, tvFact_eq_fact n, tvFact_eq_fact k,
    tvFact_eq_fact (m - k), tvFact_eq_fact (n - k),
    tvFact_eq_fact (m + n - k + 1),
    tvFact_eq_fact (m + n - 2 * k + 1)]
  have houtFact : fact (m + n - 2 * k + 1) =
      (m + n - 2 * k + 1) * fact (m + n - 2 * k) := by
    rfl
  rw [houtFact]
  push_cast
  simp only [Int.ofNat_eq_natCast]
  ac_rfl

end YMGap.Continuum.SU2ClosedBinaryGramIdentification

#print axioms YMGap.Continuum.SU2ClosedBinaryGramIdentification.tvFact_eq_fact
#print axioms YMGap.Continuum.SU2ClosedBinaryGramIdentification.binaryTransvectantGram_eq_closedBinaryGram
