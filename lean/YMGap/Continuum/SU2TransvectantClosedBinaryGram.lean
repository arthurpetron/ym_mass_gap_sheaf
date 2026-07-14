/-
# Closed factorial product for the all-label binary transvectant Gram

The terminal-row bridge identifies the complete invariant Gram with the
highest-weight row.  Substituting the independently proved Chu/factorial
evaluation removes the final finite sum and exposes every exact factor.
-/

import YMGap.Continuum.SU2TransvectantTerminalRowBridge

namespace YMGap.Continuum.SU2TransvectantClosedBinaryGram

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
open YMGap.Continuum.SU2TransvectantRowNormConstancy
open YMGap.Continuum.SU2TransvectantNormalizedRows
open YMGap.Continuum.SU2TransvectantTerminalRowBridge

local infix:50 " ≈ " => Q'.eqv

/-- The common closed factorial carrier for every normalized output row. -/
def binaryRowFactorialProduct (m n k : Nat) : Q' :=
  tvFallQ m k * tvFallQ n k * Q'.ofNat (tvFact k) *
    tvFallQ (m + n - k + 1) k

/-- The raw terminal coefficient-row norm is the closed factorial product. -/
theorem binaryRawRowNorm_terminal_factorial_product (m n k : Nat)
    (hm : k ≤ m) (hn : k ≤ n) :
    binaryRawRowNorm m n k (m + n - 2 * k) ≈
      binaryRowFactorialProduct m n k := by
  refine Q'.eqv_trans _ (highestRowNorm m n k) _
    (binaryRawRowNorm_terminal_eq_highestRowNorm m n k hm hn) ?_
  simpa only [binaryRowFactorialProduct] using
    highestRowNorm_factorial_product m n k hm hn

/-- Every physical invariantly normalized output row has the same explicit
factorial product. -/
theorem binaryNormalizedRowNorm_factorial_product (m n k s : Nat)
    (hm : k ≤ m) (hn : k ≤ n) (hs : s ≤ m + n - 2 * k) :
    binaryNormalizedRowNorm m n k s ≈
      binaryRowFactorialProduct m n k := by
  refine Q'.eqv_trans _
    (binaryNormalizedRowNorm m n k (m + n - 2 * k)) _
    (binaryNormalizedRowNorm_eq_terminal m n k s hm hn hs) ?_
  refine Q'.eqv_trans _ (highestRowNorm m n k) _
    (binaryNormalizedRowNorm_terminal_eq_highestRowNorm m n k hm hn) ?_
  simpa only [binaryRowFactorialProduct] using
    highestRowNorm_factorial_product m n k hm hn

/-- **Explicit all-label closed binary Gram.**  The complete Hilbert--Schmidt
weight is the output dimension times four exact factorial/falling-factorial
factors, with no unevaluated sum or measured normalization constant. -/
theorem binaryTransvectantGram_factorial_product (m n k : Nat)
    (hm : k ≤ m) (hn : k ≤ n) :
    binaryTransvectantGram m n k ≈
      Q'.ofNat (m + n - 2 * k + 1) *
        binaryRowFactorialProduct m n k := by
  refine Q'.eqv_trans _
    (Q'.ofNat (m + n - 2 * k + 1) * highestRowNorm m n k) _
    (binaryTransvectantGram_highestRow_multiplier m n k hm hn) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (by simpa only [binaryRowFactorialProduct] using
      highestRowNorm_factorial_product m n k hm hn)

end YMGap.Continuum.SU2TransvectantClosedBinaryGram

#print axioms YMGap.Continuum.SU2TransvectantClosedBinaryGram.binaryRawRowNorm_terminal_factorial_product
#print axioms YMGap.Continuum.SU2TransvectantClosedBinaryGram.binaryNormalizedRowNorm_factorial_product
#print axioms YMGap.Continuum.SU2TransvectantClosedBinaryGram.binaryTransvectantGram_factorial_product
