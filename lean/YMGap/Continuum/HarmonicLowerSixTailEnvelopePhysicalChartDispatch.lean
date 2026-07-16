/-
# Physical projective-chart dispatch for the lower-six E8/E9 envelopes

The moving lower-six corridor lies in the union of the two exact Bernstein
charts.  This file performs only the natural-number chart split and delegates
both signs to the checked cleared-evaluator certificates.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeChartBScaling
import YMGap.Continuum.HarmonicLowerSixTailCorridor

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopePhysicalChartDispatch

open YMGap.Constructive
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeRawScaling
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeChartBScaling
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicGrowingAnchorPF2

/-- The production lower-six corridor is covered by chart A (`n² ≤ D`) and
chart B (`D ≤ n²`).  Both E8 and E9 signs are returned from the same split. -/
theorem tailEnvelopeE8E9ClearedEval_nonnegative
    {k n : Nat} (hk : 8189 ≤ k)
    (hleft : thetaWindowLeft k + 1 ≤ n)
    (hnright : n ≤ growingAnchor k) :
    (0 : Q') ≤
        tailEnvelopeE8ClearedEval (Q'.ofNat (k + 2)) (Q'.ofNat n) ∧
      (0 : Q') ≤
        tailEnvelopeE9ClearedEval (Q'.ofNat (k + 2)) (Q'.ofNat n) := by
  have hcenter : 127 ≤ thetaWindowCenter k := by
    unfold thetaWindowCenter thetaWindowLength
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hn64 : 64 ≤ n := by
    unfold thetaWindowLeft at hleft
    omega
  have hdenHigh : k + 2 ≤ 2 * (n * n) :=
    HarmonicLowerSixTailCorridor.lowerSixTail_den_le_two_sq_of_left_succ_le
      hleft
  by_cases hn2D : n * n ≤ k + 2
  · exact ⟨
      tailEnvelopeE8ClearedEval_nonnegative_chartA
        (k + 2) n hn64 hn2D hdenHigh,
      tailEnvelopeE9ClearedEval_nonnegative_chartA
        (k + 2) n hn64 hn2D hdenHigh⟩
  · have hDn2 : k + 2 ≤ n * n := by omega
    have hn91 : 91 ≤ n := by
      have hcases : 91 ≤ n ∨ n ≤ 90 := by omega
      rcases hcases with hlarge | hn90
      · exact hlarge
      · have hsquare : n * n ≤ 90 * 90 := Nat.mul_le_mul hn90 hn90
        omega
    have hn2D' : n ≤ 2 * (k + 2) := by
      simpa [growingAnchor] using hnright
    exact ⟨
      tailEnvelopeE8ClearedEval_nonnegative_chartB
        (k + 2) n hn91 hn2D' hDn2,
      tailEnvelopeE9ClearedEval_nonnegative_chartB
        (k + 2) n hn91 hn2D' hDn2⟩

#print axioms tailEnvelopeE8E9ClearedEval_nonnegative

end YMGap.Continuum.HarmonicLowerSixTailEnvelopePhysicalChartDispatch
