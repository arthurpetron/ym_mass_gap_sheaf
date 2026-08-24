/-
# Oddness of the constructive direct-window logarithm

`CRealLog.logRat` is built from the odd-power `artanh` series.  This module
proves the missing representation-level oddness facts explicitly.  In
particular, the direct-window logarithm at `1/2` has approximation stream
equivalent to the negation of the `log 2` stream.  The result lets a single
direct-window exponential-inverse compiler supply the universal dyadic
`log 2` seed used by the Wilson exact-log evaluator.

No completed-real inverse law is assumed here.  Every statement is proved on
the literal rational partial sums, modulo `Q'.eqv`.
-/

import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Constructive.CRealLogOddness

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CRealLog

/-- Negating a rational base preserves its even powers and negates its odd
powers.  The two parity statements are proved together so each successor step
uses the previously established odd/even companion. -/
theorem negPow_even_odd_eqv (y : Q') : forall k : Nat,
    ((-y) ^ (2 * k)).eqv (y ^ (2 * k)) /\
    ((-y) ^ (2 * k + 1)).eqv (-(y ^ (2 * k + 1)))
  | 0 => by
      constructor
      · exact Q'.eqv_refl 1
      · exact Q'.neg_mul_eqv y 1
  | k + 1 => by
      obtain ⟨evenK, oddK⟩ := negPow_even_odd_eqv y k
      have evenNext :
          ((-y) ^ (2 * (k + 1))).eqv (y ^ (2 * (k + 1))) := by
        have hIndex : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
        rw [hIndex, Q'.pow_succ, Q'.pow_succ]
        refine Q'.eqv_trans _ ((-y) * (-(y ^ (2 * k + 1)))) _
          (Q'.mul_eqv_congr_left (-y) _ _ oddK) ?_
        refine Q'.eqv_trans _ (-(y * (-(y ^ (2 * k + 1))))) _
          (Q'.neg_mul_eqv y (-(y ^ (2 * k + 1)))) ?_
        refine Q'.eqv_trans _ (-(-(y * y ^ (2 * k + 1)))) _
          (Q'.neg_eqv_congr _ _
            (Q'.mul_neg_eqv y (y ^ (2 * k + 1)))) ?_
        exact Q'.neg_neg_eqv (y * y ^ (2 * k + 1))
      have oddNext :
          ((-y) ^ (2 * (k + 1) + 1)).eqv
            (-(y ^ (2 * (k + 1) + 1))) := by
        rw [Q'.pow_succ, Q'.pow_succ]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (-y) _ _ evenNext)
          (Q'.neg_mul_eqv y (y ^ (2 * (k + 1))))
      exact ⟨evenNext, oddNext⟩

/-- Each signed artanh term is odd in its rational argument. -/
theorem artanhTerm_neg_eqv (y : Q') (k : Nat) :
    (CRealLog.term (-y) k).eqv (-(CRealLog.term y k)) := by
  unfold CRealLog.term
  refine Q'.eqv_trans _
    ((-(y ^ (2 * k + 1))) * CRealLog.recipOdd k) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right
      ((-y) ^ (2 * k + 1)) (-(y ^ (2 * k + 1)))
      (CRealLog.recipOdd k) (negPow_even_odd_eqv y k).2
  · exact Q'.neg_mul_eqv (y ^ (2 * k + 1)) (CRealLog.recipOdd k)

/-- Every finite artanh partial sum is odd in its rational argument. -/
theorem artanhPartial_neg_eqv (y : Q') : forall n : Nat,
    (CRealLog.partialSum (-y) n).eqv
      (-(CRealLog.partialSum y n))
  | 0 => by
      change (0 : Q').eqv (-(0 : Q'))
      rfl
  | n + 1 => by
      show
        (CRealLog.partialSum (-y) n + CRealLog.term (-y) n).eqv
          (-(CRealLog.partialSum y n + CRealLog.term y n))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (artanhPartial_neg_eqv y n)
          (artanhTerm_neg_eqv y n))
        (Q'.eqv_symm
          (Q'.neg_add_eqv
            (CRealLog.partialSum y n) (CRealLog.term y n)))

/-- The exact rational `1/2` used for the reciprocal-log specialization. -/
def oneHalf : Q' := Q'.mkPos 1 2 (by decide)

theorem oneHalf_plus_one_pos : (0 : Q') < oneHalf + 1 := by decide

theorem oneHalf_lt_one : oneHalf < (1 : Q') := by decide

/-- The artanh coordinate of `1/2` is the negation of the coordinate of `2`:
`(1/2 - 1)/(1/2 + 1) = -1/3`. -/
theorem yOf_oneHalf_eqv_neg_yOf_two :
    (CRealLog.yOf oneHalf oneHalf_plus_one_pos).eqv
      (-(CRealLog.yOf (2 : Q') (by decide))) := by
  decide

/-- The direct-window certificate at `1/2`. -/
theorem yOf_oneHalf_window :
    Q'.abs (CRealLog.yOf oneHalf oneHalf_plus_one_pos) <=
      CRealLog.recipOdd 1 := by
  decide

/-- Pointwise reciprocal identity for the literal rational log streams:
`logRat(1/2)_n` is equivalent to `-log2_n` at every approximation index. -/
theorem logRat_oneHalf_approx_eqv_neg_log2_approx (stage : Nat) :
    ((CRealLog.logRat oneHalf oneHalf_plus_one_pos
      yOf_oneHalf_window).approx stage).eqv
    (-(CRealLog.log2.approx stage)) := by
  let yTwo := CRealLog.yOf (2 : Q') (by decide)
  let yHalf := CRealLog.yOf oneHalf oneHalf_plus_one_pos
  have hHalfToNeg :
      (CRealLog.partialSum yHalf stage).eqv
        (CRealLog.partialSum (-yTwo) stage) :=
    CRealLog.artanhPartial_eqv_congr
      yOf_oneHalf_eqv_neg_yOf_two stage
  have hPartial :
      (CRealLog.partialSum yHalf stage).eqv
        (-(CRealLog.partialSum yTwo stage)) :=
    Q'.eqv_trans _ _ _ hHalfToNeg
      (artanhPartial_neg_eqv yTwo stage)
  change
    (CRealLog.partialSum yHalf stage +
      CRealLog.partialSum yHalf stage).eqv
    (-(CRealLog.partialSum yTwo stage +
      CRealLog.partialSum yTwo stage))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hPartial hPartial)
    (Q'.eqv_symm
      (Q'.neg_add_eqv
        (CRealLog.partialSum yTwo stage)
        (CRealLog.partialSum yTwo stage)))

end YMGap.Constructive.CRealLogOddness

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.CRealLogOddness.negPow_even_odd_eqv
#print axioms YMGap.Constructive.CRealLogOddness.artanhTerm_neg_eqv
#print axioms YMGap.Constructive.CRealLogOddness.artanhPartial_neg_eqv
#print axioms YMGap.Constructive.CRealLogOddness.yOf_oneHalf_eqv_neg_yOf_two
#print axioms YMGap.Constructive.CRealLogOddness.yOf_oneHalf_window
#print axioms YMGap.Constructive.CRealLogOddness.logRat_oneHalf_approx_eqv_neg_log2_approx
