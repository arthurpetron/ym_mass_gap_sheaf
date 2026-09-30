/-
# Minimum distance to a completed projection's fixed space

For a self-adjoint idempotent, its residual is the orthogonal projection onto
the complement of its range. Therefore the residual norm is no larger than
the distance to any fixed vector. This is an exact Hilbert-space comparison;
it asserts no quantitative lower bound on the residual for arbitrary vectors.
-/

import YMGap.Continuum.GNSProjectionSweep

namespace YMGap.Continuum.GNSProjectionSweep.Family

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSProjectionSweep

variable {D : GNSData} {Index : Type} (P : Family D Index)

private theorem rc_sub_zero_distance (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

private theorem cSub_zero_right_distance (x : GNSCompletionSpace D) :
    D.cSub x (embedV D D.zero) = x := by
  apply eq_of_pairings_equal
  intro z
  rw [D.cinnerCompl_cSub_left, D.cinnerCompl_embedZero_left,
    rc_sub_zero_distance]

/-- A fixed vector has zero residual. -/
theorem residual_eq_zero_of_fixed (i : Index) (y : GNSCompletionSpace D)
    (hy : P.op i y = y) :
    P.residual i y = embedV D D.zero := by
  rw [← hy]
  exact P.residual_after_own i y

/-- Subtracting a vector fixed by `P.op i` does not change the `i`-residual. -/
theorem residual_sub_fixed (i : Index) (x y : GNSCompletionSpace D)
    (hy : P.op i y = y) :
    P.residual i (D.cSub x y) = P.residual i x := by
  rw [P.residual_sub, P.residual_eq_zero_of_fixed i y hy,
    cSub_zero_right_distance]

/-- The residual norm is the minimum distance to the fixed space: for every
fixed `y`, `||(I-P_i)x||² ≤ ||x-y||²` on the same completed carrier. -/
theorem residual_distance_minimum (i : Index) (x y : GNSCompletionSpace D)
    (hy : P.op i y = y) :
    RCle (normSq (P.residual i x)) (normSq (D.cSub x y)) := by
  rw [← P.residual_sub_fixed i x y hy]
  exact P.residual_norm i (D.cSub x y)

#print axioms residual_eq_zero_of_fixed
#print axioms residual_sub_fixed
#print axioms residual_distance_minimum

end YMGap.Continuum.GNSProjectionSweep.Family
