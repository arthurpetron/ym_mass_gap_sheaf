/-
# Difference forms and cancellation of a controlled positive normalization

The four-pairing identity transfers a physically pinned bilinear form to
squared differences. A normalization with a supplied positive rational
floor can be cancelled from eventual-order inequalities, without an inverse,
choice, a square root or a loss in the contraction constant.
-/

import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.ScaledGNSCompletion

namespace YMGap.Continuum.RCBilinearDifference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal

theorem difference_diagonal {V : Type} (subV : V → V → V) (B : V → V → RC)
    (hsub : ∀ x y z, B (subV x y) z = RCsub (B x z) (B y z))
    (hsym : ∀ x y, B x y = B y x) (x y : V) :
    B (subV x y) (subV x y) =
      RCsub (RCsub (B x x) (B x y)) (RCsub (B y x) (B y y)) := by
  rw [hsub, hsym x (subV x y), hsym y (subV x y), hsub, hsub, hsym y x, hsym x y]

theorem mul_sub (a b c : RC) :
    RCmul (RCsub a b) c = RCsub (RCmul a c) (RCmul b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv _ _))

/-- An explicit positive lower floor cancels the SAME possibly irrational
normalization from both sides, retaining the exact bound. -/
theorem cancel_positive_factor {a b normalization : CReal} (floor : Q')
    (hfloor : (0 : Q') < floor) (hlower : ∀ n, floor ≤ normalization.approx n)
    (h : leEv (CReal.mul a normalization) (CReal.mul b normalization)) : leEv a b := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h (floor * epsilon) (Q'.mul_pos hfloor hepsilon)
  refine ⟨N, fun n hn => ?_⟩
  have hlambda : (0 : Q') < normalization.approx n := Q'.pos_of_lt_of_le hfloor (hlower n)
  have hbudget := Q'.mul_le_mul_of_nonneg_right _ _ epsilon (hlower n) (Q'.le_of_lt hepsilon)
  have hstep := Q'.le_trans' _ _ _ (hN n hn) (Q'.add_le_add_left _ _ _ hbudget)
  have hproduct : normalization.approx n * a.approx n ≤
      normalization.approx n * (b.approx n + epsilon) := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ hstep (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
        (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)))))
  exact Q'.le_of_mul_le_mul_left hproduct hlambda

end YMGap.Continuum.RCBilinearDifference

#print axioms YMGap.Continuum.RCBilinearDifference.difference_diagonal
#print axioms YMGap.Continuum.RCBilinearDifference.mul_sub
#print axioms YMGap.Continuum.RCBilinearDifference.cancel_positive_factor
