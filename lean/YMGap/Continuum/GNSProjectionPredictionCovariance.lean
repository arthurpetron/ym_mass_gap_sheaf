/-
# The exact prediction covariance behind a signed residual pair

For two orthogonal projections with a common subprojection, the mixed
residual is a nonnegative defect square minus the covariance of their
predictions after removal of the common part. No angle or gap is assumed.
In particular, a covariance of arbitrary dense tests is not silently
identified with a residual pairing: the prediction arguments and the
positive defect are explicit.
-/

import YMGap.Continuum.GNSProjectionResidualPair
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.GNSProjectionSweep.Family

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RingNormaliser

variable {D : GNSData} {Index : Type} (P : Family D Index)

private theorem sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

private theorem sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CReal.sub_self_eqv_zero A)

private theorem inner_sub_right (x y z : GNSCompletionSpace D) :
    D.cinnerCompl x (D.cSub y z) =
      RCsub (D.cinnerCompl x y) (D.cinnerCompl x z) := by
  rw [D.cinnerCompl_comm x, D.cinnerCompl_cSub_left,
    D.cinnerCompl_comm y, D.cinnerCompl_comm z]

/-- The completed conditional covariance is the pairing of the two
residuals of that SAME projection. -/
theorem residual_pairing_covariance (k : Index) (x y : GNSCompletionSpace D) :
    D.cinnerCompl (P.residual k x) (P.residual k y) =
      RCsub (D.cinnerCompl x y) (D.cinnerCompl (P.op k x) (P.op k y)) := by
  rw [P.residual_adjoint, P.residual_idem]
  change D.cinnerCompl x (D.cSub y (P.op k y)) = _
  rw [inner_sub_right, P.adjoint k x (P.op k y), P.idem]

private theorem restore (a b c e : RC) :
    RCsub a (RCsub b c) =
      RCsub (RCsub (RCsub a (RCsub b c))
        (RCsub (RCsub b c) (RCsub b e))) (RCsub c e) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  refine Quotient.inductionOn e ?_
  intro E
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add
        (.add (.add (.var 0) (.neg (.add (.var 1) (.neg (.var 2)))))
          (.neg (.add (.add (.var 1) (.neg (.var 2)))
            (.neg (.add (.var 1) (.neg (.var 3)))))))
        (.neg (.add (.var 2) (.neg (.var 3)))))
      (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n
           | 2 => C.approx n | _ => E.approx n)))

/-- Exact signed decomposition on EVERY completed state. Here `k` is a
common subprojection; it need not be asserted to be the entire intersection.
The defect is `x - P_i x - P_j x + P_k x`. -/
theorem residual_pair_prediction_decomposition (i j k : Index)
    (hik : ∀ y, P.op i (P.op k y) = P.op k y)
    (hkj : ∀ y, P.op k (P.op j y) = P.op k y)
    (x : GNSCompletionSpace D) :
    D.cinnerCompl (P.residual i x) (P.residual j x) =
      RCsub (normSq (D.cSub (P.residual i x) (D.cSub (P.op j x) (P.op k x))))
        (RCsub (D.cinnerCompl (P.op i x) (P.op j x)) (normSq (P.op k x))) := by
  have hrx : D.cinnerCompl (P.residual i x) x = normSq (P.residual i x) := by
    rw [P.single_loss]
    change D.cinnerCompl (D.cSub x (P.op i x)) x = _
    rw [D.cinnerCompl_cSub_left, ← P.self_pairing]
    rfl
  have hrj : D.cinnerCompl (P.residual i x) (P.op j x) =
      RCsub (normSq (P.op j x)) (D.cinnerCompl (P.op i x) (P.op j x)) := by
    change D.cinnerCompl (D.cSub x (P.op i x)) (P.op j x) = _
    rw [D.cinnerCompl_cSub_left, D.cinnerCompl_comm x (P.op j x), ← P.self_pairing]
    rfl
  have hrk : D.cinnerCompl (P.residual i x) (P.op k x) = RCzero := by
    change D.cinnerCompl (D.cSub x (P.op i x)) (P.op k x) = _
    rw [D.cinnerCompl_cSub_left, P.adjoint, hik, sub_self]
  have hrv : D.cinnerCompl (P.residual i x) (D.cSub (P.op j x) (P.op k x)) =
      RCsub (normSq (P.op j x)) (D.cinnerCompl (P.op i x) (P.op j x)) := by
    rw [inner_sub_right, hrj, hrk, sub_zero]
  have hvv : normSq (D.cSub (P.op j x) (P.op k x)) =
      RCsub (normSq (P.op j x)) (normSq (P.op k x)) := by
    have h := P.single_loss k (P.op j x)
    unfold residual at h
    rw [hkj] at h
    exact h
  have hdefect :
      normSq (D.cSub (P.residual i x) (D.cSub (P.op j x) (P.op k x))) =
      RCsub
        (RCsub (normSq (P.residual i x))
          (RCsub (normSq (P.op j x)) (D.cinnerCompl (P.op i x) (P.op j x))))
        (RCsub
          (RCsub (normSq (P.op j x)) (D.cinnerCompl (P.op i x) (P.op j x)))
          (RCsub (normSq (P.op j x)) (normSq (P.op k x)))) := by
    change D.cinnerCompl _ _ = _
    rw [D.cinnerCompl_cSub_left, inner_sub_right (P.residual i x),
      inner_sub_right (D.cSub (P.op j x) (P.op k x)),
      D.cinnerCompl_comm (D.cSub (P.op j x) (P.op k x)) (P.residual i x), hrv]
    change RCsub (RCsub _ _) (RCsub _ (normSq (D.cSub (P.op j x) (P.op k x)))) = _
    rw [hvv]
    rfl
  rw [hdefect]
  change D.cinnerCompl (P.residual i x) (D.cSub x (P.op j x)) = _
  rw [inner_sub_right, hrx, hrj]
  exact restore _ _ _ _

/-- The covariance in the decomposition really is between the two
predictions centered at the SAME common projection. -/
theorem centered_prediction_pairing (i j k : Index)
    (hki : ∀ y, P.op k (P.op i y) = P.op k y)
    (hkj : ∀ y, P.op k (P.op j y) = P.op k y)
    (x : GNSCompletionSpace D) :
    D.cinnerCompl (D.cSub (P.op i x) (P.op k x))
      (D.cSub (P.op j x) (P.op k x)) =
      RCsub (D.cinnerCompl (P.op i x) (P.op j x)) (normSq (P.op k x)) := by
  have h := P.residual_pairing_covariance k (P.op i x) (P.op j x)
  unfold residual at h
  rw [hki, hkj] at h
  exact h

#print axioms residual_pairing_covariance
#print axioms residual_pair_prediction_decomposition
#print axioms centered_prediction_pairing

end YMGap.Continuum.GNSProjectionSweep.Family
