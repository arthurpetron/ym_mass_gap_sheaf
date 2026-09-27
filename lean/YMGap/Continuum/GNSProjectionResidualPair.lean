/-
# Orthogonality identity for commuting projection residuals

For commuting self-adjoint idempotents, the mixed pairing of their residuals
is the squared norm of the composed residual. This is an exact algebraic
identity and positivity statement; it asserts no uniform gap.
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

private theorem rc_sub_zero_local (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

private theorem cSub_zero_right (a : GNSCompletionSpace D) :
    D.cSub a (embedV D D.zero) = a := by
  apply eq_of_pairings_equal
  intro z
  rw [D.cinnerCompl_cSub_left, D.cinnerCompl_embedZero_left,
    rc_sub_zero_local]

/-- The orthogonal residual of an idempotent is itself idempotent. -/
theorem residual_idem (i : Index) (x : GNSCompletionSpace D) :
    P.residual i (P.residual i x) = P.residual i x := by
  change P.residual i (D.cSub x (P.op i x)) = P.residual i x
  rw [P.residual_sub, P.residual_after_own, cSub_zero_right]

/-- Commuting projection updates have commuting residual projections too. -/
theorem residual_commute_of_op_commute (i j : Index)
    (hcomm : ∀ x, P.op i (P.op j x) = P.op j (P.op i x))
    (x : GNSCompletionSpace D) :
    P.residual i (P.residual j x) = P.residual j (P.residual i x) := by
  change P.residual i (D.cSub x (P.op j x)) =
    D.cSub (P.residual i x) (P.op j (P.residual i x))
  rw [P.residual_sub, P.residual_commute i j hcomm x]

/-- The mixed residual pairing is the norm square of the composed residual. -/
theorem commuting_residual_pairing_eq_normSq (i j : Index)
    (hcomm : ∀ x, P.op i (P.op j x) = P.op j (P.op i x))
    (x : GNSCompletionSpace D) :
    D.cinnerCompl (P.residual i x) (P.residual j x) =
      normSq (P.residual i (P.residual j x)) := by
  have hcomp : P.residual j (P.residual i (P.residual j x)) =
      P.residual i (P.residual j x) := by
    rw [← P.residual_commute_of_op_commute i j hcomm (P.residual j x),
      P.residual_idem j x]
  calc
    D.cinnerCompl (P.residual i x) (P.residual j x) =
        D.cinnerCompl x (P.residual i (P.residual j x)) :=
      P.residual_adjoint i x (P.residual j x)
    _ = normSq (P.residual i (P.residual j x)) := by
      unfold normSq
      calc
        D.cinnerCompl x (P.residual i (P.residual j x)) =
            D.cinnerCompl x
              (P.residual j (P.residual i (P.residual j x))) := by
          rw [hcomp]
        _ = D.cinnerCompl (P.residual j x)
              (P.residual i (P.residual j x)) :=
          (P.residual_adjoint j x (P.residual i (P.residual j x))).symm
        _ = D.cinnerCompl
              (P.residual i (P.residual j x))
              (P.residual i (P.residual j x)) := by
          symm
          rw [P.residual_adjoint i, P.residual_idem]

/-- Positivity of the commuting residual-pair contribution in the ordinary
completed GNS inner product. No reflected OS form is used. -/
theorem commuting_residual_pairing_nonnegative (i j : Index)
    (hcomm : ∀ x, P.op i (P.op j x) = P.op j (P.op i x))
    (x : GNSCompletionSpace D) :
    RCle RCzero (D.cinnerCompl (P.residual i x) (P.residual j x)) := by
  rw [P.commuting_residual_pairing_eq_normSq i j hcomm x]
  exact D.cinner_self_nonneg _

#print axioms residual_idem
#print axioms residual_commute_of_op_commute
#print axioms commuting_residual_pairing_eq_normSq
#print axioms commuting_residual_pairing_nonnegative

end YMGap.Continuum.GNSProjectionSweep.Family
