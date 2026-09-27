/-
# Reverse adjoint and balanced product of one completed projection sweep

The list head acts first. Thus the adjoint of a sweep applies the same
self-adjoint projections in reverse order. The balanced product is positive
on the same completed carrier; no coercivity or strict contraction is asserted.
-/

import YMGap.Continuum.GNSCommutingSweep

namespace YMGap.Continuum.GNSProjectionSweep.Family

set_option autoImplicit false

open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient

variable {D : GNSData} {Index : Type} (P : Family D Index)

/-- The finite sweep has the reversed sweep as its pairing adjoint. -/
theorem sweep_adjoint_reverse (schedule : List Index)
    (x y : GNSCompletionSpace D) :
    D.cinnerCompl (P.sweep schedule x) y =
      D.cinnerCompl x (P.sweep schedule.reverse y) := by
  induction schedule generalizing x with
  | nil => rfl
  | cons i rest ih =>
    change D.cinnerCompl (P.sweep rest (P.op i x)) y =
      D.cinnerCompl x (P.sweep (List.reverse (i :: rest)) y)
    rw [ih (P.op i x), P.adjoint, List.reverse_cons, P.sweep_append]
    rfl

/-- The actual completed operator `S* S` for this finite sweep. -/
def balanced (schedule : List Index) (x : GNSCompletionSpace D) :
    GNSCompletionSpace D :=
  P.sweep schedule.reverse (P.sweep schedule x)

theorem balanced_pairing (schedule : List Index)
    (x y : GNSCompletionSpace D) :
    D.cinnerCompl (P.balanced schedule x) y =
      D.cinnerCompl (P.sweep schedule x) (P.sweep schedule y) := by
  unfold balanced
  rw [P.sweep_adjoint_reverse schedule.reverse,
    List.reverse_reverse]

theorem balanced_selfAdjoint (schedule : List Index)
    (x y : GNSCompletionSpace D) :
    D.cinnerCompl (P.balanced schedule x) y =
      D.cinnerCompl x (P.balanced schedule y) := by
  calc
    D.cinnerCompl (P.balanced schedule x) y =
        D.cinnerCompl (P.sweep schedule x) (P.sweep schedule y) :=
      P.balanced_pairing schedule x y
    _ = D.cinnerCompl (P.sweep schedule y) (P.sweep schedule x) :=
      D.cinnerCompl_comm _ _
    _ = D.cinnerCompl (P.balanced schedule y) x :=
      (P.balanced_pairing schedule y x).symm
    _ = D.cinnerCompl x (P.balanced schedule y) :=
      D.cinnerCompl_comm _ _

theorem balanced_positive (schedule : List Index)
    (x : GNSCompletionSpace D) :
    RCnonneg (D.cinnerCompl (P.balanced schedule x) x) := by
  rw [P.balanced_pairing schedule x x]
  exact D.cinner_self_nonneg _

#print axioms sweep_adjoint_reverse
#print axioms balanced
#print axioms balanced_pairing
#print axioms balanced_selfAdjoint
#print axioms balanced_positive

end YMGap.Continuum.GNSProjectionSweep.Family
