/-
# Remove inactive updates from a commuting layer

For a finite commuting family, every update fixing the ORIGINAL input may
be deleted from the sweep. The remaining operators and the completed output
are unchanged. This is exact equality, not an estimate on a different norm.
It is the algebraic cancellation used by the physical eight-layer cone.
-/

import YMGap.Continuum.GNSProjectionSweep

namespace YMGap.Continuum.GNSProjectionSweep.Family

set_option autoImplicit false

open YMGap.Continuum.GNSQuotient

variable {D : GNSData} {Index : Type} (P : Family D Index)

/-- Commutation with every factor passes through the forward sweep. -/
theorem op_sweep (i : Index) (schedule : List Index)
    (hcomm : ∀ j, j ∈ schedule → ∀ x, P.op i (P.op j x) = P.op j (P.op i x))
    (x : GNSCompletionSpace D) :
    P.op i (P.sweep schedule x) = P.sweep schedule (P.op i x) := by
  induction schedule generalizing x with
  | nil => rfl
  | cons j rest ih =>
    change P.op i (P.sweep rest (P.op j x)) = P.sweep rest (P.op j (P.op i x))
    rw [ih (fun k hk => hcomm k (List.mem_cons_of_mem j hk)),
      hcomm j List.mem_cons_self]

/-- Filter away operators which fix the input. Commutation is assumed only
within this one supplied schedule; no global commuting-action premise. -/
theorem sweep_filter (schedule : List Index) (keep : Index → Bool)
    (hcomm : ∀ i, i ∈ schedule → ∀ j, j ∈ schedule → ∀ x,
      P.op i (P.op j x) = P.op j (P.op i x))
    (x : GNSCompletionSpace D)
    (hfixed : ∀ i, i ∈ schedule → keep i = false → P.op i x = x) :
    P.sweep schedule x = P.sweep (schedule.filter keep) x := by
  induction schedule generalizing x with
  | nil => rfl
  | cons i rest ih =>
    have hc : ∀ j, j ∈ rest → ∀ k, k ∈ rest → ∀ y,
        P.op j (P.op k y) = P.op k (P.op j y) :=
      fun j hj k hk => hcomm j (List.mem_cons_of_mem i hj) k (List.mem_cons_of_mem i hk)
    cases hi : keep i with
    | false =>
      simp only [List.filter_cons, hi, Bool.false_eq_true, if_false, sweep]
      rw [hfixed i List.mem_cons_self hi]
      exact ih hc x (fun j hj => hfixed j (List.mem_cons_of_mem i hj))
    | true =>
      simp only [List.filter_cons, hi, if_true, sweep]
      apply ih hc
      intro j hj hjkeep
      rw [hcomm j (List.mem_cons_of_mem i hj) i List.mem_cons_self,
        hfixed j (List.mem_cons_of_mem i hj) hjkeep]

theorem sweep_append (left right : List Index) (x : GNSCompletionSpace D) :
    P.sweep (left ++ right) x = P.sweep right (P.sweep left x) := by
  induction left generalizing x with
  | nil => rfl
  | cons i rest ih => exact ih (P.op i x)

#print axioms op_sweep
#print axioms sweep_filter
#print axioms sweep_append

end YMGap.Continuum.GNSProjectionSweep.Family
