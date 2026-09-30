/-
# Exact commuting-projection variance on a completed GNS carrier

For a finite schedule of pairwise commuting orthogonal projections, the
forward sweep is itself fixed by every listed projection. Its squared
complement norm is the exact sweep loss and is bounded by the sum of the
ORIGINAL-input residual energies. Lists may be empty or contain repeats.
-/

import YMGap.Continuum.GNSCommutingSweep
import YMGap.Continuum.GNSProjectionSweepEnergy

namespace YMGap.Continuum.GNSProjectionSweep.Family

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient

variable {D : GNSData} {Index : Type} (P : Family D Index)

/-- Every listed operator fixes the completed output of its commuting sweep.
This remains valid when the schedule repeats an index. -/
theorem commuting_sweep_joint_fixed (tests : List Index)
    (hcomm : ∀ i, i ∈ tests → ∀ j, j ∈ tests → ∀ y,
      P.op i (P.op j y) = P.op j (P.op i y))
    (x : GNSCompletionSpace D) : P.JointFixed tests (P.sweep tests x) := by
  induction tests generalizing x with
  | nil =>
      intro i hi
      exact False.elim (List.not_mem_nil hi)
  | cons j rest ih =>
      intro i hi
      rcases List.mem_cons.mp hi with he | hi
      · subst i
        change P.op j (P.sweep rest (P.op j x)) = P.sweep rest (P.op j x)
        rw [P.op_sweep j rest
          (fun k hk => hcomm j List.mem_cons_self k (List.mem_cons_of_mem j hk)),
          P.idem]
      · exact ih
          (fun a ha b hb y => hcomm a (List.mem_cons_of_mem j ha)
            b (List.mem_cons_of_mem j hb) y)
          (P.op j x) i hi

/-- The commuting sweep has the orthogonal-projection self-pairing identity
on the original completed inner product, without a separate adjoint theorem. -/
theorem commuting_sweep_self_pairing (tests : List Index)
    (hcomm : ∀ i, i ∈ tests → ∀ j, j ∈ tests → ∀ y,
      P.op i (P.op j y) = P.op j (P.op i y))
    (x : GNSCompletionSpace D) :
    D.cinnerCompl (P.sweep tests x) (P.sweep tests x) =
      D.cinnerCompl x (P.sweep tests x) :=
  P.sweep_pair_fixed tests x (P.sweep tests x)
    (P.commuting_sweep_joint_fixed tests hcomm x)

/-- Its completed squared complement is exactly the original sweep loss. -/
theorem commuting_sweep_variance_eq_loss (tests : List Index)
    (hcomm : ∀ i, i ∈ tests → ∀ j, j ∈ tests → ∀ y,
      P.op i (P.op j y) = P.op j (P.op i y))
    (x : GNSCompletionSpace D) :
    normSq (D.cSub x (P.sweep tests x)) = P.loss tests x := by
  change D.cinnerCompl (D.cSub x (P.sweep tests x))
    (D.cSub x (P.sweep tests x)) = _
  rw [GNSPairingNormBound.residual_norm_identity D _ _
    ((P.commuting_sweep_self_pairing tests hcomm x).trans
      (D.cinnerCompl_comm x (P.sweep tests x))), P.loss_eq]
  rfl

/-- Each commuting update contracts every later test's residual, so the
actual intermediate losses cost no more than the original-input energy. -/
theorem commuting_loss_le_finalEnergy (tests : List Index)
    (hcomm : ∀ i, i ∈ tests → ∀ j, j ∈ tests → ∀ y,
      P.op i (P.op j y) = P.op j (P.op i y))
    (x : GNSCompletionSpace D) :
    RCle (P.loss tests x) (P.finalEnergy tests x) := by
  induction tests generalizing x with
  | nil => exact RCle_refl _
  | cons i rest ih =>
      have hrest : ∀ j, j ∈ rest → ∀ k, k ∈ rest → ∀ y,
          P.op j (P.op k y) = P.op k (P.op j y) :=
        fun j hj k hk y => hcomm j (List.mem_cons_of_mem i hj)
          k (List.mem_cons_of_mem i hk) y
      have htail := ih hrest (P.op i x)
      have henergy : RCle (P.finalEnergy rest (P.op i x))
          (P.finalEnergy rest x) := by
        exact sumOn_mono rest _ _ (fun j hj =>
          P.commuting_residual_norm j i
            (hcomm j (List.mem_cons_of_mem i hj) i List.mem_cons_self) x)
      change RCle
        (RCadd (normSq (P.residual i x)) (P.loss rest (P.op i x)))
        (RCadd (normSq (P.residual i x)) (P.finalEnergy rest x))
      exact RCle_trans (RCadd_le_add (RCle_refl _) htail)
        (RCadd_le_add (RCle_refl _) henergy)

/-- Finite commuting-patch Poincare inequality on EVERY completed vector.
The right side is evaluated on x, not on intermediate or final states. -/
theorem commuting_sweep_variance_le_finalEnergy (tests : List Index)
    (hcomm : ∀ i, i ∈ tests → ∀ j, j ∈ tests → ∀ y,
      P.op i (P.op j y) = P.op j (P.op i y))
    (x : GNSCompletionSpace D) :
    RCle (normSq (D.cSub x (P.sweep tests x)))
      (P.finalEnergy tests x) := by
  rw [P.commuting_sweep_variance_eq_loss tests hcomm x]
  exact P.commuting_loss_le_finalEnergy tests hcomm x

#print axioms commuting_sweep_joint_fixed
#print axioms commuting_sweep_self_pairing
#print axioms commuting_sweep_variance_eq_loss
#print axioms commuting_loss_le_finalEnergy
#print axioms commuting_sweep_variance_le_finalEnergy

end YMGap.Continuum.GNSProjectionSweep.Family
