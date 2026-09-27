/-
# Exact loss and residual transport for completed projection sweeps

The schedule is applied from left to right on ONE GNS completion. Its loss
is the sum of the squared norms of the ACTUAL successive residual vectors,
not a sum evaluated repeatedly on the initial vector. This sum telescopes
exactly. The orthogonal complement of the joint fixed space is preserved;
no free-product centering assumption is used.

Noncommuting neighbors are not discarded: their residual recurrence retains
the full correction. Commuting updates only contract a previously formed
residual. These identities supply the algebraic part of a possible bounded-
degree sweep estimate, not its finite-sum estimate, interacting coercivity,
signed-covariance join, OS transfer gap, or continuum scaling control.
-/

import YMGap.Continuum.GNSDenseCompletionLaws
import YMGap.Continuum.GNSPairingNormBound

namespace YMGap.Continuum.GNSProjectionSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CReal.sub_self_eqv_zero A)

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

private theorem rc_telescope (a b c : RC) :
    RCadd (RCsub a b) (RCsub b c) = RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      (Q'.add_eqv_congr_right _ _ _ (Q'.sub_add_cancel_eqv _ _))))

private theorem rc_sub_sub (a b : RC) : RCsub a (RCsub a b) = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_sub_eqv _ _))
      (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
        (Q'.sub_add_cancel_eqv _ _))))

/-- Pure operator data, instantiated below by actual original-action
conditional projections. No analytic gap or centering hypothesis. -/
structure Family (D : GNSData) (Index : Type) where
  op : Index → GNSCompletionSpace D → GNSCompletionSpace D
  adjoint : ∀ i x y, D.cinnerCompl (op i x) y = D.cinnerCompl x (op i y)
  idem : ∀ i x, op i (op i x) = op i x

variable {D : GNSData} {Index : Type}

def normSq (x : GNSCompletionSpace D) : RC := D.cinnerCompl x x

namespace Family

variable (P : Family D Index)

def residual (i : Index) (x : GNSCompletionSpace D) : GNSCompletionSpace D :=
  D.cSub x (P.op i x)

theorem self_pairing (i : Index) (x : GNSCompletionSpace D) :
    D.cinnerCompl (P.op i x) (P.op i x) = D.cinnerCompl (P.op i x) x := by
  rw [P.adjoint, P.idem, D.cinnerCompl_comm x (P.op i x)]

theorem single_loss (i : Index) (x : GNSCompletionSpace D) :
    normSq (P.residual i x) = RCsub (normSq x) (normSq (P.op i x)) :=
  GNSPairingNormBound.residual_norm_identity D _ _ (P.self_pairing i x)

theorem op_norm (i : Index) (x : GNSCompletionSpace D) :
    RCle (normSq (P.op i x)) (normSq x) :=
  GNSPairingNormBound.norm_le_of_self_pairing D _ _ (P.self_pairing i x)

theorem op_sub (i : Index) (x y : GNSCompletionSpace D) :
    P.op i (D.cSub x y) = D.cSub (P.op i x) (P.op i y) := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  rw [P.adjoint, D.cinnerCompl_cSub_left, D.cinnerCompl_cSub_left,
    P.adjoint, P.adjoint]

theorem residual_adjoint (i : Index) (x y : GNSCompletionSpace D) :
    D.cinnerCompl (P.residual i x) y = D.cinnerCompl x (P.residual i y) := by
  unfold residual
  rw [D.cinnerCompl_cSub_left, P.adjoint,
    D.cinnerCompl_comm x (D.cSub y (P.op i y)), D.cinnerCompl_cSub_left,
    D.cinnerCompl_comm y x, D.cinnerCompl_comm (P.op i y) x]

theorem residual_sub (i : Index) (x y : GNSCompletionSpace D) :
    P.residual i (D.cSub x y) = D.cSub (P.residual i x) (P.residual i y) := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  rw [P.residual_adjoint, D.cinnerCompl_cSub_left, D.cinnerCompl_cSub_left,
    P.residual_adjoint, P.residual_adjoint]

theorem residual_norm (i : Index) (x : GNSCompletionSpace D) :
    RCle (normSq (P.residual i x)) (normSq x) := by
  apply GNSPairingNormBound.norm_le_of_self_pairing
  have horth := GNSPairingNormBound.residual_orthogonal D _ _ (P.self_pairing i x)
  change D.cinnerCompl (P.op i x) (P.residual i x) = RCzero at horth
  calc
    D.cinnerCompl (P.residual i x) (P.residual i x) =
        RCsub (D.cinnerCompl (P.residual i x) x)
          (D.cinnerCompl (P.residual i x) (P.op i x)) := by
      change D.cinnerCompl (P.residual i x) (D.cSub x (P.op i x)) = _
      rw [D.cinnerCompl_comm, D.cinnerCompl_cSub_left,
        D.cinnerCompl_comm x, D.cinnerCompl_comm (P.op i x)]
    _ = D.cinnerCompl (P.residual i x) x := by
      rw [D.cinnerCompl_comm (P.residual i x) (P.op i x), horth, rc_sub_zero]

/-- Forward order: the list head acts first. -/
def sweep (P : Family D Index) : List Index → GNSCompletionSpace D → GNSCompletionSpace D
  | [], x => x
  | i :: rest, x => sweep P rest (P.op i x)

/-- Every summand is evaluated at its actual intermediate state. -/
def loss (P : Family D Index) : List Index → GNSCompletionSpace D → RC
  | [], _ => RCzero
  | i :: rest, x => RCadd (normSq (P.residual i x)) (loss P rest (P.op i x))

theorem loss_eq (schedule : List Index) (x : GNSCompletionSpace D) :
    P.loss schedule x = RCsub (normSq x) (normSq (P.sweep schedule x)) := by
  induction schedule generalizing x with
  | nil => exact (rc_sub_self _).symm
  | cons i rest ih =>
    change RCadd (normSq (P.residual i x)) (P.loss rest (P.op i x)) = _
    rw [P.single_loss, ih, rc_telescope]
    rfl

theorem sweep_norm (schedule : List Index) (x : GNSCompletionSpace D) :
    RCle (normSq (P.sweep schedule x)) (normSq x) := by
  induction schedule generalizing x with
  | nil => exact RCle_refl _
  | cons i rest ih => exact RCle_trans (ih (P.op i x)) (P.op_norm i x)

/-- Signed pairing changes at the actual intermediate states; no absolute
values and no replacement of the original test by a free-product test. -/
def pairingLoss (P : Family D Index) :
    List Index → GNSCompletionSpace D → GNSCompletionSpace D → RC
  | [], _, _ => RCzero
  | i :: rest, x, y => RCadd (D.cinnerCompl (P.residual i x) y)
      (pairingLoss P rest (P.op i x) y)

theorem pairingLoss_eq (schedule : List Index) (x y : GNSCompletionSpace D) :
    P.pairingLoss schedule x y =
      RCsub (D.cinnerCompl x y) (D.cinnerCompl (P.sweep schedule x) y) := by
  induction schedule generalizing x with
  | nil => exact (rc_sub_self _).symm
  | cons i rest ih =>
    change RCadd (D.cinnerCompl (D.cSub x (P.op i x)) y)
      (P.pairingLoss rest (P.op i x) y) = _
    rw [D.cinnerCompl_cSub_left, ih, rc_telescope]
    rfl

def JointFixed (schedule : List Index) (z : GNSCompletionSpace D) : Prop :=
  ∀ i, i ∈ schedule → P.op i z = z

def OrthogonalJointFixed (schedule : List Index) (x : GNSCompletionSpace D) : Prop :=
  ∀ z, P.JointFixed schedule z → D.cinnerCompl x z = RCzero

theorem sweep_pair_fixed (schedule : List Index) (x z : GNSCompletionSpace D)
    (hz : P.JointFixed schedule z) :
    D.cinnerCompl (P.sweep schedule x) z = D.cinnerCompl x z := by
  induction schedule generalizing x with
  | nil => rfl
  | cons i rest ih =>
    change D.cinnerCompl (P.sweep rest (P.op i x)) z = _
    rw [ih (P.op i x) (fun j hj => hz j (List.mem_cons_of_mem i hj)),
      P.adjoint, hz i List.mem_cons_self]

/-- This is the preserved interacting sector, not a free Haar sector or an
assertion that joint fixed vectors are precisely the scalar constants. -/
theorem sweep_preserves_sector (schedule : List Index) (x : GNSCompletionSpace D)
    (hx : P.OrthogonalJointFixed schedule x) :
    P.OrthogonalJointFixed schedule (P.sweep schedule x) := by
  intro z hz
  rw [P.sweep_pair_fixed schedule x z hz]
  exact hx z hz

theorem residual_after_own (i : Index) (x : GNSCompletionSpace D) :
    P.residual i (P.op i x) = embedV D D.zero := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  unfold residual
  rw [P.idem, D.cinnerCompl_cSub_left, rc_sub_self, D.cinnerCompl_embedZero_left]

/-- A commuting update transports the residual exactly. -/
theorem residual_commute (i j : Index)
    (hcomm : ∀ x, P.op i (P.op j x) = P.op j (P.op i x))
    (x : GNSCompletionSpace D) :
    P.residual i (P.op j x) = P.op j (P.residual i x) := by
  unfold residual
  rw [P.op_sub, hcomm]

theorem commuting_residual_norm (i j : Index)
    (hcomm : ∀ x, P.op i (P.op j x) = P.op j (P.op i x))
    (x : GNSCompletionSpace D) :
    RCle (normSq (P.residual i (P.op j x))) (normSq (P.residual i x)) := by
  rw [P.residual_commute i j hcomm x]
  exact P.op_norm j _

/-- Every update, including a neighbor, retains its exact loss correction:
R_i C_j x = R_i x - R_i (x - C_j x). No commutator is silently zeroed. -/
theorem residual_update (i j : Index) (x : GNSCompletionSpace D) :
    P.residual i (P.op j x) =
      D.cSub (P.residual i x) (P.residual i (P.residual j x)) := by
  rw [← P.residual_sub]
  apply congrArg (P.residual i)
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  change D.cinnerCompl (P.op j x) z = D.cinnerCompl (D.cSub x (D.cSub x (P.op j x))) z
  rw [D.cinnerCompl_cSub_left, D.cinnerCompl_cSub_left, rc_sub_sub]

theorem update_correction_norm (i j : Index) (x : GNSCompletionSpace D) :
    RCle (normSq (P.residual i (P.residual j x)))
      (RCsub (normSq x) (normSq (P.op j x))) := by
  rw [← P.single_loss]
  exact P.residual_norm i _

end Family

#print axioms Family.single_loss
#print axioms Family.op_sub
#print axioms Family.residual_norm
#print axioms Family.loss_eq
#print axioms Family.sweep_norm
#print axioms Family.pairingLoss_eq
#print axioms Family.sweep_preserves_sector
#print axioms Family.residual_after_own
#print axioms Family.residual_commute
#print axioms Family.commuting_residual_norm
#print axioms Family.residual_update
#print axioms Family.update_correction_norm

end YMGap.Continuum.GNSProjectionSweep
