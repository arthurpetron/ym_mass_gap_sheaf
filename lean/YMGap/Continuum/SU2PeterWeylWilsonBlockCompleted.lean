/-
# Completed correctly indexed SU(2) same-state Wilson block

The old faithful connector combines the vacuum/fundamental Haar Gram with the
fundamental/next-excited transfer eigenvalues.  The frozen
`SU2PeterWeylWilsonBlock` already contains the correct repair at one link: its
two coordinates are explicitly vacuum and fundamental, its interacting Gram is
`diag(1,1/8)`, and the transfer obtained from a second use of the same Wilson
kernel is `diag(1,1/8)`.

This successor makes that corrected indexing explicit and closes the purely
functional-analytic extension to the constructive GNS completion.  Unlike the
old adapter, the distinguished vector is the nonzero vacuum mode and is proved
fixed.  Honest scope: this is the exact one-link Peter--Weyl Wilson block; the
embedding into the full finite-volume `E_Lambda` observable algebra remains a
separate same-state field.
-/

import YMGap.Continuum.SU2FaithfulTwoModeSameStateFence
import YMGap.Continuum.PositiveTimeCompressedTransfer
import YMGap.Continuum.SU2PeterWeylWilsonBlock

namespace YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2PeterWeylWilsonBlock

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Correct vacuum/fundamental indexing -/

def correctedModeVector (i : Fin 2) : ModeVec :=
  if i.val = 0 then vacuumMode else fundamentalMode

def correctedEigenvalue (i : Fin 2) : Q' :=
  if i.val = 0 then 1 else eighth

/-- The corrected interacting Gram keeps the constant character as a unit-norm
vacuum and gives the fundamental character its derived Wilson weight `1/8`. -/
theorem corrected_mode_gram (i j : Fin 2) :
    wilsonModeGNS.B (correctedModeVector i) (correctedModeVector j) ≈
      if i.val = j.val then
        (if i.val = 0 then 1 else eighth)
      else 0 := by
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  have hj : j.val = 0 ∨ j.val = 1 := by omega
  rcases hi with hi | hi <;> rcases hj with hj | hj
  <;> simp [correctedModeVector, hi, hj, wilsonModeGNS, reflectedWilsonGram,
    vacuumMode, fundamentalMode, modeZero, eighth]
  <;> decide

/-- Each correctly labelled mode has its physical same-state eigenvalue:
vacuum `1`, fundamental `1/8`. -/
theorem corrected_mode_eigen (i : Fin 2) :
    modeEqv (sameStateTransfer (correctedModeVector i))
      (modeSmul (correctedEigenvalue i) (correctedModeVector i)) := by
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · simp [correctedModeVector, correctedEigenvalue, hi]
    exact vacuum_eigen
  · simp [correctedModeVector, correctedEigenvalue, hi]
    exact fundamental_eighth_eigen

/-- The transfer and Gram arise from the same one-link Wilson coefficient
table: the compressed pairing is exactly the twice-used-kernel moment. -/
theorem corrected_same_state_compatibility (a b : ModeVec) :
    wilsonModeGNS.B (sameStateTransfer a) b ≈ twoLinkWilsonMoment a b :=
  same_state_compression a b

/-! ## Completion descent -/

theorem sameStateTransfer_map_sub (a b : ModeVec) :
    wilsonModeGNS.veq
      (sameStateTransfer (wilsonModeGNS.sub a b))
      (wilsonModeGNS.sub (sameStateTransfer a) (sameStateTransfer b)) := by
  unfold sameStateTransfer wilsonModeGNS GNSData.sub modeAdd modeNeg modeEqv
  constructor
  · exact Q'.eqv_refl _
  · ring_qeqv

theorem sameStateTransfer_distSq_contraction (a b : ModeVec) :
    wilsonModeGNS.distSqQ (sameStateTransfer a) (sameStateTransfer b) ≤
      wilsonModeGNS.distSqQ a b := by
  have hsub := sameStateTransfer_map_sub a b
  exact le_of_eqv_le
    (Q'.eqv_symm (wilsonModeGNS.B_diag_congr hsub))
    (sameStateTransfer_contraction (wilsonModeGNS.sub a b))

def applyCauchy (x : CauchyGNS wilsonModeGNS) : CauchyGNS wilsonModeGNS where
  seq := fun n => sameStateTransfer (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _
      (sameStateTransfer_distSq_contraction (x.seq p) (x.seq q))
      (x.isCauchy epsilon hepsilon p q hp hq)

theorem applyCauchy_null {x y : CauchyGNS wilsonModeGNS}
    (h : CauchyNull wilsonModeGNS x y) :
    CauchyNull wilsonModeGNS (applyCauchy x) (applyCauchy y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (sameStateTransfer_distSq_contraction (x.seq n) (y.seq n)) (hN n hn)⟩

def completedSameStateTransfer :
    GNSCompletionSpace wilsonModeGNS → GNSCompletionSpace wilsonModeGNS :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid wilsonModeGNS) (applyCauchy x))
    (fun _ _ h => Quotient.sound (applyCauchy_null h))

theorem completedSameStateTransfer_embed (a : ModeVec) :
    completedSameStateTransfer (embedV wilsonModeGNS a) =
      embedV wilsonModeGNS (sameStateTransfer a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

/-! ## Completed operator laws -/

theorem cinnerRep_selfAdjoint (x y : CauchyGNS wilsonModeGNS) :
    CReal.Equiv
      (wilsonModeGNS.cinnerRep (applyCauchy x) y)
      (wilsonModeGNS.cinnerRep x (applyCauchy y)) := by
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (wilsonModeGNS.cInnerSeq (applyCauchy x) y n))
    (bSeq := fun n => CReal.ofQ'
      (wilsonModeGNS.cInnerSeq x (applyCauchy y) n))
    (fun n =>
      PositiveTimeCompressedTransfer.PositiveTimeCompression.lifted_eqv
      (sameStateTransfer_selfAdjoint (x.seq n) (y.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem completedSameStateTransfer_selfAdjoint
    (x y : GNSCompletionSpace wilsonModeGNS) :
    wilsonModeGNS.cinnerCompl (completedSameStateTransfer x) y =
      wilsonModeGNS.cinnerCompl x (completedSameStateTransfer y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  exact cinnerRep_selfAdjoint u v

theorem completedSameStateTransfer_positive
    (x : GNSCompletionSpace wilsonModeGNS) :
    CReal.RCnonneg
      (wilsonModeGNS.cinnerCompl (completedSameStateTransfer x) x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show CReal.leEv CReal.czero
    (wilsonModeGNS.cinnerRep (applyCauchy u) u)
  exact CReal.leEv_ofQ'_of_approx_ge
    (fun _ => sameStateTransfer_positive (u.seq _))

theorem cinnerRep_contraction (x : CauchyGNS wilsonModeGNS) :
    CReal.leEv
      (wilsonModeGNS.cinnerRep (applyCauchy x) (applyCauchy x))
      (wilsonModeGNS.cinnerRep x x) := by
  refine CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _) ?_
  intro epsilon hepsilon
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (sameStateTransfer_contraction (x.seq n))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

theorem completedSameStateTransfer_contraction
    (x : GNSCompletionSpace wilsonModeGNS) :
    CReal.RCle
      (wilsonModeGNS.cinnerCompl (completedSameStateTransfer x)
        (completedSameStateTransfer x))
      (wilsonModeGNS.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact cinnerRep_contraction u

/-- The correctly indexed completed operator, with the physical nonzero vacuum
mode distinguished instead of additive zero. -/
def completedWilsonBlockTransferOperator : TransferOperator wilsonModeGNS.gnsComplete where
  T := completedSameStateTransfer
  vacuum := embedV wilsonModeGNS vacuumMode
  selfAdjoint := completedSameStateTransfer_selfAdjoint
  positive := completedSameStateTransfer_positive
  contraction := completedSameStateTransfer_contraction

/-! ## Completed physical modes -/

theorem completed_vacuum_eigen :
    completedWilsonBlockTransferOperator.T
        (embedV wilsonModeGNS vacuumMode) =
      embedV wilsonModeGNS vacuumMode := by
  refine Eq.trans (completedSameStateTransfer_embed vacuumMode) ?_
  apply Quotient.sound
  exact embed_null_of_rad wilsonModeGNS
    (rad_of_veq wilsonModeGNS vacuum_eigen)

theorem completed_fundamental_eigen :
    completedWilsonBlockTransferOperator.T
        (embedV wilsonModeGNS fundamentalMode) =
      embedV wilsonModeGNS (modeSmul eighth fundamentalMode) := by
  refine Eq.trans (completedSameStateTransfer_embed fundamentalMode) ?_
  apply Quotient.sound
  exact embed_null_of_rad wilsonModeGNS
    (rad_of_veq wilsonModeGNS fundamental_eighth_eigen)

theorem vacuum_qmk_ne_zero :
    wilsonModeGNS.qmk vacuumMode ≠ wilsonModeGNS.qmk wilsonModeGNS.zero := by
  intro h
  have hr : wilsonModeGNS.rad vacuumMode wilsonModeGNS.zero := Quotient.exact h
  have hsub : wilsonModeGNS.veq
      (wilsonModeGNS.sub vacuumMode wilsonModeGNS.zero) vacuumMode := by
    unfold GNSData.sub wilsonModeGNS modeAdd modeNeg modeZero vacuumMode modeEqv
    exact ⟨by decide, by decide⟩
  have hdiag := wilsonModeGNS.B_diag_congr hsub
  have he : wilsonModeGNS.B vacuumMode vacuumMode ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hdiag) hr
  exact (by decide :
    ¬ (wilsonModeGNS.B vacuumMode vacuumMode ≈ 0)) he

theorem completed_vacuum_ne_zero :
    embedV wilsonModeGNS vacuumMode ≠
      embedV wilsonModeGNS wilsonModeGNS.zero := by
  intro h
  apply vacuum_qmk_ne_zero
  exact embedQuot_injective wilsonModeGNS h

theorem completed_fundamental_ne_zero :
    embedV wilsonModeGNS fundamentalMode ≠
      embedV wilsonModeGNS wilsonModeGNS.zero := by
  intro h
  apply fundamental_qmk_ne_zero
  exact embedQuot_injective wilsonModeGNS h

end YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted

#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.corrected_mode_gram
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.corrected_mode_eigen
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.corrected_same_state_compatibility
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.sameStateTransfer_distSq_contraction
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.applyCauchy
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.applyCauchy_null
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.completedSameStateTransfer
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.completedSameStateTransfer_embed
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.completedSameStateTransfer_selfAdjoint
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.completedSameStateTransfer_positive
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.completedSameStateTransfer_contraction
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.completedWilsonBlockTransferOperator
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.completed_vacuum_eigen
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.completed_fundamental_eigen
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.completed_vacuum_ne_zero
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted.completed_fundamental_ne_zero
