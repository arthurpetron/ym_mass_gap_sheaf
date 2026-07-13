/-
# Completed faithful two-mode character transfer

`SU2FaithfulTwoModeGNSConnector` constructs a nondegenerate rational two-mode
GNS carrier and proves the exact `1/8` and `1/256` character evolution laws on
its dense vectors.  This file closes the purely functional-analytic extension
step: the dense contraction acts termwise on Cauchy representatives, respects
the completion null relation, and therefore descends to the canonical
constructive GNS completion.  Self-adjointness, positivity, and contraction of
the completed map are derived from the corresponding rational carrier
identities by the existing constructive-real limit machinery.

The distinguished vector of the generic `TransferOperator` adapter below is
the additive zero.  It is only a structural adapter, not a physical-vacuum
claim.  In particular this file does not identify the two-mode form with the
interacting finite-volume Wilson state `E_Lambda`; that same-state
identification remains open.
-/

import YMGap.Continuum.SU2FaithfulTwoModeGNSConnector

namespace YMGap.Continuum.SU2FaithfulTwoModeCompletedTransfer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FaithfulTwoModeGNSConnector
open YMGap.Continuum.SU2HaarTwoModePositiveTimePilot

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Distance contraction and descent -/

/-- The diagonal character map commutes with subtraction modulo the carrier
equivalence. -/
theorem dense_character_map_sub (a b : faithfulModeGNS.V) :
    faithfulModeGNS.veq
      (denseCharacterTransfer (faithfulModeGNS.sub a b))
      (faithfulModeGNS.sub (denseCharacterTransfer a)
        (denseCharacterTransfer b)) := by
  unfold denseCharacterTransfer faithfulModeGNS positivePlane gnsProduct
    unitQGNS GNSData.sub
  constructor <;> ring_qeqv

/-- The proved squared-norm contraction is equivalently a squared-distance
contraction, which is exactly the input needed by the completion. -/
theorem dense_character_distSq_contraction (a b : faithfulModeGNS.V) :
    faithfulModeGNS.distSqQ (denseCharacterTransfer a)
        (denseCharacterTransfer b) ≤ faithfulModeGNS.distSqQ a b := by
  have hsub := dense_character_map_sub a b
  exact le_of_eqv_le
    (Q'.eqv_symm (faithfulModeGNS.B_diag_congr hsub))
    (dense_character_contraction (faithfulModeGNS.sub a b))

/-- Apply the dense character transfer termwise to a Cauchy representative. -/
def applyCauchy (x : CauchyGNS faithfulModeGNS) : CauchyGNS faithfulModeGNS where
  seq := fun n => denseCharacterTransfer (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro ε hε p q hp hq
    exact Q'.le_trans' _ _ _
      (dense_character_distSq_contraction (x.seq p) (x.seq q))
      (x.isCauchy ε hε p q hp hq)

theorem applyCauchy_null {x y : CauchyGNS faithfulModeGNS}
    (h : CauchyNull faithfulModeGNS x y) :
    CauchyNull faithfulModeGNS (applyCauchy x) (applyCauchy y) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (dense_character_distSq_contraction (x.seq n) (y.seq n)) (hN n hn)⟩

/-- The exact two-character evolution on the canonical constructive GNS
completion. -/
def completedTransfer :
    GNSCompletionSpace faithfulModeGNS → GNSCompletionSpace faithfulModeGNS :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid faithfulModeGNS) (applyCauchy x))
    (fun _ _ h => Quotient.sound (applyCauchy_null h))

theorem completedTransfer_embed (a : faithfulModeGNS.V) :
    completedTransfer (embedV faithfulModeGNS a) =
      embedV faithfulModeGNS (denseCharacterTransfer a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

/-! ## Completed operator laws -/

theorem cinnerRep_selfAdjoint (x y : CauchyGNS faithfulModeGNS) :
    CReal.Equiv
      (faithfulModeGNS.cinnerRep (applyCauchy x) y)
      (faithfulModeGNS.cinnerRep x (applyCauchy y)) := by
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (faithfulModeGNS.cInnerSeq (applyCauchy x) y n))
    (bSeq := fun n => CReal.ofQ'
      (faithfulModeGNS.cInnerSeq x (applyCauchy y) n))
    (fun n => PositiveTimeCompression.lifted_eqv
      (dense_character_selfAdjoint (x.seq n) (y.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem completedTransfer_selfAdjoint
    (x y : GNSCompletionSpace faithfulModeGNS) :
    faithfulModeGNS.cinnerCompl (completedTransfer x) y =
      faithfulModeGNS.cinnerCompl x (completedTransfer y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  exact cinnerRep_selfAdjoint u v

theorem completedTransfer_positive (x : GNSCompletionSpace faithfulModeGNS) :
    CReal.RCnonneg (faithfulModeGNS.cinnerCompl (completedTransfer x) x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show CReal.leEv CReal.czero
    (faithfulModeGNS.cinnerRep (applyCauchy u) u)
  exact CReal.leEv_ofQ'_of_approx_ge
    (fun _ => dense_character_positive (u.seq _))

theorem cinnerRep_contraction (x : CauchyGNS faithfulModeGNS) :
    CReal.leEv
      (faithfulModeGNS.cinnerRep (applyCauchy x) (applyCauchy x))
      (faithfulModeGNS.cinnerRep x x) := by
  refine CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _) ?_
  intro ε hε
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (dense_character_contraction (x.seq n))
    (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))⟩

theorem completedTransfer_contraction (x : GNSCompletionSpace faithfulModeGNS) :
    CReal.RCle
      (faithfulModeGNS.cinnerCompl (completedTransfer x) (completedTransfer x))
      (faithfulModeGNS.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact cinnerRep_contraction u

/-- Structural completed transfer with the generic adapter's zero
distinguished vector.  No physical-vacuum interpretation is attached. -/
def completedCharacterTransferOperator : TransferOperator faithfulModeGNS.gnsComplete where
  T := completedTransfer
  vacuum := embedV faithfulModeGNS faithfulModeGNS.zero
  selfAdjoint := completedTransfer_selfAdjoint
  positive := completedTransfer_positive
  contraction := completedTransfer_contraction

/-! ## Exact completed eigenmodes -/

theorem completed_first_eigen :
    completedCharacterTransferOperator.T
        (embedV faithfulModeGNS firstModeVector) =
      embedV faithfulModeGNS
        (faithfulModeGNS.smul firstEigenvalue firstModeVector) := by
  refine Eq.trans (completedTransfer_embed firstModeVector) ?_
  apply Quotient.sound
  apply embed_null_of_rad faithfulModeGNS
  have hsub : faithfulModeGNS.veq
      (faithfulModeGNS.sub (denseCharacterTransfer firstModeVector)
        (faithfulModeGNS.smul firstEigenvalue firstModeVector))
      (faithfulModeGNS.sub
        (faithfulModeGNS.smul firstEigenvalue firstModeVector)
        (faithfulModeGNS.smul firstEigenvalue firstModeVector)) :=
    faithfulModeGNS.add_congr dense_character_first_eigen
      (faithfulModeGNS.veq_refl _)
  exact Q'.eqv_trans _ _ _ (faithfulModeGNS.B_diag_congr hsub)
    (faithfulModeGNS.rad_refl _)

theorem completed_second_eigen :
    completedCharacterTransferOperator.T
        (embedV faithfulModeGNS secondModeVector) =
      embedV faithfulModeGNS
        (faithfulModeGNS.smul secondEigenvalue secondModeVector) := by
  refine Eq.trans (completedTransfer_embed secondModeVector) ?_
  apply Quotient.sound
  apply embed_null_of_rad faithfulModeGNS
  have hsub : faithfulModeGNS.veq
      (faithfulModeGNS.sub (denseCharacterTransfer secondModeVector)
        (faithfulModeGNS.smul secondEigenvalue secondModeVector))
      (faithfulModeGNS.sub
        (faithfulModeGNS.smul secondEigenvalue secondModeVector)
        (faithfulModeGNS.smul secondEigenvalue secondModeVector)) :=
    faithfulModeGNS.add_congr dense_character_second_eigen
      (faithfulModeGNS.veq_refl _)
  exact Q'.eqv_trans _ _ _ (faithfulModeGNS.B_diag_congr hsub)
    (faithfulModeGNS.rad_refl _)

theorem completed_first_ne_zero :
    embedV faithfulModeGNS firstModeVector ≠
      embedV faithfulModeGNS faithfulModeGNS.zero := by
  intro h
  apply first_mode_qmk_ne_zero
  apply embedQuot_injective faithfulModeGNS
  exact h

theorem completed_second_ne_zero :
    embedV faithfulModeGNS secondModeVector ≠
      embedV faithfulModeGNS faithfulModeGNS.zero := by
  intro h
  apply second_mode_qmk_ne_zero
  apply embedQuot_injective faithfulModeGNS
  exact h

#print axioms dense_character_map_sub
#print axioms dense_character_distSq_contraction
#print axioms applyCauchy
#print axioms applyCauchy_null
#print axioms completedTransfer
#print axioms completedTransfer_embed
#print axioms cinnerRep_selfAdjoint
#print axioms completedTransfer_selfAdjoint
#print axioms completedTransfer_positive
#print axioms cinnerRep_contraction
#print axioms completedTransfer_contraction
#print axioms completedCharacterTransferOperator
#print axioms completed_first_eigen
#print axioms completed_second_eigen
#print axioms completed_first_ne_zero
#print axioms completed_second_ne_zero

end YMGap.Continuum.SU2FaithfulTwoModeCompletedTransfer
