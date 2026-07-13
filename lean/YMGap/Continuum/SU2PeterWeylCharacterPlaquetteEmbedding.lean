/-
# Character block inside the completed SU(2) plaquette block

The corrected two-channel Wilson block has coordinates `(vacuum, chi_1)`.
The five-coordinate cut-plaquette block has coordinates
`(vacuum, D00, D01, D10, D11)`.  This file proves that the literal trace map

    (a0, a1) |-> (a0, a1, 0, 0, a1)

is an isometry for the SAME Wilson reflection form and intertwines the SAME
one-step compressed transfer.  The map is then descended through both
constructive GNS completions.  Thus the factor `2 * (1/16) = 1/8` and the
fundamental eigenvalue `1/8` are compatible before and after completion.

Honest scope: this identifies the character block with the trace subspace of
one cut plaquette.  It does not identify an orthogonal product of such blocks
with the shared-link finite-volume `E_Lambda` state.
-/

import YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted
import YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock

namespace YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted
open YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, zero_num_cast, zero_den_cast, one_num_cast,
               one_den_cast, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## The literal character trace map -/

def characterTraceEmbedding (a : ModeVec) : PlaquetteVec :=
  (a.1, (a.2, (0, (0, a.2))))

theorem characterTraceEmbedding_map_veq {a b : ModeVec}
    (h : wilsonModeGNS.veq a b) :
    plaquetteGNS.veq (characterTraceEmbedding a) (characterTraceEmbedding b) :=
  ⟨h.1, ⟨h.2, ⟨Q'.eqv_refl 0, ⟨Q'.eqv_refl 0, h.2⟩⟩⟩⟩

theorem characterTraceEmbedding_map_add (a b : ModeVec) :
    plaquetteGNS.veq
      (characterTraceEmbedding (wilsonModeGNS.add a b))
      (plaquetteGNS.add (characterTraceEmbedding a)
        (characterTraceEmbedding b)) := by
  unfold characterTraceEmbedding wilsonModeGNS modeAdd plaquetteGNS gnsProduct
    vacuumLine matrixLine qWeightGNS
  exact ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _,
    ⟨Q'.eqv_symm (QPoly.q_zero_add_eqv 0),
      ⟨Q'.eqv_symm (QPoly.q_zero_add_eqv 0), Q'.eqv_refl _⟩⟩⟩⟩

theorem characterTraceEmbedding_map_smul (s : Q') (a : ModeVec) :
    plaquetteGNS.veq
      (characterTraceEmbedding (wilsonModeGNS.smul s a))
      (plaquetteGNS.smul s (characterTraceEmbedding a)) := by
  unfold characterTraceEmbedding wilsonModeGNS modeSmul plaquetteGNS gnsProduct
    vacuumLine matrixLine qWeightGNS
  exact ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _,
    ⟨Q'.eqv_symm (QPoly.q_mul_zero s),
      ⟨Q'.eqv_symm (QPoly.q_mul_zero s), Q'.eqv_refl _⟩⟩⟩⟩

theorem characterTraceEmbedding_map_sub (a b : ModeVec) :
    plaquetteGNS.veq
      (characterTraceEmbedding (wilsonModeGNS.sub a b))
      (plaquetteGNS.sub (characterTraceEmbedding a)
        (characterTraceEmbedding b)) := by
  unfold GNSData.sub characterTraceEmbedding wilsonModeGNS modeAdd modeNeg
    plaquetteGNS gnsProduct vacuumLine matrixLine qWeightGNS
  exact ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _,
    ⟨by ring_qeqv, ⟨by ring_qeqv, Q'.eqv_refl _⟩⟩⟩⟩

/-- The trace map is an exact same-state isometry.  Its two diagonal matrix
coefficients each contribute `1/16`, giving the character weight `1/8`. -/
theorem characterTraceEmbedding_gram (a b : ModeVec) :
    plaquetteGNS.B (characterTraceEmbedding a) (characterTraceEmbedding b) ≈
      wilsonModeGNS.B a b := by
  refine Q'.eqv_trans _ _ _ (plaquetteGNS_B_eq_gram _ _) ?_
  refine Q'.eqv_trans _
    (a.1 * b.1 + eighth * (a.2 * b.2)) _ ?_ ?_
  · unfold characterTraceEmbedding plaquetteGram matrixDot
    refine QPoly.q_add_congr (Q'.eqv_refl _) ?_
    refine Q'.eqv_trans _
      ((fundamentalMatrixWeight + fundamentalMatrixWeight) * (a.2 * b.2)) _
      (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  · exact Q'.eqv_symm (reflectedWilsonGram_diagonal a b)

/-- The same-state transfer preserves the trace subspace and has exactly the
same fundamental eigenvalue on both presentations. -/
theorem characterTraceEmbedding_intertwines (a : ModeVec) :
    plaquetteGNS.veq
      (plaquetteTransfer (characterTraceEmbedding a))
      (characterTraceEmbedding (sameStateTransfer a)) := by
  unfold characterTraceEmbedding plaquetteTransfer sameStateTransfer plaquetteGNS
    gnsProduct vacuumLine matrixLine qWeightGNS
  exact ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _,
    ⟨QPoly.q_mul_zero eighth,
      ⟨QPoly.q_mul_zero eighth, Q'.eqv_refl _⟩⟩⟩⟩

theorem characterTraceEmbedding_distSq (a b : ModeVec) :
    plaquetteGNS.distSqQ (characterTraceEmbedding a) (characterTraceEmbedding b) ≈
      wilsonModeGNS.distSqQ a b := by
  refine Q'.eqv_trans _ _ _
    (plaquetteGNS.B_diag_congr
      (plaquetteGNS.veq_symm (characterTraceEmbedding_map_sub a b))) ?_
  exact characterTraceEmbedding_gram
    (wilsonModeGNS.sub a b) (wilsonModeGNS.sub a b)

/-! ## Completion of the plaquette transfer -/

theorem plaquetteTransfer_map_sub (a b : PlaquetteVec) :
    plaquetteGNS.veq
      (plaquetteTransfer (plaquetteGNS.sub a b))
      (plaquetteGNS.sub (plaquetteTransfer a) (plaquetteTransfer b)) := by
  unfold GNSData.sub plaquetteTransfer plaquetteGNS gnsProduct vacuumLine
    matrixLine qWeightGNS
  exact ⟨Q'.eqv_refl _, ⟨by ring_qeqv,
    ⟨by ring_qeqv, ⟨by ring_qeqv, by ring_qeqv⟩⟩⟩⟩

theorem plaquetteTransfer_distSq_contraction (a b : PlaquetteVec) :
    plaquetteGNS.distSqQ (plaquetteTransfer a) (plaquetteTransfer b) ≤
      plaquetteGNS.distSqQ a b := by
  have hsub := plaquetteTransfer_map_sub a b
  exact le_of_eqv_le
    (Q'.eqv_symm (plaquetteGNS.B_diag_congr hsub))
    (plaquetteTransfer_contraction (plaquetteGNS.sub a b))

def plaquetteApplyCauchy (x : CauchyGNS plaquetteGNS) :
    CauchyGNS plaquetteGNS where
  seq := fun n => plaquetteTransfer (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _
      (plaquetteTransfer_distSq_contraction (x.seq p) (x.seq q))
      (x.isCauchy epsilon hepsilon p q hp hq)

theorem plaquetteApplyCauchy_null {x y : CauchyGNS plaquetteGNS}
    (h : CauchyNull plaquetteGNS x y) :
    CauchyNull plaquetteGNS (plaquetteApplyCauchy x)
      (plaquetteApplyCauchy y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (plaquetteTransfer_distSq_contraction (x.seq n) (y.seq n)) (hN n hn)⟩

def completedPlaquetteTransfer :
    GNSCompletionSpace plaquetteGNS → GNSCompletionSpace plaquetteGNS :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid plaquetteGNS) (plaquetteApplyCauchy x))
    (fun _ _ h => Quotient.sound (plaquetteApplyCauchy_null h))

theorem completedPlaquetteTransfer_embed (a : PlaquetteVec) :
    completedPlaquetteTransfer (embedV plaquetteGNS a) =
      embedV plaquetteGNS (plaquetteTransfer a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

/-! ## Isometric embedding through the completions -/

def traceMapCauchy (x : CauchyGNS wilsonModeGNS) : CauchyGNS plaquetteGNS where
  seq := fun n => characterTraceEmbedding (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (characterTraceEmbedding_distSq (x.seq p) (x.seq q)))
      (x.isCauchy epsilon hepsilon p q hp hq)

theorem traceMapCauchy_null {x y : CauchyGNS wilsonModeGNS}
    (h : CauchyNull wilsonModeGNS x y) :
    CauchyNull plaquetteGNS (traceMapCauchy x) (traceMapCauchy y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (Q'.le_of_eqv (characterTraceEmbedding_distSq (x.seq n) (y.seq n)))
    (hN n hn)⟩

def completedCharacterTraceEmbedding :
    GNSCompletionSpace wilsonModeGNS → GNSCompletionSpace plaquetteGNS :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid plaquetteGNS) (traceMapCauchy x))
    (fun _ _ h => Quotient.sound (traceMapCauchy_null h))

theorem completedCharacterTraceEmbedding_embed (a : ModeVec) :
    completedCharacterTraceEmbedding (embedV wilsonModeGNS a) =
      embedV plaquetteGNS (characterTraceEmbedding a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

theorem traceMapCauchy_intertwines (x : CauchyGNS wilsonModeGNS) :
    CauchyNull plaquetteGNS
      (plaquetteApplyCauchy (traceMapCauchy x))
      (traceMapCauchy (applyCauchy x)) := by
  intro epsilon hepsilon
  refine ⟨0, fun n _ => ?_⟩
  exact Q'.le_trans' _ 0 epsilon
    (Q'.le_of_eqv (rad_of_veq plaquetteGNS
      (characterTraceEmbedding_intertwines (x.seq n))))
    (Q'.le_of_lt hepsilon)

/-- The literal character trace embedding intertwines the two completed
same-state Wilson transfers. -/
theorem completedCharacterTraceEmbedding_intertwines
    (x : GNSCompletionSpace wilsonModeGNS) :
    completedPlaquetteTransfer (completedCharacterTraceEmbedding x) =
      completedCharacterTraceEmbedding (completedSameStateTransfer x) := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  exact traceMapCauchy_intertwines u

end YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding

#print axioms YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding.characterTraceEmbedding_gram
#print axioms YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding.characterTraceEmbedding_intertwines
#print axioms YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding.characterTraceEmbedding_distSq
#print axioms YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding.plaquetteTransfer_distSq_contraction
#print axioms YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding.completedPlaquetteTransfer
#print axioms YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding.completedCharacterTraceEmbedding
#print axioms YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding.completedCharacterTraceEmbedding_embed
#print axioms YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding.completedCharacterTraceEmbedding_intertwines
