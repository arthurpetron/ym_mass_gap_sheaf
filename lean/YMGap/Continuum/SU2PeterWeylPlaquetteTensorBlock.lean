/-
# The fundamental SU(2) plaquette tensor block

Cutting a plaquette through two opposite links exposes the Peter--Weyl
half-plaquette carrier `1 ⊕ (V_1 ⊗ V_1*)`.  The vacuum contributes one
coordinate and the fundamental representation contributes its four genuine
matrix coefficients.  This file constructs that five-dimensional carrier
from the SAME non-unit Wilson kernel and bare Haar state used by
`SU2PeterWeylWilsonBlock`.

For a fundamental matrix coefficient the two Haar contractions contribute
`1/dim_1^2`, while `coeffW = dim_1 * lambda_1`.  Its reflected norm is thus

    coeffW / dim_1^2 = lambda_1 / dim_1 = 1/16.

The character is the trace `D_00 + D_11`, so its norm is `2/16 = 1/8`, exactly
the character norm in the predecessor.  One further plaquette multiplies all
four fundamental matrix coefficients by the SAME channel eigenvalue `1/8`.
The resulting transfer is nonidentity, positive, self-adjoint, and
contractive.  No independent auxiliary state or ambient isometry is used.

Honest scope: this is one cut plaquette and the vacuum plus fundamental
Peter--Weyl sectors only.  It does not assert closure under the full plaquette
algebra, uniformity in volume, or construction of the four-dimensional
interacting continuum measure.  Volume tensorization is treated separately.
-/

import YMGap.Continuum.SU2PeterWeylWilsonBlock
import YMGap.Continuum.PositiveTimeCompressedTransfer

namespace YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.SU2PeterWeylWilsonBlock

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

/-! ## Exact matrix-coefficient normalization -/

def sixteenth : Q' := Q'.mkPos 1 16 (by decide)
def oneTwentyEighth : Q' := Q'.mkPos 1 128 (by decide)

/-- `lambda_1 / dim_1`, derived from the predecessor's literal bare-Haar
Wilson channel. -/
def fundamentalMatrixWeight : Q' :=
  bareHaarLinkEntry coupling 1 1 * Q'.invSucc 1

theorem fundamentalMatrixWeight_exact :
    fundamentalMatrixWeight ≈ sixteenth := by decide

/-- Normalization audit: this is literally
`coeffW_1 * (1/dim_1) * (1/dim_1)`.  The first Schur factor is already in
`bareHaarLinkEntry`; the second resolves the two matrix indices exposed by the
plaquette cut. -/
theorem fundamentalMatrixWeight_two_schur_factors :
    fundamentalMatrixWeight ≈
      (BondMovingStep.coeffW coupling 1 * Q'.invSucc 1) * Q'.invSucc 1 := by
  unfold fundamentalMatrixWeight bareHaarLinkEntry
  apply Q'.mul_eqv_congr_right
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (BondMovingStep.coeffW coupling 1 * Q'.invSucc 1) _ _
      bareHaar_fundamental_pairing)
    (Q'.mul_one_eqv _)

theorem fundamentalMatrixWeight_pos :
    (0 : Q') < fundamentalMatrixWeight := by decide

/-- One more use of the same plaquette kernel gives
`(lambda_1 / dim_1) * lambda_1 = 1/128`. -/
def translatedMatrixWeight : Q' :=
  fundamentalMatrixWeight * bareHaarLinkEntry coupling 1 1

theorem translatedMatrixWeight_exact :
    translatedMatrixWeight ≈ oneTwentyEighth := by decide

/-! ## The five Peter--Weyl coordinates -/

/-- Coordinates `(vacuum, D00, D01, D10, D11)`. -/
abbrev PlaquetteVec := Q' × (Q' × (Q' × (Q' × Q')))

def matrixDot (a b : PlaquetteVec) : Q' :=
  a.2.1 * b.2.1 +
    (a.2.2.1 * b.2.2.1 +
      (a.2.2.2.1 * b.2.2.2.1 + a.2.2.2.2 * b.2.2.2.2))

/-- The literal plaquette reflection Gram: vacuum plus the four entries of
`V_1 ⊗ V_1*`, each with the Schur weight `lambda_1/dim_1`. -/
def plaquetteGram (a b : PlaquetteVec) : Q' :=
  a.1 * b.1 + fundamentalMatrixWeight * matrixDot a b

theorem plaquetteGram_diagonal (a b : PlaquetteVec) :
    plaquetteGram a b ≈ a.1 * b.1 + sixteenth * matrixDot a b :=
  QPoly.q_add_congr (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _ _ fundamentalMatrixWeight_exact)

theorem plaquetteGram_nonneg (a : PlaquetteVec) :
    (0 : Q') ≤ plaquetteGram a a := by
  have h00 := SumOfSquares.q_mul_self_nonneg a.2.1
  have h01 := SumOfSquares.q_mul_self_nonneg a.2.2.1
  have h10 := SumOfSquares.q_mul_self_nonneg a.2.2.2.1
  have h11 := SumOfSquares.q_mul_self_nonneg a.2.2.2.2
  have hm : (0 : Q') ≤ matrixDot a a :=
    Q'.zero_le_add _ _ h00
      (Q'.zero_le_add _ _ h01 (Q'.zero_le_add _ _ h10 h11))
  exact Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg a.1)
    (Q'.mul_nonneg _ _ (Q'.le_of_lt fundamentalMatrixWeight_pos) hm)

/-! ## A genuine GNS datum for the plaquette block -/

def vacuumLine : GNSData := qWeightGNS 1 (by decide)
def matrixLine : GNSData :=
  qWeightGNS fundamentalMatrixWeight (Q'.le_of_lt fundamentalMatrixWeight_pos)

/-- The direct sum here is the linear Peter--Weyl coefficient space.  It is
not the nonlinear pointwise pure-product carrier refuted elsewhere. -/
abbrev plaquetteGNS : GNSData :=
  gnsProduct vacuumLine
    (gnsProduct matrixLine (gnsProduct matrixLine (gnsProduct matrixLine matrixLine)))

theorem plaquetteGNS_B_eq_gram (a b : PlaquetteVec) :
    plaquetteGNS.B a b ≈ plaquetteGram a b := by
  unfold plaquetteGNS gnsProduct vacuumLine matrixLine qWeightGNS plaquetteGram matrixDot
  ring_qeqv

theorem plaquette_reflection_positive (a : PlaquetteVec) :
    (0 : Q') ≤ plaquetteGNS.B a a := plaquetteGNS.self_nonneg a

/-! ## Same-state translated moment and transfer -/

def plaquetteTransfer (a : PlaquetteVec) : PlaquetteVec :=
  (a.1,
    (eighth * a.2.1,
      (eighth * a.2.2.1,
        (eighth * a.2.2.2.1, eighth * a.2.2.2.2))))

def translatedPlaquetteMoment (a b : PlaquetteVec) : Q' :=
  a.1 * b.1 + translatedMatrixWeight * matrixDot a b

theorem translatedPlaquetteMoment_exact (a b : PlaquetteVec) :
    translatedPlaquetteMoment a b ≈
      a.1 * b.1 + oneTwentyEighth * matrixDot a b :=
  QPoly.q_add_congr (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _ _ translatedMatrixWeight_exact)

theorem matrixDot_transfer_left (a b : PlaquetteVec) :
    matrixDot (plaquetteTransfer a) b ≈ eighth * matrixDot a b := by
  unfold matrixDot plaquetteTransfer
  ring_qeqv

/-- Pairing the compressed translate in the one-plaquette GNS form is exactly
the two-plaquette moment derived from a second use of the SAME Wilson kernel. -/
theorem same_state_plaquette_compression (a b : PlaquetteVec) :
    plaquetteGNS.B (plaquetteTransfer a) b ≈
      translatedPlaquetteMoment a b := by
  refine Q'.eqv_trans _ _ _ (plaquetteGNS_B_eq_gram _ b) ?_
  refine Q'.eqv_trans _
    (a.1 * b.1 + fundamentalMatrixWeight * (eighth * matrixDot a b)) _ ?_ ?_
  · unfold plaquetteGram plaquetteTransfer
    exact QPoly.q_add_congr (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left fundamentalMatrixWeight _ _
        (matrixDot_transfer_left a b))
  · unfold translatedPlaquetteMoment translatedMatrixWeight
    refine QPoly.q_add_congr (Q'.eqv_refl _) ?_
    refine Q'.eqv_trans _
      ((fundamentalMatrixWeight * eighth) * matrixDot a b) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left fundamentalMatrixWeight _ _
        (Q'.eqv_symm bareHaarLinkEntry_fundamental))

theorem plaquetteTransfer_map_veq {a b : PlaquetteVec}
    (h : plaquetteGNS.veq a b) :
    plaquetteGNS.veq (plaquetteTransfer a) (plaquetteTransfer b) :=
  ⟨h.1,
    ⟨Q'.mul_eqv_congr_left eighth _ _ h.2.1,
      ⟨Q'.mul_eqv_congr_left eighth _ _ h.2.2.1,
        ⟨Q'.mul_eqv_congr_left eighth _ _ h.2.2.2.1,
          Q'.mul_eqv_congr_left eighth _ _ h.2.2.2.2⟩⟩⟩⟩

theorem plaquetteTransfer_map_add (a b : PlaquetteVec) :
    plaquetteGNS.veq (plaquetteTransfer (plaquetteGNS.add a b))
      (plaquetteGNS.add (plaquetteTransfer a) (plaquetteTransfer b)) := by
  unfold plaquetteTransfer plaquetteGNS gnsProduct vacuumLine matrixLine qWeightGNS
  exact ⟨Q'.eqv_refl _,
    ⟨by ring_qeqv, ⟨by ring_qeqv, ⟨by ring_qeqv, by ring_qeqv⟩⟩⟩⟩

theorem plaquetteTransfer_map_smul (s : Q') (a : PlaquetteVec) :
    plaquetteGNS.veq (plaquetteTransfer (plaquetteGNS.smul s a))
      (plaquetteGNS.smul s (plaquetteTransfer a)) := by
  unfold plaquetteTransfer plaquetteGNS gnsProduct vacuumLine matrixLine qWeightGNS
  exact ⟨Q'.eqv_refl _,
    ⟨by ring_qeqv, ⟨by ring_qeqv, ⟨by ring_qeqv, by ring_qeqv⟩⟩⟩⟩

theorem plaquetteTransfer_selfAdjoint (a b : PlaquetteVec) :
    plaquetteGNS.B (plaquetteTransfer a) b ≈
      plaquetteGNS.B a (plaquetteTransfer b) := by
  refine Q'.eqv_trans _ _ _ (plaquetteGNS_B_eq_gram _ b) ?_
  refine Q'.eqv_trans _ _ _ (show
      plaquetteGram (plaquetteTransfer a) b ≈
        plaquetteGram a (plaquetteTransfer b) by
      unfold plaquetteGram plaquetteTransfer matrixDot
      ring_qeqv) ?_
  exact Q'.eqv_symm (plaquetteGNS_B_eq_gram a _)

theorem plaquetteTransfer_positive (a : PlaquetteVec) :
    (0 : Q') ≤ plaquetteGNS.B (plaquetteTransfer a) a := by
  have h00 := SumOfSquares.q_mul_self_nonneg a.2.1
  have h01 := SumOfSquares.q_mul_self_nonneg a.2.2.1
  have h10 := SumOfSquares.q_mul_self_nonneg a.2.2.2.1
  have h11 := SumOfSquares.q_mul_self_nonneg a.2.2.2.2
  have hm : (0 : Q') ≤ matrixDot a a :=
    Q'.zero_le_add _ _ h00
      (Q'.zero_le_add _ _ h01 (Q'.zero_le_add _ _ h10 h11))
  have ht : (0 : Q') ≤ translatedMatrixWeight := by decide
  have hraw : (0 : Q') ≤ translatedPlaquetteMoment a a :=
    Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg a.1)
      (Q'.mul_nonneg _ _ ht hm)
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_of_eqv (Q'.eqv_symm (same_state_plaquette_compression a a)))

private theorem scaled_square_le (x : Q') :
    fundamentalMatrixWeight * ((eighth * x) * (eighth * x)) ≤
      fundamentalMatrixWeight * (x * x) := by
  have hx := SumOfSquares.q_mul_self_nonneg x
  have he : eighth * eighth ≤ (1 : Q') := by decide
  have hc := Q'.mul_le_mul_of_nonneg_right
    (eighth * eighth) 1 (x * x) he hx
  have hc' : (eighth * eighth) * (x * x) ≤ x * x :=
    Q'.le_trans' _ _ _ hc (Q'.le_of_eqv (Q'.one_mul_eqv (x * x)))
  have hw : (0 : Q') ≤ fundamentalMatrixWeight :=
    Q'.le_of_lt fundamentalMatrixWeight_pos
  refine Q'.le_trans' _
    (fundamentalMatrixWeight * ((eighth * eighth) * (x * x))) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left fundamentalMatrixWeight _ _ (by ring_qeqv))
  · exact Q'.mul_le_mul_of_nonneg_left _ _ fundamentalMatrixWeight hc' hw

private theorem raw_scaled_square_le (x : Q') :
    (eighth * x) * (eighth * x) ≤ x * x := by
  have hx := SumOfSquares.q_mul_self_nonneg x
  have he : eighth * eighth ≤ (1 : Q') := by decide
  have hc := Q'.mul_le_mul_of_nonneg_right
    (eighth * eighth) 1 (x * x) he hx
  refine Q'.le_trans' _ ((eighth * eighth) * (x * x)) _
    (Q'.le_of_eqv (by ring_qeqv)) ?_
  exact Q'.le_trans' _ _ _ hc (Q'.le_of_eqv (Q'.one_mul_eqv (x * x)))

theorem matrixDot_transfer_diag_le (a : PlaquetteVec) :
    matrixDot (plaquetteTransfer a) (plaquetteTransfer a) ≤ matrixDot a a := by
  unfold matrixDot plaquetteTransfer
  exact Q'.add_le_add (raw_scaled_square_le a.2.1)
    (Q'.add_le_add (raw_scaled_square_le a.2.2.1)
      (Q'.add_le_add (raw_scaled_square_le a.2.2.2.1)
        (raw_scaled_square_le a.2.2.2.2)))

def unscaledPlaquetteNorm (a : PlaquetteVec) : Q' :=
  a.1 * a.1 +
    (fundamentalMatrixWeight * (a.2.1 * a.2.1) +
      (fundamentalMatrixWeight * (a.2.2.1 * a.2.2.1) +
        (fundamentalMatrixWeight * (a.2.2.2.1 * a.2.2.2.1) +
          fundamentalMatrixWeight * (a.2.2.2.2 * a.2.2.2.2))))

theorem plaquetteGram_self_eq_unscaled (a : PlaquetteVec) :
    plaquetteGram a a ≈ unscaledPlaquetteNorm a := by
  unfold plaquetteGram matrixDot unscaledPlaquetteNorm
  ring_qeqv

theorem plaquetteTransfer_contraction (a : PlaquetteVec) :
    plaquetteGNS.B (plaquetteTransfer a) (plaquetteTransfer a) ≤
      plaquetteGNS.B a a := by
  have hw : (0 : Q') ≤ fundamentalMatrixWeight :=
    Q'.le_of_lt fundamentalMatrixWeight_pos
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ fundamentalMatrixWeight
    (matrixDot_transfer_diag_le a) hw
  have hg : plaquetteGram (plaquetteTransfer a) (plaquetteTransfer a) ≤
      plaquetteGram a a := by
    unfold plaquetteGram plaquetteTransfer
    exact Q'.add_le_add (Q'.le_refl' _) hm
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (plaquetteGNS_B_eq_gram _ _)) hg)
    (Q'.le_of_eqv (Q'.eqv_symm (plaquetteGNS_B_eq_gram a a)))

/-! ## Nondegeneracy and the character trace -/

def vacuumMode : PlaquetteVec := (1, (0, (0, (0, 0))))
def matrix00Mode : PlaquetteVec := (0, (1, (0, (0, 0))))
def matrix01Mode : PlaquetteVec := (0, (0, (1, (0, 0))))
def matrix10Mode : PlaquetteVec := (0, (0, (0, (1, 0))))
def matrix11Mode : PlaquetteVec := (0, (0, (0, (0, 1))))
def fundamentalCharacterMode : PlaquetteVec := (0, (1, (0, (0, 1))))

theorem matrix00_norm :
    plaquetteGNS.B matrix00Mode matrix00Mode ≈ sixteenth := by decide

/-- The two diagonal matrix entries reconstruct the fundamental character
with norm `2 * (1/16) = 1/8`, matching the predecessor exactly. -/
theorem fundamentalCharacter_norm :
    plaquetteGNS.B fundamentalCharacterMode fundamentalCharacterMode ≈
      eighth := by decide

theorem fundamentalCharacter_matches_link_norm :
    plaquetteGNS.B fundamentalCharacterMode fundamentalCharacterMode ≈
      wilsonModeGNS.B fundamentalMode fundamentalMode := by
  exact Q'.eqv_trans _ _ _ fundamentalCharacter_norm
    (Q'.eqv_symm fundamental_norm)

theorem plaquetteTransfer_vacuum_eigen :
    plaquetteGNS.veq (plaquetteTransfer vacuumMode) vacuumMode := by
  unfold plaquetteGNS gnsProduct vacuumLine matrixLine qWeightGNS
    plaquetteTransfer vacuumMode
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩

theorem plaquetteTransfer_character_eigen :
    plaquetteGNS.veq (plaquetteTransfer fundamentalCharacterMode)
      (plaquetteGNS.smul eighth fundamentalCharacterMode) := by
  unfold plaquetteGNS gnsProduct vacuumLine matrixLine qWeightGNS
    plaquetteTransfer fundamentalCharacterMode
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩

/-- Explicit normalization/evolution audit: every one of the four genuine
fundamental matrix coefficients, not only their trace, has eigenvalue `1/8`. -/
theorem plaquetteTransfer_all_four_matrix_eigen :
    plaquetteGNS.veq (plaquetteTransfer matrix00Mode)
        (plaquetteGNS.smul eighth matrix00Mode) ∧
      plaquetteGNS.veq (plaquetteTransfer matrix01Mode)
        (plaquetteGNS.smul eighth matrix01Mode) ∧
      plaquetteGNS.veq (plaquetteTransfer matrix10Mode)
        (plaquetteGNS.smul eighth matrix10Mode) ∧
      plaquetteGNS.veq (plaquetteTransfer matrix11Mode)
        (plaquetteGNS.smul eighth matrix11Mode) := by
  unfold plaquetteGNS gnsProduct vacuumLine matrixLine qWeightGNS
    plaquetteTransfer matrix00Mode matrix01Mode matrix10Mode matrix11Mode
  exact ⟨⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩,
    ⟨⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩,
      ⟨⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩,
        ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩⟩⟩⟩

theorem matrix00_qmk_ne_zero :
    plaquetteGNS.qmk matrix00Mode ≠ plaquetteGNS.qmk plaquetteGNS.zero := by
  intro h
  have hr : plaquetteGNS.rad matrix00Mode plaquetteGNS.zero := Quotient.exact h
  have hsub : plaquetteGNS.veq
      (plaquetteGNS.sub matrix00Mode plaquetteGNS.zero) matrix00Mode := by
    unfold GNSData.sub plaquetteGNS gnsProduct vacuumLine matrixLine qWeightGNS
      matrix00Mode
    exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩
  have hdiag := plaquetteGNS.B_diag_congr hsub
  have he : sixteenth ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm matrix00_norm)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hdiag) hr)
  exact (by decide : ¬ ((sixteenth : Q').eqv 0)) he

theorem plaquetteTransfer_nonidentity : plaquetteTransfer ≠ id := by
  intro h
  have hv := congrFun h matrix00Mode
  have h00 := congrArg (fun x : PlaquetteVec => x.2.1) hv
  exact (by decide : ¬ (eighth = (1 : Q'))) h00

end YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock

#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.fundamentalMatrixWeight_exact
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.fundamentalMatrixWeight_two_schur_factors
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.plaquetteGNS_B_eq_gram
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.plaquette_reflection_positive
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.same_state_plaquette_compression
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.plaquetteTransfer_selfAdjoint
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.plaquetteTransfer_positive
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.plaquetteTransfer_contraction
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.fundamentalCharacter_matches_link_norm
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.plaquetteTransfer_all_four_matrix_eigen
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.matrix00_qmk_ne_zero
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock.plaquetteTransfer_nonidentity
