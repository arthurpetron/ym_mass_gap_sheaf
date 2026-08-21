/-
# Exact cutoff-two obstruction to the one-sixteenth upper form

The verified 65-state cutoff-two physical sector already contains a literal
weighted-mean-zero coordinate on which `(1/16) D - K` is negative.  Hence the
canonical upper-edge reduced matrix at this finite cutoff is not positive
semidefinite, although the independently scouted lower-edge form is positive.

This is an exact obstruction to an all-cutoff `1/16` certificate and to using
this cutoff as a cofinal anchor.  It does not by itself refute the weaker
possibility of `1/16` estimates on some later unbounded cutoff subsequence.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.FiniteRationalHeadCenteredPullback

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSixteenthObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteRationalHeadCenteredPullback
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalPenalizedMatrix
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem rangeNodupLocal (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyk : y = k := List.mem_singleton.mp hy
      rw [hxy, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

private theorem listQSum_ite_single
    {A : Type} [DecidableEq A] (selected : A) (value : A → Q') :
    ∀ items : List A,
      items.Nodup → selected ∈ items →
      listQSum
          (fun item => if selected = item then value item else 0)
          items ≈
        value selected
  | [], _hnodup, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum]
        have htailZero :
            listQSum
                (fun item => if selected = item then value item else 0)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _item => (0 : Q')) tail) _ ?_ ?_
          · apply listQSum_congr_on
            intro item hitem
            rw [if_neg]
            exact Q'.eqv_refl 0
            intro heq
            exact hparts.1 (heq ▸ hitem)
          · exact listQSum_zero tail
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hne : selected ≠ head := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hne]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr_left _ _ _
            (listQSum_ite_single selected value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

private def finiteCoordinateUnit (selected index : Nat) : Q' :=
  if selected = index then 1 else 0

private theorem finiteMatrixQuadratic_coordinateUnit
    (n : Nat) (matrix : Nat → Nat → Q')
    (selected : Nat) (hselected : selected < n) :
    finiteMatrixQuadratic n matrix (finiteCoordinateUnit selected) ≈
      matrix selected selected := by
  unfold finiteMatrixQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun i => if selected = i then matrix i selected else 0)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro i _hi
    refine Q'.eqv_trans _
      (listQSum
        (fun j =>
          if selected = i then
            if selected = j then matrix i j else 0
          else 0)
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr_on
      intro j _hj
      by_cases his : selected = i
      · rw [if_pos his]
        by_cases hjs : selected = j
        · rw [if_pos hjs]
          unfold finiteCoordinateUnit
          rw [if_pos his, if_pos hjs]
          refine Q'.eqv_trans _ (1 * matrix i j) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv 1)
          · exact Q'.one_mul_eqv _
        · rw [if_neg hjs]
          unfold finiteCoordinateUnit
          rw [if_pos his, if_neg hjs]
          refine Q'.eqv_trans _ (0 * matrix i j) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv 1)
          · exact Q'.zero_mul_eqv _
      · rw [if_neg his]
        unfold finiteCoordinateUnit
        rw [if_neg his]
        refine Q'.eqv_trans _ (0 * matrix i j) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _)
        · exact Q'.zero_mul_eqv _
    · by_cases his : selected = i
      · simpa only [if_pos his] using
          (listQSum_ite_single selected (matrix i)
            (List.range n) (rangeNodupLocal n)
            (List.mem_range.mpr hselected))
      · simpa only [if_neg his] using
          (listQSum_zero (List.range n))
  · exact listQSum_ite_single selected
      (fun i => matrix i selected) (List.range n)
      (rangeNodupLocal n) (List.mem_range.mpr hselected)

/-- The literal rational rate tested by the physical finite-gap compiler. -/
def cutoffTwoSectorSixteenth : Q' := Q'.mkPos 1 16 (by decide)

/-- The head row sum in the exact 65-state sector is strictly positive. -/
theorem cutoffTwoSectorRawRowSum_zero_pos :
    (0 : Q') < cutoffTwoSectorRawRowSum 0 := by
  decide

/-- Tail coordinate one (full sector index two) is already a strict negative
diagonal of the canonical head-centered upper matrix at rate `1/16`. -/
theorem cutoffTwoSectorUpperSixteenth_coordinateOne_neg :
    finiteHeadCenteredUpperMatrix
        64 cutoffTwoSectorSixteenth
        cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
        cutoffTwoSectorRawRowSum_zero_pos 1 1 < 0 := by
  have hdiagonal := finiteHeadCenteredMatrix_diagonal
    64 cutoffTwoSectorRawRowSum cutoffTwoSectorRawRowSum_zero_pos
    (finiteUpperPenalizedMatrix cutoffTwoSectorSixteenth
      cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel)
    1 (by decide)
  have hnegative :
      let a := Q'.divPos (-(cutoffTwoSectorRawRowSum 2))
        (cutoffTwoSectorRawRowSum 0)
        cutoffTwoSectorRawRowSum_zero_pos
      (finiteUpperPenalizedMatrix cutoffTwoSectorSixteenth
          cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel 0 0 * a +
        finiteUpperPenalizedMatrix cutoffTwoSectorSixteenth
          cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel 0 2) * a +
        (finiteUpperPenalizedMatrix cutoffTwoSectorSixteenth
            cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel 2 0 * a +
          finiteUpperPenalizedMatrix cutoffTwoSectorSixteenth
            cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel 2 2) < 0 := by
    decide
  exact Q'.lt_of_le_of_lt (Q'.le_of_eqv hdiagonal) hnegative

/-- The canonical head-centered restriction for the exact raw sector table. -/
def cutoffTwoSectorCanonicalRestriction :
    FiniteCenteredTwoSidedRestriction
      65 cutoffTwoSectorSixteenth
      cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel :=
  finiteCanonicalHeadCenteredRestriction
    64 cutoffTwoSectorSixteenth
    cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
    cutoffTwoSectorRawRowSum_zero_pos

/-- The displayed upper matrix cannot be nonnegative on every reduced
coefficient vector. -/
theorem cutoffTwoSectorUpperSixteenth_not_nonnegative :
    ¬ ∀ coefficient : Nat → Q',
      (0 : Q') ≤ finiteMatrixQuadratic 64
        (finiteHeadCenteredUpperMatrix
          64 cutoffTwoSectorSixteenth
          cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
          cutoffTwoSectorRawRowSum_zero_pos)
        coefficient := by
  intro hnonnegative
  have hunit := hnonnegative (finiteCoordinateUnit 1)
  have hdiagonal := finiteMatrixQuadratic_coordinateUnit
    64
    (finiteHeadCenteredUpperMatrix
      64 cutoffTwoSectorSixteenth
      cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
      cutoffTwoSectorRawRowSum_zero_pos)
    1 (by decide)
  have hzeroLeDiagonal :
      (0 : Q') ≤
        finiteHeadCenteredUpperMatrix
          64 cutoffTwoSectorSixteenth
          cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
          cutoffTwoSectorRawRowSum_zero_pos 1 1 :=
    Q'.le_trans' _ _ _ hunit (Q'.le_of_eqv hdiagonal)
  exact (Int.not_lt_of_ge hzeroLeDiagonal)
    cutoffTwoSectorUpperSixteenth_coordinateOne_neg

/-- Consequently no ordinary two-sided LDL certificate can inhabit the
canonical cutoff-two sector restriction. -/
theorem no_cutoffTwoSectorCanonicalRestrictionLDLCertificate :
    FiniteCenteredRestrictionLDLCertificate
      cutoffTwoSectorCanonicalRestriction → False := by
  intro certificate
  apply cutoffTwoSectorUpperSixteenth_not_nonnegative
  intro coefficient
  exact finiteMatrixQuadratic_nonnegative_of_ldl_check
    certificate.upperCheck coefficient

/-- Nor can the shardable cleared-denominator LDL interface be inhabited. -/
theorem no_cutoffTwoSectorCanonicalRestrictionClearedLDLCertificate :
    FiniteCenteredRestrictionClearedLDLCertificate
      cutoffTwoSectorCanonicalRestriction → False := by
  intro certificate
  apply cutoffTwoSectorUpperSixteenth_not_nonnegative
  intro coefficient
  exact finiteMatrixQuadratic_nonnegative_of_cleared_ldl_check
    certificate.upperRowsCheck certificate.upperTriangular
    certificate.upperDiagonalCheck coefficient

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSixteenthObstruction

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSixteenthObstruction.cutoffTwoSectorUpperSixteenth_coordinateOne_neg
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSixteenthObstruction.no_cutoffTwoSectorCanonicalRestrictionLDLCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSixteenthObstruction.no_cutoffTwoSectorCanonicalRestrictionClearedLDLCertificate
