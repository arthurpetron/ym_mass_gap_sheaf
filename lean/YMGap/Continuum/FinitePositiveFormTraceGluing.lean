/-
# Constructive finite trace gluing for a positive form

For a positive symmetric bilinear form, suppose a finite family of coordinate
vectors has diagonal bounds

    B(e_i,e_i) <= rho_i p_i,

with nonnegative rates `rho_i` and nonnegative diagonal weights `p_i`.  Then
every finite linear combination obeys

    B(sum_i c_i e_i, sum_i c_i e_i)
      <= (sum_i rho_i) (sum_i c_i^2 p_i).

Thus the sum of normalized diagonal rates is a complete finite form bound.
The proof recursively applies positive-form head--tail gluing.  Coordinates
with zero rate are handled by radical descent, so the statement needs no
strict-positivity fudge factor and no square roots.

This is the certificate boundary intended for large finite computations:
external code may emit exact rational coordinate rates and their finite sum,
while Lean checks every diagonal inequality and this theorem checks the full
quadratic consequence.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.FinitePositiveFormHeadTailGluing

namespace YMGap.Continuum.FinitePositiveFormTraceGluing

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FinitePositiveFormHeadTailGluing
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite linear combinations and their diagonal budget -/

/-- Assemble a finite linear combination in the displayed list order. -/
def finiteLinearCombination {Index : Type}
    (D : GNSData) (vector : Index → D.V) (coefficient : Index → Q') :
    List Index → D.V
  | [] => D.zero
  | index :: rest =>
      D.add (D.smul (coefficient index) (vector index))
        (finiteLinearCombination D vector coefficient rest)

/-- The stationary diagonal contribution `c_i^2 p_i` of one coordinate. -/
def coordinateDiagonalBudget {Index : Type}
    (weight coefficient : Index → Q') (index : Index) : Q' :=
  (coefficient index * coefficient index) * weight index

theorem coordinateDiagonalBudget_nonnegative
    {Index : Type} (weight coefficient : Index → Q') (index : Index)
    (hweight : (0 : Q') ≤ weight index) :
    (0 : Q') ≤ coordinateDiagonalBudget weight coefficient index := by
  exact Q'.mul_nonneg _ _
    (q_mul_self_nonneg (coefficient index)) hweight

/-! ## 2. One coordinate -/

/-- Scaling a coordinate preserves its rate and moves the square of the
coefficient into the diagonal budget. -/
theorem GNSData.smul_self_le_coordinate_rate
    {Index : Type} (D : GNSData) (vector : Index → D.V)
    (weight rate coefficient : Index → Q') (index : Index)
    (hdiagonal : D.B (vector index) (vector index) ≤
      rate index * weight index) :
    D.B (D.smul (coefficient index) (vector index))
        (D.smul (coefficient index) (vector index)) ≤
      rate index * coordinateDiagonalBudget weight coefficient index := by
  let scalar := coefficient index
  have hscaled :
      (scalar * scalar) * D.B (vector index) (vector index) ≤
        (scalar * scalar) * (rate index * weight index) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiagonal
      (q_mul_self_nonneg scalar)
  have hleft :
      D.B (D.smul scalar (vector index))
          (D.smul scalar (vector index)) ≈
        (scalar * scalar) * D.B (vector index) (vector index) := by
    refine Q'.eqv_trans _
      (scalar * D.B (vector index) (D.smul scalar (vector index))) _
      (D.B_smul_left scalar (vector index)
        (D.smul scalar (vector index))) ?_
    refine Q'.eqv_trans _
      (scalar * (scalar * D.B (vector index) (vector index))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left scalar _ _
        (D.B_smul_right scalar (vector index) (vector index))
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv scalar scalar
          (D.B (vector index) (vector index)))
  have hright :
      (scalar * scalar) * (rate index * weight index) ≈
        rate index * coordinateDiagonalBudget weight coefficient index := by
    unfold coordinateDiagonalBudget
    refine Q'.eqv_trans _
      (((scalar * scalar) * rate index) * weight index) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (scalar * scalar) (rate index) (weight index))) ?_
    refine Q'.eqv_trans _
      ((rate index * (scalar * scalar)) * weight index) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ (weight index)
        (Q'.mul_comm_eqv (scalar * scalar) (rate index))
    · exact Q'.mul_assoc_eqv (rate index) (scalar * scalar) (weight index)
  exact OSReconstructionProgress.le_of_eqv_le hleft
    (OSReconstructionProgress.le_of_le_eqv hscaled hright)

/-! ## 3. The finite trace bound -/

/-- **Finite normalized-trace-to-form theorem.**  Pointwise diagonal rates
sum to a bound for the entire positive quadratic form.  Repeated indices are
allowed and are counted with their displayed multiplicity. -/
theorem finiteLinearCombination_self_le_traceBudget
    {Index : Type} (D : GNSData) (vector : Index → D.V)
    (weight rate coefficient : Index → Q') :
    ∀ indices : List Index,
      (∀ index, index ∈ indices → (0 : Q') ≤ weight index) →
      (∀ index, index ∈ indices → (0 : Q') ≤ rate index) →
      (∀ index, index ∈ indices →
        D.B (vector index) (vector index) ≤
          rate index * weight index) →
      D.B
          (finiteLinearCombination D vector coefficient indices)
          (finiteLinearCombination D vector coefficient indices) ≤
        listQSum rate indices *
          listQSum (coordinateDiagonalBudget weight coefficient) indices
  | [], _, _, _ => by
      exact Q'.le_trans' _ (0 : Q') _
        (Q'.le_of_eqv (D.B_zero_left D.zero))
        (Q'.ge_of_eqv (Q'.zero_mul_eqv 0))
  | index :: rest, hweight, hrate, hdiagonal => by
      let head := D.smul (coefficient index) (vector index)
      let tail := finiteLinearCombination D vector coefficient rest
      let headBudget := coordinateDiagonalBudget weight coefficient index
      let tailBudget :=
        listQSum (coordinateDiagonalBudget weight coefficient) rest
      let tailRate := listQSum rate rest
      have hheadWeight : (0 : Q') ≤ weight index :=
        hweight index List.mem_cons_self
      have hheadRate : (0 : Q') ≤ rate index :=
        hrate index List.mem_cons_self
      have hheadBudget : (0 : Q') ≤ headBudget :=
        coordinateDiagonalBudget_nonnegative weight coefficient index
          hheadWeight
      have htailBudget : (0 : Q') ≤ tailBudget := by
        exact listQSum_nonnegative_on
          (coordinateDiagonalBudget weight coefficient) rest
          (fun item hitem =>
            coordinateDiagonalBudget_nonnegative weight coefficient item
              (hweight item (List.mem_cons_of_mem index hitem)))
      have htailRate : (0 : Q') ≤ tailRate := by
        exact listQSum_nonnegative_on rate rest
          (fun item hitem =>
            hrate item (List.mem_cons_of_mem index hitem))
      have hhead : D.B head head ≤ rate index * headBudget := by
        exact GNSData.smul_self_le_coordinate_rate
          D vector weight rate coefficient index
          (hdiagonal index List.mem_cons_self)
      have htail : D.B tail tail ≤ tailRate * tailBudget := by
        exact finiteLinearCombination_self_le_traceBudget
          D vector weight rate coefficient rest
          (fun item hitem =>
            hweight item (List.mem_cons_of_mem index hitem))
          (fun item hitem =>
            hrate item (List.mem_cons_of_mem index hitem))
          (fun item hitem =>
            hdiagonal item (List.mem_cons_of_mem index hitem))
      exact FinitePositiveFormHeadTailGluing.GNSData.add_self_le_of_head_tail_nonnegative
        D head tail (rate index) tailRate headBudget tailBudget
        hheadRate htailRate hheadBudget htailBudget hhead htail

end YMGap.Continuum.FinitePositiveFormTraceGluing

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.FinitePositiveFormTraceGluing.coordinateDiagonalBudget_nonnegative
#print axioms
  YMGap.Continuum.FinitePositiveFormTraceGluing.GNSData.smul_self_le_coordinate_rate
#print axioms
  YMGap.Continuum.FinitePositiveFormTraceGluing.finiteLinearCombination_self_le_traceBudget
