/-
# Exact two-row cutoff-one sufficient statistic

The cutoff-one vacuum row and the explicit lower-cube row are both supported
on the vacuum boundary word.  Their row masses are respectively one and the
sixth power of the fundamental heat-kernel coefficient.  Consequently their
cross-multiplied pairwise residual vanishes on every binary boundary word.

This certifies one exact two-row proportional block inside the genuine BF4
matrix.  It does not assert that all retained rows belong to this block.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeStatistics

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumStatistics
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteRegularizedRankOneStatistics
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_zero_of_eqv {left right : Q'}
    (h : left ≈ right) : left + -right ≈ 0 := by
  exact Q'.eqv_trans _ (right + -right) _
    (Q'.add_eqv_congr' h (Q'.eqv_refl _))
    (Q'.add_neg_self_eqv right)

/-- Every row has zero pairwise residual with itself, independently of the
cutoff-one specialization. -/
theorem centralBoundaryPairwiseRowCrossTerm_self_eqv_zero
    (w : Q') (K half : Nat)
    (source boundary : EdgeLabelling) :
    centralBoundaryPairwiseRowCrossTerm
        w K half source source boundary ≈ 0 := by
  unfold centralBoundaryPairwiseRowCrossTerm finitePairwiseRowCrossTerm
  exact Q'.add_neg_self_eqv _

/-- Vacuum-to-cube cross residual: exact cancellation of the two delta
rows after multiplying by their row masses. -/
theorem centralBoundaryPairwiseRowCrossTerm_cutoffOne_vacuum_cube_word_eqv_zero
    (w : Q') (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    centralBoundaryPairwiseRowCrossTerm
        w 1 0 zeroEdgeLabelling centralLowerCubeState
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      0 := by
  refine Q'.eqv_trans _
    (centralHalfAmplitudeBoundaryRowMass w 1 0 centralLowerCubeState *
        binaryVacuumWordWeight word +
      -centralHalfAmplitude w 1 0 centralLowerCubeState
        (wordToEdgeLabelling (centralFixedFaceIds 0) word)) _
    (centralBoundaryPairwiseRowCrossTerm_cutoffOne_vacuum_word_eqv
      w centralLowerCubeState word hword) ?_
  refine sub_eqv_zero_of_eqv ?_
  refine Q'.eqv_trans _
    ((coeffW w 1) ^ 6 * binaryVacuumWordWeight word) _
    (Q'.mul_eqv_congr_right _ _ _
      (centralHalfAmplitudeBoundaryRowMass_cutoffOne_cube_eqv w)) ?_
  refine Q'.eqv_trans _
    (binaryVacuumWordWeight word * (coeffW w 1) ^ 6) _
    (Q'.mul_comm_eqv _ _) ?_
  exact Q'.eqv_symm
    (centralHalfAmplitude_cutoffOne_cube_word_eqv_delta w word hword)

/-- Cube-to-vacuum cross residual, proved directly in the reverse ordering. -/
theorem centralBoundaryPairwiseRowCrossTerm_cutoffOne_cube_vacuum_word_eqv_zero
    (w : Q') (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    centralBoundaryPairwiseRowCrossTerm
        w 1 0 centralLowerCubeState zeroEdgeLabelling
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      0 := by
  unfold centralBoundaryPairwiseRowCrossTerm finitePairwiseRowCrossTerm
  apply sub_eqv_zero_of_eqv
  let boundary :=
    wordToEdgeLabelling (centralFixedFaceIds 0) word
  let delta := binaryVacuumWordWeight word
  let activity := (coeffW w 1) ^ 6
  have hleft :
      centralHalfAmplitudeBoundaryRowMass w 1 0 zeroEdgeLabelling *
          centralHalfAmplitude w 1 0 centralLowerCubeState boundary ≈
        1 * (delta * activity) := by
    refine Q'.eqv_trans _
      (1 * centralHalfAmplitude w 1 0 centralLowerCubeState boundary) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ 1 _
        (centralHalfAmplitudeBoundaryRowMass_cutoffOne_vacuum_eqv_one w)
    · exact Q'.mul_eqv_congr_left 1 _ _
        (centralHalfAmplitude_cutoffOne_cube_word_eqv_delta w word hword)
  have hright :
      delta * activity ≈
        centralHalfAmplitudeBoundaryRowMass w 1 0 centralLowerCubeState *
          centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary := by
    refine Q'.eqv_trans _ (activity * delta) _
      (Q'.mul_comm_eqv _ _) ?_
    refine Q'.eqv_trans _
      (centralHalfAmplitudeBoundaryRowMass w 1 0 centralLowerCubeState *
        delta) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (centralHalfAmplitudeBoundaryRowMass_cutoffOne_cube_eqv w))
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (centralHalfAmplitude_cutoffOne_vacuum_word_eqv_delta
            w word hword))
  exact Q'.eqv_trans _ (1 * (delta * activity)) _ hleft
    (Q'.eqv_trans _ (delta * activity) _ (Q'.one_mul_eqv _) hright)

/-- The exact two-source block formed by the vacuum and lower-cube rows. -/
def cutoffOneVacuumCubeSourceBlock : List EdgeLabelling :=
  [zeroEdgeLabelling, centralLowerCubeState]

theorem cutoffOneVacuumCubeSourceBlock_nodup :
    cutoffOneVacuumCubeSourceBlock.Nodup := by
  simp only [cutoffOneVacuumCubeSourceBlock, List.nodup_cons,
    List.mem_singleton, List.not_mem_nil]
  exact ⟨Ne.symm centralLowerCubeState_ne_zero, (fun h => h),
    List.nodup_nil⟩

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeStatistics

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeStatistics.centralBoundaryPairwiseRowCrossTerm_self_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeStatistics.centralBoundaryPairwiseRowCrossTerm_cutoffOne_vacuum_cube_word_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeStatistics.centralBoundaryPairwiseRowCrossTerm_cutoffOne_cube_vacuum_word_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeStatistics.cutoffOneVacuumCubeSourceBlock_nodup
