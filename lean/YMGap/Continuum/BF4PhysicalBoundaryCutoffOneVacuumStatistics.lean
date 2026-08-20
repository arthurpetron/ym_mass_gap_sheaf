/-
# Cutoff-one vacuum-row sufficient statistics

The exact cutoff-one contraction identifies the physical vacuum row with a
Boolean delta and proves that its total boundary mass is one.  This file
threads those two facts into the canonical regularized rank-one and finite
statistics layers.

For a decoded binary boundary word, the rank-one projection of the vacuum
row is exactly the canonical profile.  Its pairwise residual against any
retained source reduces to

  other row mass * vacuum delta - other boundary entry.

Thus the original `2^24`-entry vacuum row no longer appears in the remaining
source sum.  The result is still a finite `K = 1`, half-extent-zero reduction;
it does not bound the other rows or provide cutoff or volume uniformity.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
import YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumStatistics

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRegularizedRankOneStatistics
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact rank-one action of the physical vacuum row -/

/-- The generic finite-row statistic sees the same exact mass-one theorem. -/
theorem finiteRowMass_cutoffOne_vacuum_eqv_one (w : Q') :
    finiteRowMass
        (centralBoundaryChannels 1 0)
        (centralHalfAmplitude w 1 0)
        zeroEdgeLabelling ≈
      1 := by
  exact centralHalfAmplitudeBoundaryRowMass_cutoffOne_vacuum_eqv_one w

/-- Since the physical vacuum row has mass one, its canonical rank-one
projection is exactly the normalized aggregate boundary profile. -/
theorem centralHalfAmplitude_cutoffOne_vacuum_regularizedRankOneAction_eqv_profile
    {w : Q'} (hw : (0 : Q') ≤ w)
    {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (boundary : EdgeLabelling) :
    centralHalfAmplitudeBoundaryAction
        w 1 0
        (centralRegularizedBoundaryRankOneKernel
          w hw 1 0 pseudocount pseudocount_pos)
        zeroEdgeLabelling boundary ≈
      centralRegularizedBoundaryProfile
        w hw 1 0 pseudocount pseudocount_pos boundary := by
  refine Q'.eqv_trans _
    (centralHalfAmplitudeBoundaryRowMass w 1 0 zeroEdgeLabelling *
      centralRegularizedBoundaryProfile
        w hw 1 0 pseudocount pseudocount_pos boundary) _
    (centralHalfAmplitude_regularizedRankOneAction_eqv
      hw 1 0 pseudocount_pos zeroEdgeLabelling boundary) ?_
  refine Q'.eqv_trans _
    (1 * centralRegularizedBoundaryProfile
      w hw 1 0 pseudocount pseudocount_pos boundary) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ 1 _
      (centralHalfAmplitudeBoundaryRowMass_cutoffOne_vacuum_eqv_one w)
  · exact Q'.one_mul_eqv _

/-- On a decoded binary boundary word, the physical vacuum-row defect is
literally the absolute difference between the Boolean vacuum delta and the
canonical profile. -/
theorem centralHalfAmplitudeRegularizedRankOneDefect_cutoffOne_vacuum_word_eqv
    {w : Q'} (hw : (0 : Q') ≤ w)
    {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    centralHalfAmplitudeRegularizedRankOneDefect
        w hw 1 0 pseudocount pseudocount_pos zeroEdgeLabelling
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      Q'.abs
        (binaryVacuumWordWeight word +
          -centralRegularizedBoundaryProfile
            w hw 1 0 pseudocount pseudocount_pos
            (wordToEdgeLabelling (centralFixedFaceIds 0) word)) := by
  unfold centralHalfAmplitudeRegularizedRankOneDefect
  apply Q'.abs_eqv_congr
  exact Q'.add_eqv_congr'
    (centralHalfAmplitude_cutoffOne_vacuum_word_eqv_delta w word hword)
    (Q'.neg_eqv_congr _ _
      (Q'.eqv_trans _
        (1 * centralRegularizedBoundaryProfile
          w hw 1 0 pseudocount pseudocount_pos
          (wordToEdgeLabelling (centralFixedFaceIds 0) word)) _
        (Q'.mul_eqv_congr_right _ 1 _
          (centralHalfAmplitudeBoundaryRowMass_cutoffOne_vacuum_eqv_one w))
        (Q'.one_mul_eqv _)))

/-! ## 2. Exact sufficient-statistic reduction -/

/-- Every cross-row residual against the cutoff-one vacuum row can be
evaluated without retaining that full row: only its Boolean delta and exact
mass one remain. -/
theorem centralBoundaryPairwiseRowCrossTerm_cutoffOne_vacuum_word_eqv
    (w : Q') (other : EdgeLabelling) (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    centralBoundaryPairwiseRowCrossTerm
        w 1 0 zeroEdgeLabelling other
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      centralHalfAmplitudeBoundaryRowMass w 1 0 other *
          binaryVacuumWordWeight word +
        -centralHalfAmplitude w 1 0 other
          (wordToEdgeLabelling (centralFixedFaceIds 0) word) := by
  unfold centralBoundaryPairwiseRowCrossTerm finitePairwiseRowCrossTerm
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _
      (centralHalfAmplitude_cutoffOne_vacuum_word_eqv_delta w word hword))
    (Q'.neg_eqv_congr _ _
      (Q'.eqv_trans _
        (1 * centralHalfAmplitude w 1 0 other
          (wordToEdgeLabelling (centralFixedFaceIds 0) word)) _
        (Q'.mul_eqv_congr_right _ 1 _
          (centralHalfAmplitudeBoundaryRowMass_cutoffOne_vacuum_eqv_one w))
        (Q'.one_mul_eqv _)))

/-- The exact pseudocount term has the same delta reduction. -/
theorem finitePseudocountBiasTerm_cutoffOne_vacuum_word_eqv
    (w pseudocount : Q') (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    finitePseudocountBiasTerm
        (centralBoundaryChannels 1 0)
        (centralHalfAmplitude w 1 0)
        pseudocount zeroEdgeLabelling
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      pseudocount *
        (Q'.ofNat (centralBoundaryChannels 1 0).length *
            binaryVacuumWordWeight word +
          -1) := by
  unfold finitePseudocountBiasTerm
  apply Q'.mul_eqv_congr_left
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _
      (centralHalfAmplitude_cutoffOne_vacuum_word_eqv_delta w word hword))
    (Q'.neg_eqv_congr _ _
      (centralHalfAmplitudeBoundaryRowMass_cutoffOne_vacuum_eqv_one w))

/-- Reduced exact numerator for the cutoff-one vacuum-source statistical
budget.  It retains the other physical rows but replaces the entire vacuum
row by its checked mass and Boolean delta. -/
def cutoffOneVacuumReducedExactStatisticalNumerator
    (w : Q') (hw : (0 : Q') ≤ w)
    (pseudocount : Q') (word : List Nat) : Q' :=
  listQSum
      (fun other =>
        Q'.abs
          (centralHalfAmplitudeBoundaryRowMass w 1 0 other *
              binaryVacuumWordWeight word +
            -centralHalfAmplitude w 1 0 other
              (wordToEdgeLabelling (centralFixedFaceIds 0) word)))
      (centralPositiveHalfStates w hw 1 0) +
    Q'.abs
      (pseudocount *
        (Q'.ofNat (centralBoundaryChannels 1 0).length *
            binaryVacuumWordWeight word +
          -1))

/-- Exact statistical budget after eliminating the physical vacuum row. -/
def cutoffOneVacuumReducedExactStatisticalBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (pseudocount : Q') (pseudocount_pos : (0 : Q') < pseudocount)
    (word : List Nat) : Q' :=
  Q'.divPos
    (cutoffOneVacuumReducedExactStatisticalNumerator
      w hw pseudocount word)
    (centralRegularizedBoundaryDenominator w hw 1 0 pseudocount)
    (centralRegularizedBoundaryDenominator_pos
      hw 1 0 pseudocount_pos)

theorem centralBoundaryExactStatisticalRankOneBudget_cutoffOne_vacuum_word_eqv
    {w : Q'} (hw : (0 : Q') ≤ w)
    {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    centralBoundaryExactStatisticalRankOneBudget
        w hw 1 0 pseudocount pseudocount_pos zeroEdgeLabelling
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      cutoffOneVacuumReducedExactStatisticalBudget
        w hw pseudocount pseudocount_pos word := by
  unfold centralBoundaryExactStatisticalRankOneBudget
    cutoffOneVacuumReducedExactStatisticalBudget Q'.divPos
  apply Q'.mul_eqv_congr_right
  unfold cutoffOneVacuumReducedExactStatisticalNumerator
    finitePairwiseRowResidualBudget finitePseudocountBiasBudget
  exact Q'.add_eqv_congr'
    (listQSum_congr_on _ _
      (centralPositiveHalfStates w hw 1 0)
      (fun other _hother =>
        Q'.abs_eqv_congr
          (centralBoundaryPairwiseRowCrossTerm_cutoffOne_vacuum_word_eqv
            w other word hword)))
    (Q'.abs_eqv_congr
      (finitePseudocountBiasTerm_cutoffOne_vacuum_word_eqv
        w pseudocount word hword))

/-- The generic deterministic defect theorem now lands in the reduced
vacuum-row budget. -/
theorem centralHalfAmplitudeRegularizedRankOneDefect_cutoffOne_vacuum_word_le_reduced
    {w : Q'} (hw : (0 : Q') ≤ w)
    {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    centralHalfAmplitudeRegularizedRankOneDefect
        w hw 1 0 pseudocount pseudocount_pos zeroEdgeLabelling
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≤
      cutoffOneVacuumReducedExactStatisticalBudget
        w hw pseudocount pseudocount_pos word := by
  exact Q'.le_trans' _ _ _
    (centralHalfAmplitudeRegularizedRankOneDefect_le_exactStatisticalBudget
      hw 1 0 pseudocount_pos zeroEdgeLabelling
      (wordToEdgeLabelling (centralFixedFaceIds 0) word))
    (Q'.le_of_eqv
      (centralBoundaryExactStatisticalRankOneBudget_cutoffOne_vacuum_word_eqv
        hw pseudocount_pos word hword))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumStatistics

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumStatistics.finiteRowMass_cutoffOne_vacuum_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumStatistics.centralHalfAmplitude_cutoffOne_vacuum_regularizedRankOneAction_eqv_profile
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumStatistics.centralHalfAmplitudeRegularizedRankOneDefect_cutoffOne_vacuum_word_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumStatistics.centralBoundaryPairwiseRowCrossTerm_cutoffOne_vacuum_word_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumStatistics.centralBoundaryExactStatisticalRankOneBudget_cutoffOne_vacuum_word_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumStatistics.centralHalfAmplitudeRegularizedRankOneDefect_cutoffOne_vacuum_word_le_reduced
