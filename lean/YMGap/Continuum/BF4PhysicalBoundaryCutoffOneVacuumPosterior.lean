/-
# Exact normalized cutoff-one vacuum-column posterior

The exact vacuum-column contraction gives a canonical two-atom probability
law on retained lower-half sources.  This file normalizes the genuine BF4
half amplitudes by the checked denominator

  1 + (coeffW w 1)^6,

identifies the result with the project's existing target-given-boundary
posterior, and proves that both the vacuum and central-cube atoms have
strictly positive mass.  Consequently the cube indicator has a strictly
positive finite Bernoulli variance.

This is a finite `K = 1`, half-extent-zero theorem.  The positive variance is
not a cutoff-uniform spectral gap and is not a continuum mass gap.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction
import YMGap.Continuum.BF4PhysicalBoundaryPosterior
import YMGap.Continuum.CubeRatioBounds
import YMGap.Continuum.LocatedSpectralGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit positive denominator -/

def cutoffOneVacuumColumnDenominator (w : Q') : Q' :=
  1 + (coeffW w 1) ^ 6

theorem cutoffOneVacuumColumnActivity_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < (coeffW w 1) ^ 6 :=
  YMGap.Continuum.HKPos.pow_pos (coeffW_pos hw 1) 6

theorem cutoffOneVacuumColumnDenominator_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < cutoffOneVacuumColumnDenominator w := by
  unfold cutoffOneVacuumColumnDenominator
  exact Q'.pos_add_nonneg (by decide)
    (Q'.le_of_lt (cutoffOneVacuumColumnActivity_pos hw))

/-- The canonical boundary-total name used by the posterior layer has the
same exact two-term value. -/
theorem centralPositiveBoundaryTotalHalfAmplitude_cutoffOne_vacuum_eqv
    {w : Q'} (hw : (0 : Q') < w) :
    centralPositiveBoundaryTotalHalfAmplitude
        w (Q'.le_of_lt hw) 1 0 zeroEdgeLabelling ≈
      cutoffOneVacuumColumnDenominator w := by
  simpa [centralPositiveBoundaryTotalHalfAmplitude,
    finiteChannelTotalAmplitude, centralBoundaryColumnMass,
    cutoffOneVacuumColumnDenominator] using
      (centralBoundaryColumnMass_cutoffOne_vacuum_eqv hw)

theorem centralPositiveBoundaryTotalHalfAmplitude_cutoffOne_vacuum_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') <
      centralPositiveBoundaryTotalHalfAmplitude
        w (Q'.le_of_lt hw) 1 0 zeroEdgeLabelling := by
  exact Q'.pos_of_lt_of_le
    (cutoffOneVacuumColumnDenominator_pos hw)
    (Q'.ge_of_eqv
      (centralPositiveBoundaryTotalHalfAmplitude_cutoffOne_vacuum_eqv hw))

/-! ## 2. Explicit normalized law and canonical-posterior bridge -/

def cutoffOneVacuumColumnPosterior
    (w : Q') (hw : (0 : Q') < w)
    (source : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralHalfAmplitude w 1 0 source zeroEdgeLabelling)
    (cutoffOneVacuumColumnDenominator w)
    (cutoffOneVacuumColumnDenominator_pos hw)

theorem cutoffOneVacuumColumnPosterior_total_one
    {w : Q'} (hw : (0 : Q') < w) :
    listQSum
        (cutoffOneVacuumColumnPosterior w hw)
        (centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0) ≈
      1 := by
  unfold cutoffOneVacuumColumnPosterior Q'.divPos
  refine Q'.eqv_trans _
    (centralBoundaryColumnMass w (Q'.le_of_lt hw) 1 0
        zeroEdgeLabelling *
      Q'.recipPos
        (cutoffOneVacuumColumnDenominator w)
        (cutoffOneVacuumColumnDenominator_pos hw)) _ ?_ ?_
  · exact listQSum_mul_right
      (fun source =>
        centralHalfAmplitude w 1 0 source zeroEdgeLabelling)
      (Q'.recipPos
        (cutoffOneVacuumColumnDenominator w)
        (cutoffOneVacuumColumnDenominator_pos hw))
      (centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0)
  · exact Q'.eqv_trans _
      (cutoffOneVacuumColumnDenominator w *
        Q'.recipPos
          (cutoffOneVacuumColumnDenominator w)
          (cutoffOneVacuumColumnDenominator_pos hw)) _
      (Q'.mul_eqv_congr_right _ _ _
        (centralBoundaryColumnMass_cutoffOne_vacuum_eqv hw))
      (Q'.mul_recipPos_eqv _ _)

private theorem qeqv_of_le_of_ge_local {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (ha : a ≈ a') (hden : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hden))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) ha))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hden)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm ha)))

/-- The explicit two-term normalization is exactly the existing genuine BF4
target-given-vacuum posterior. -/
theorem centralTargetGivenVacuum_cutoffOne_eqv_explicit
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling) :
    centralTargetGivenBoundary
        w (Q'.le_of_lt hw) 1 0 zeroEdgeLabelling
        (centralPositiveBoundaryTotalHalfAmplitude_cutoffOne_vacuum_pos hw)
        source ≈
      cutoffOneVacuumColumnPosterior w hw source := by
  unfold centralTargetGivenBoundary finiteStateGivenChannel
    cutoffOneVacuumColumnPosterior
  exact divPos_eqv_congr_local
    (centralPositiveBoundaryTotalHalfAmplitude_cutoffOne_vacuum_pos hw)
    (cutoffOneVacuumColumnDenominator_pos hw)
    (Q'.eqv_refl _)
    (centralPositiveBoundaryTotalHalfAmplitude_cutoffOne_vacuum_eqv hw)

/-! ## 3. Exact atoms and a positive finite fluctuation -/

theorem cutoffOneVacuumColumnPosterior_vacuum_eqv
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneVacuumColumnPosterior w hw zeroEdgeLabelling ≈
      Q'.divPos 1
        (cutoffOneVacuumColumnDenominator w)
        (cutoffOneVacuumColumnDenominator_pos hw) := by
  unfold cutoffOneVacuumColumnPosterior Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (centralHalfAmplitude_cutoffOne_vacuum_vacuum_eqv_one w)

theorem cutoffOneVacuumColumnPosterior_cube_eqv
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneVacuumColumnPosterior w hw centralLowerCubeState ≈
      Q'.divPos ((coeffW w 1) ^ 6)
        (cutoffOneVacuumColumnDenominator w)
        (cutoffOneVacuumColumnDenominator_pos hw) := by
  unfold cutoffOneVacuumColumnPosterior Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (centralHalfAmplitude_cutoffOne_cube_vacuum_eqv w)

theorem cutoffOneVacuumColumnPosterior_cube_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') <
      cutoffOneVacuumColumnPosterior w hw centralLowerCubeState := by
  unfold cutoffOneVacuumColumnPosterior
  exact Q'.divPos_pos _ _ _
    (centralHalfAmplitude_cutoffOne_cube_vacuum_pos hw)

theorem cutoffOneVacuumColumnActivity_lt_denominator
    {w : Q'} (_hw : (0 : Q') < w) :
    (coeffW w 1) ^ 6 < cutoffOneVacuumColumnDenominator w := by
  unfold cutoffOneVacuumColumnDenominator
  have hraw := lt_add_of_pos_right ((coeffW w 1) ^ 6) 1
    (by decide : (0 : Q') < 1)
  exact q_lt_of_lt_of_le hraw
    (Q'.le_of_eqv (Q'.add_comm_eqv ((coeffW w 1) ^ 6) 1))

theorem cutoffOneVacuumColumnPosterior_cube_lt_one
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneVacuumColumnPosterior w hw centralLowerCubeState <
      (1 : Q') := by
  have hexplicit :
      Q'.divPos ((coeffW w 1) ^ 6)
          (cutoffOneVacuumColumnDenominator w)
          (cutoffOneVacuumColumnDenominator_pos hw) <
        (1 : Q') :=
    divPos_lt_one_of_lt _ _
      (cutoffOneVacuumColumnDenominator_pos hw)
      (cutoffOneVacuumColumnActivity_lt_denominator hw)
  exact Q'.lt_of_le_of_lt
    (Q'.le_of_eqv (cutoffOneVacuumColumnPosterior_cube_eqv hw))
    hexplicit

/-- Exact Bernoulli variance of the central-cube indicator in the normalized
vacuum column. -/
def cutoffOneVacuumColumnCubeVariance
    (w : Q') (hw : (0 : Q') < w) : Q' :=
  let p := cutoffOneVacuumColumnPosterior w hw centralLowerCubeState
  p * ((1 : Q') - p)

/-- Both atoms are present, so the finite cube-indicator fluctuation is
strictly positive.  This is intentionally only a finite statistic. -/
theorem cutoffOneVacuumColumnCubeVariance_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < cutoffOneVacuumColumnCubeVariance w hw := by
  unfold cutoffOneVacuumColumnCubeVariance
  exact Q'.mul_pos
    (cutoffOneVacuumColumnPosterior_cube_pos hw)
    (one_sub_pos_of_lt_one
      (cutoffOneVacuumColumnPosterior_cube_lt_one hw))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior.centralPositiveBoundaryTotalHalfAmplitude_cutoffOne_vacuum_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior.cutoffOneVacuumColumnPosterior_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior.centralTargetGivenVacuum_cutoffOne_eqv_explicit
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior.cutoffOneVacuumColumnPosterior_cube_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior.cutoffOneVacuumColumnCubeVariance_pos
