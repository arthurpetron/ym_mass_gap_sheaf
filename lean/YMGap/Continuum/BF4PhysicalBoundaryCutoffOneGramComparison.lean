/-
# Exact refresh-comparison certificate for the cutoff-one physical block

The genuine row-normalized BF4 Gram rows at the vacuum and central lower
cube form an invariant two-state block.  This file packages their exact
identification with the vacuum-column refresh kernel in the generic finite
`L1` comparison interface.  The checked row defect is exactly zero, hence
the comparison contraction margin is exactly one.

This is a finite `K = 1`, half-extent-zero certificate.  It validates the
comparison plumbing needed by later cutoff-indexed certificates; it is not
a cutoff-uniform or continuum spectral-gap theorem.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov
import YMGap.Continuum.FiniteRefreshSpectralComparison

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneGramComparison

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRefreshSpectralComparison
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact normalization on the invariant two-atom sector -/

/-- The two retained physical atoms carry the entire normalized vacuum
column: their exact posterior masses add to one. -/
theorem cutoffOneVacuumColumnPosterior_two_atom_sum
    {w : Q'} (hw : (0 : Q') < w) :
    listQSum
        (cutoffOneVacuumColumnPosterior w hw)
        cutoffOneVacuumCubePhysicalSources ≈
      1 := by
  let denominator := cutoffOneVacuumColumnDenominator w
  let activity := (coeffW w 1) ^ 6
  let vacuumMass := cutoffOneVacuumColumnPosterior w hw zeroEdgeLabelling
  let cubeMass :=
    cutoffOneVacuumColumnPosterior w hw centralLowerCubeState
  refine Q'.eqv_trans _ (vacuumMass + cubeMass) _ ?_ ?_
  · unfold cutoffOneVacuumCubePhysicalSources listQSum
    exact Q'.add_eqv_congr_left vacuumMass _ cubeMass
      (QPoly.q_add_zero_eqv cubeMass)
  refine Q'.eqv_trans _
    (Q'.divPos 1 denominator
        (cutoffOneVacuumColumnDenominator_pos hw) +
      Q'.divPos activity denominator
        (cutoffOneVacuumColumnDenominator_pos hw)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (cutoffOneVacuumColumnPosterior_vacuum_eqv hw)
      (cutoffOneVacuumColumnPosterior_cube_eqv hw)
  apply Q'.mul_left_cancel_of_pos
    (cutoffOneVacuumColumnDenominator_pos hw)
  refine Q'.eqv_trans _
    ((Q'.divPos 1 denominator
        (cutoffOneVacuumColumnDenominator_pos hw) +
      Q'.divPos activity denominator
        (cutoffOneVacuumColumnDenominator_pos hw)) * denominator) _
    (Q'.mul_comm_eqv denominator _) ?_
  refine Q'.eqv_trans _
    (Q'.divPos 1 denominator
          (cutoffOneVacuumColumnDenominator_pos hw) * denominator +
      Q'.divPos activity denominator
          (cutoffOneVacuumColumnDenominator_pos hw) * denominator) _
    (Q'.add_mul_eqv _ _ denominator) ?_
  refine Q'.eqv_trans _ (1 + activity) _
    (Q'.add_eqv_congr'
      (Q'.divPos_mul_eqv 1 denominator
        (cutoffOneVacuumColumnDenominator_pos hw))
      (Q'.divPos_mul_eqv activity denominator
        (cutoffOneVacuumColumnDenominator_pos hw))) ?_
  refine Q'.eqv_trans _ denominator _ ?_ ?_
  · exact Q'.eqv_refl _
  exact Q'.eqv_symm (Q'.mul_one_eqv denominator)

/-- Restricting the refresh kernel to the invariant vacuum/cube sector
still gives a normalized row. -/
theorem cutoffOneVacuumCubeRefreshKernel_row_normalized
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling) :
    listQSum
        (cutoffOneVacuumColumnRefreshKernel w hw source)
        cutoffOneVacuumCubePhysicalSources ≈
      1 := by
  unfold cutoffOneVacuumColumnRefreshKernel
  exact cutoffOneVacuumColumnPosterior_two_atom_sum hw

/-- The genuine selected physical rows are normalized after restriction to
the invariant vacuum/cube sector. -/
theorem cutoffOneVacuumCubePhysicalGramMarkov_restricted_row_normalized
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources) :
    listQSum
        (cutoffOneVacuumCubePhysicalGramMarkov w hw source)
        cutoffOneVacuumCubePhysicalSources ≈
      1 := by
  refine Q'.eqv_trans _
    (listQSum
      (cutoffOneVacuumColumnRefreshKernel w hw source)
      cutoffOneVacuumCubePhysicalSources) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
      hw source hsource target
      (cutoffOneVacuumCubePhysicalSources_subset_carrier
        hw target htarget)
  exact cutoffOneVacuumCubeRefreshKernel_row_normalized hw source

/-! ## 2. The exact zero-defect comparison packet -/

/-- The first genuine positive-cutoff physical block inhabits the generic
refresh-comparison interface with exact row defect `epsilon = 0`. -/
def cutoffOneVacuumCubePhysicalGramComparisonCertificate
    (w : Q') (hw : (0 : Q') < w) :
    FiniteRefreshComparisonCertificate
      cutoffOneVacuumCubePhysicalSources
      (cutoffOneVacuumCubePhysicalGramMarkov w hw)
      (cutoffOneVacuumColumnRefreshKernel w hw) where
  epsilon := 0
  epsilon_nonnegative := by decide
  epsilon_lt_one := by decide
  kernel_nonnegative := by
    intro source hsource target htarget
    have href :=
      cutoffOneVacuumColumnRefreshKernel_nonnegative
        hw source target
    have heq :=
      cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
        hw source hsource target
        (cutoffOneVacuumCubePhysicalSources_subset_carrier
          hw target htarget)
    exact Q'.le_trans' 0
      (cutoffOneVacuumColumnRefreshKernel w hw source target)
      (cutoffOneVacuumCubePhysicalGramMarkov w hw source target)
      href (Q'.ge_of_eqv heq)
  kernel_row_normalized := by
    intro source hsource
    exact
      cutoffOneVacuumCubePhysicalGramMarkov_restricted_row_normalized
        hw source hsource
  reference_nonnegative := by
    intro source _hsource target _htarget
    exact cutoffOneVacuumColumnRefreshKernel_nonnegative hw source target
  reference_row_normalized := by
    intro source _hsource
    exact cutoffOneVacuumCubeRefreshKernel_row_normalized hw source
  row_defect_le := by
    intro source hsource
    exact Q'.le_of_eqv
      (finiteRowL1Defect_eqv_zero_of_pointwise
        cutoffOneVacuumCubePhysicalSources
        (cutoffOneVacuumCubePhysicalGramMarkov w hw)
        (cutoffOneVacuumColumnRefreshKernel w hw)
        source
        (fun target htarget =>
          cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
            hw source hsource target
            (cutoffOneVacuumCubePhysicalSources_subset_carrier
              hw target htarget)))

theorem cutoffOneVacuumCubePhysicalGramComparison_margin_eqv_one
    {w : Q'} (hw : (0 : Q') < w) :
    FiniteRefreshComparisonCertificate.contractionMargin
        (cutoffOneVacuumCubePhysicalGramComparisonCertificate w hw) ≈
      1 := by
  unfold FiniteRefreshComparisonCertificate.contractionMargin
    cutoffOneVacuumCubePhysicalGramComparisonCertificate
  change ((1 : Q') - 0) ≈ 1
  decide

theorem cutoffOneVacuumCubePhysicalGramComparison_margin_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') <
      FiniteRefreshComparisonCertificate.contractionMargin
        (cutoffOneVacuumCubePhysicalGramComparisonCertificate w hw) := by
  exact FiniteRefreshComparisonCertificate.contractionMargin_pos _

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneGramComparison

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneGramComparison.cutoffOneVacuumColumnPosterior_two_atom_sum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneGramComparison.cutoffOneVacuumCubePhysicalGramMarkov_restricted_row_normalized
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneGramComparison.cutoffOneVacuumCubePhysicalGramComparison_margin_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneGramComparison.cutoffOneVacuumCubePhysicalGramComparison_margin_pos
