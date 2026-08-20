/-
# Exact normalized cutoff-two vacuum-column excitation statistic

The kernel-checked cutoff-two vacuum-column contraction canonically normalizes
the retained lower-source amplitudes to a finite probability law.  This file
identifies that law with the genuine BF4 target-given-vacuum posterior, proves
that the aggregate non-vacuum event has the exact rational mass

  (68719477465 / 281474976710656) /
    (281543696188121 / 281474976710656),

and derives a strictly positive Bernoulli variance for its indicator.  The
explicit source selected in the excitation module also has positive posterior
mass.

These are finite `K = 2`, half-extent-zero statements at coupling `1/2`.
They are not cutoff-uniform, volume-uniform, spectral-gap, or continuum claims.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosteriorDenominator
import YMGap.Continuum.CubeRatioBounds
import YMGap.Continuum.LocatedSpectralGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumExcitation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Normalization of the explicit source law -/

/-- Normalization is inherited from the generic finite posterior theorem;
the pointwise bridge above is the only cutoff-two specialization. -/
theorem cutoffTwoVacuumColumnPosterior_total_one :
    listQSum
        cutoffTwoVacuumColumnPosterior
        (centralPositiveHalfStates cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0) ≈
      1 := by
  refine Q'.eqv_trans _
    (listQSum
      (centralTargetGivenBoundary
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 zeroEdgeLabelling
        centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_pos)
      (centralPositiveHalfStates cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact Q'.eqv_symm
      (centralTargetGivenVacuum_cutoffTwo_eqv_explicit source)
  · exact centralTargetGivenBoundary_total_one
      centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_pos

/-! ## 2. Exact excited-event mass and positive variance -/

/-- Exact posterior probability of the retained non-vacuum event. -/
def cutoffTwoVacuumExcitationProbability : Q' :=
  Q'.divPos cutoffTwoVacuumExcitedExcess
    cutoffTwoVacuumColumnDenominator
    cutoffTwoVacuumColumnDenominator_pos

theorem cutoffTwoVacuumColumnPosterior_nonvacuum_sum_eqv :
    listQSum cutoffTwoVacuumColumnPosterior
        cutoffTwoNonvacuumPositiveSources ≈
      cutoffTwoVacuumExcitationProbability := by
  unfold cutoffTwoVacuumColumnPosterior
    cutoffTwoVacuumExcitationProbability Q'.divPos
  refine Q'.eqv_trans _
    (listQSum
        (fun source =>
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
            zeroEdgeLabelling)
        cutoffTwoNonvacuumPositiveSources *
      Q'.recipPos cutoffTwoVacuumColumnDenominator
        cutoffTwoVacuumColumnDenominator_pos) _ ?_ ?_
  · exact listQSum_mul_right
      (fun source =>
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
          zeroEdgeLabelling)
      (Q'.recipPos cutoffTwoVacuumColumnDenominator
        cutoffTwoVacuumColumnDenominator_pos)
      cutoffTwoNonvacuumPositiveSources
  · exact Q'.mul_eqv_congr_right _ _ _
      cutoffTwoNonvacuumPositiveSources_sum_eqv_excitedExcess

theorem cutoffTwoVacuumExcitationProbability_pos :
    (0 : Q') < cutoffTwoVacuumExcitationProbability := by
  unfold cutoffTwoVacuumExcitationProbability
  exact Q'.divPos_pos _ _ cutoffTwoVacuumColumnDenominator_pos
    (by decide : (0 : Q') < cutoffTwoVacuumExcitedExcess)

theorem cutoffTwoVacuumExcitedExcess_lt_denominator :
    cutoffTwoVacuumExcitedExcess < cutoffTwoVacuumColumnDenominator := by
  unfold cutoffTwoVacuumExcitedExcess cutoffTwoVacuumColumnDenominator
    cutoffTwoVacuumExpectedScalar
  decide

theorem cutoffTwoVacuumExcitationProbability_lt_one :
    cutoffTwoVacuumExcitationProbability < (1 : Q') := by
  unfold cutoffTwoVacuumExcitationProbability
  exact divPos_lt_one_of_lt _ _
    cutoffTwoVacuumColumnDenominator_pos
    cutoffTwoVacuumExcitedExcess_lt_denominator

/-- Bernoulli variance of the event that the retained lower source is not
the faithful all-vacuum source. -/
def cutoffTwoVacuumExcitationVariance : Q' :=
  cutoffTwoVacuumExcitationProbability *
    ((1 : Q') - cutoffTwoVacuumExcitationProbability)

theorem cutoffTwoVacuumExcitationVariance_pos :
    (0 : Q') < cutoffTwoVacuumExcitationVariance := by
  unfold cutoffTwoVacuumExcitationVariance
  exact Q'.mul_pos cutoffTwoVacuumExcitationProbability_pos
    (one_sub_pos_of_lt_one cutoffTwoVacuumExcitationProbability_lt_one)

/-- The deterministic excited source has positive mass in the normalized
physical vacuum-column posterior. -/
theorem cutoffTwoExcitedVacuumSource_posterior_pos :
    (0 : Q') <
      cutoffTwoVacuumColumnPosterior cutoffTwoExcitedVacuumSource := by
  unfold cutoffTwoVacuumColumnPosterior
  exact Q'.divPos_pos _ _ cutoffTwoVacuumColumnDenominator_pos
    cutoffTwoExcitedVacuumSource_spec.2.2

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior.cutoffTwoVacuumColumnPosterior_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior.centralTargetGivenVacuum_cutoffTwo_eqv_explicit
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior.cutoffTwoVacuumColumnPosterior_nonvacuum_sum_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior.cutoffTwoVacuumExcitationVariance_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior.cutoffTwoExcitedVacuumSource_posterior_pos
