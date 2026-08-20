/-
# Cutoff-two column total to posterior denominator bridge

The two aggregate names are definitionally the same finite sum.  This module
then transports the certified cutoff-two value and positivity to the name used
by the physical posterior API.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosteriorDenominatorCore

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem cutoffTwoVacuumExpectedScalar_eqv_denominator :
    cutoffTwoVacuumExpectedScalar ≈
      cutoffTwoVacuumColumnDenominator := by
  exact Q'.eqv_refl _

private theorem centralPositiveBoundaryTotalHalfAmplitude_eqv_columnMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    centralPositiveBoundaryTotalHalfAmplitude
        w hw K half boundary ≈
      centralBoundaryColumnMass w hw K half boundary := by
  unfold centralPositiveBoundaryTotalHalfAmplitude
    finiteChannelTotalAmplitude centralBoundaryColumnMass
  exact Q'.eqv_refl _

theorem centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_eqv :
    centralPositiveBoundaryTotalHalfAmplitude
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 zeroEdgeLabelling ≈
      cutoffTwoVacuumColumnDenominator := by
  exact Q'.eqv_trans _
    (centralBoundaryColumnMass cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
      2 0 zeroEdgeLabelling) _
    (centralPositiveBoundaryTotalHalfAmplitude_eqv_columnMass
      cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
      2 0 zeroEdgeLabelling)
    (Q'.eqv_trans _ cutoffTwoVacuumExpectedScalar _
      centralBoundaryColumnMass_cutoffTwo_vacuum_eqv_expected
      cutoffTwoVacuumExpectedScalar_eqv_denominator)

theorem centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_pos :
    (0 : Q') <
      centralPositiveBoundaryTotalHalfAmplitude
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 zeroEdgeLabelling := by
  exact Q'.pos_of_lt_of_le
    cutoffTwoVacuumColumnDenominator_pos
    (Q'.ge_of_eqv
      centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_eqv)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior.centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_eqv
