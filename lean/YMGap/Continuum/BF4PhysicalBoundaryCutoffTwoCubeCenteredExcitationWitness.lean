/-
# Constructive boundary witness for the cutoff-two centered cube excitation

The strictly positive channel sum of squares is finite.  A total recursive
search therefore selects an actual retained boundary channel whose weighted
centered residual square is strictly positive.  In particular, its centered
channel amplitude is not rationally equivalent to zero.

This is a finite data-producing certificate.  It does not identify an
invariant transfer eigenstate or prove a cutoff-uniform or continuum gap.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitation

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitationWitness

set_option maxRecDepth 300000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The channel amplitude of `cube - (1/4096) vacuum`. -/
def cutoffTwoVacuumCenteredCubeChannelResidual
    (boundary : EdgeLabelling) : Q' :=
  channelLinear
    cutoffTwoVacuumCubeIndex
    (fun side fixedBoundary =>
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        (cutoffTwoVacuumCubeState side) fixedBoundary)
    cutoffTwoVacuumCenteredCubeCoefficient boundary

/-- One nonnegative summand of the centered channel SOS. -/
def cutoffTwoVacuumCenteredCubeChannelResidualTerm
    (boundary : EdgeLabelling) : Q' :=
  centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary *
    (cutoffTwoVacuumCenteredCubeChannelResidual boundary *
      cutoffTwoVacuumCenteredCubeChannelResidual boundary)

theorem cutoffTwoVacuumCenteredCubeChannelSOS_eqv_residualSum :
    cutoffTwoVacuumCenteredCubeChannelSOS ≈
      listQSum cutoffTwoVacuumCenteredCubeChannelResidualTerm
        (centralBoundaryChannels 2 0) := by
  unfold cutoffTwoVacuumCenteredCubeChannelSOS
    cutoffTwoVacuumCenteredCubeChannelResidualTerm
    cutoffTwoVacuumCenteredCubeChannelResidual
    weightedGramSOS
  exact Q'.eqv_refl _

/-- A total recursive finite search selects the first positive channel term,
falling back to the vacuum boundary only in the impossible empty case. -/
def cutoffTwoVacuumCenteredCubeBoundaryWitness : EdgeLabelling :=
  firstPositiveOr zeroEdgeLabelling
    cutoffTwoVacuumCenteredCubeChannelResidualTerm
    (centralBoundaryChannels 2 0)

theorem cutoffTwoVacuumCenteredCubeBoundaryWitness_term_pos :
    cutoffTwoVacuumCenteredCubeBoundaryWitness ∈
        centralBoundaryChannels 2 0 ∧
      (0 : Q') <
        cutoffTwoVacuumCenteredCubeChannelResidualTerm
          cutoffTwoVacuumCenteredCubeBoundaryWitness := by
  have hsum :
      (0 : Q') <
        listQSum cutoffTwoVacuumCenteredCubeChannelResidualTerm
          (centralBoundaryChannels 2 0) :=
    Q'.pos_of_lt_of_le
      cutoffTwoVacuumCenteredCubeChannelSOS_pos
      (Q'.le_of_eqv
        cutoffTwoVacuumCenteredCubeChannelSOS_eqv_residualSum)
  exact firstPositiveOr_mem_and_pos_of_sum_pos
    zeroEdgeLabelling
    cutoffTwoVacuumCenteredCubeChannelResidualTerm
    (centralBoundaryChannels 2 0) hsum

private theorem pos_not_eqv_zero {value : Q'}
    (hvalue : (0 : Q') < value) : ¬ value ≈ 0 := by
  intro hzero
  exact (Int.not_lt_of_ge (Q'.le_of_eqv hzero)) hvalue

theorem cutoffTwoVacuumCenteredCubeBoundaryWitness_residual_ne_zero :
    ¬ cutoffTwoVacuumCenteredCubeChannelResidual
        cutoffTwoVacuumCenteredCubeBoundaryWitness ≈ 0 := by
  let residual := cutoffTwoVacuumCenteredCubeChannelResidual
    cutoffTwoVacuumCenteredCubeBoundaryWitness
  let weight := centralBoundaryWeight cutoffTwoHalfCoupling 2 0
    cutoffTwoVacuumCenteredCubeBoundaryWitness
  intro hresidual
  have hsquare : residual * residual ≈ 0 := by
    refine Q'.eqv_trans _ (0 * residual) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ residual hresidual
    exact Q'.zero_mul_eqv residual
  have hterm :
      cutoffTwoVacuumCenteredCubeChannelResidualTerm
          cutoffTwoVacuumCenteredCubeBoundaryWitness ≈ 0 := by
    unfold cutoffTwoVacuumCenteredCubeChannelResidualTerm
    change weight * (residual * residual) ≈ 0
    exact Q'.eqv_trans _ (weight * 0) _
      (Q'.mul_eqv_congr_left weight _ _ hsquare)
      (Q'.mul_zero_eqv weight)
  exact pos_not_eqv_zero
    cutoffTwoVacuumCenteredCubeBoundaryWitness_term_pos.2 hterm

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitationWitness

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitationWitness.cutoffTwoVacuumCenteredCubeChannelSOS_eqv_residualSum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitationWitness.cutoffTwoVacuumCenteredCubeBoundaryWitness_term_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitationWitness.cutoffTwoVacuumCenteredCubeBoundaryWitness_residual_ne_zero
