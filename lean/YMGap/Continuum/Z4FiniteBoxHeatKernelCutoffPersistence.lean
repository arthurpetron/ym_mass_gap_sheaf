import YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder

/-!
# Cutoff persistence of the gauge-closed cube mode

The elementary-cube boundary constructed at cutoff two uses only labels zero
and two.  This file replaces every cutoff-two edge packet by the corresponding
heat-kernel, vacuum, or all-ones packet at an arbitrary cutoff `K ≥ 2`.
The old cube labelling remains bounded and physical, and its projected
amplitude is exactly unchanged.  Consequently every such cutoff contains a
positive-weight copy of the same derived closed-surface mode.

This is modewise persistence, not cutoff invariance of the complete
heat-kernel state: higher cutoffs contain additional nonzero character
coefficients and additional physical modes.  No character-tail, volume-limit,
or continuum claim is made here.
-/

namespace YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport

local infix:50 " ≈ " => Q'.eqv

/-- The same physical box packet family at an arbitrary character cutoff. -/
def gaugeHeatKernelBoxPacketsAtCutoff (K n : Nat) :
    Nat → CharacterPacket K :=
  fun edge => if edge < plaquetteEdgeCount n
    then heatKernelPacket K coupling
    else if edge ∈ vacuumBaseEdgeIds n
      then vacuumPacket K
      else allOnesPacket K

/-- The arbitrary-cutoff gauge-closed packet state on box `n`. -/
def gaugeHeatKernelBoxStateAtCutoff (K n : Nat) :
    CompensatedGraphState K where
  edges := usedResolutionEdges n
  vertices := resolutionVertices n
  packet := gaugeHeatKernelBoxPacketsAtCutoff K n
  copiedEdges := []
  copied_mem := by intro edge h; cases h

/-- The support-pruned separator is uniform in volume and character cutoff. -/
theorem gaugeHeatKernelBoxStateAtCutoff_gap (K n : Nat) :
    SpectralGapBound
      (supportedGraphSpectralModel
        (gaugeHeatKernelBoxStateAtCutoff K n))
      (eighth * eighth) :=
  path_supported_gap_from_uncompensated (.refl _) rfl

/-- A cutoff at least two still enumerates the old cube labelling. -/
theorem unitCubeSurfaceLabel_mem_bounded_at_cutoff
    {K : Nat} (hK : 2 ≤ K) :
    unitCubeSurfaceLabel 2 ∈ boundedEdgeLabellings K
      (usedResolutionEdges 2) := by
  have hold := boundedEdgeLabellings_sound 2
    (usedResolutionEdges 2) (unitCubeSurfaceLabel 2)
    unitCubeSurfaceLabel_mem_bounded
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    have hbound := hold.1 edge hedge
    omega
  · exact hold.2

theorem unitCubeSurfaceLabel_mem_physical_at_cutoff
    {K : Nat} (hK : 2 ≤ K) :
    unitCubeSurfaceLabel 2 ∈ physicalEdgeLabellings K
      (usedResolutionEdges 2) (resolutionVertices 2) := by
  exact List.mem_filter.mpr
    ⟨unitCubeSurfaceLabel_mem_bounded_at_cutoff hK,
      unitCubeSurfaceLabel_physical⟩

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on
    (f g : Nat → Q') : ∀ edges : List Nat,
    (∀ edge, edge ∈ edges → f edge ≈ g edge) →
      eliminateLinks f edges ≈ eliminateLinks g edges
  | [], _ => Q'.eqv_refl _
  | edge :: rest, h =>
      q_mul_congr
        (h edge List.mem_cons_self)
        (eliminateLinks_congr_on f g rest
          (fun e he => h e (List.mem_cons_of_mem edge he)))

/-- Every coefficient actually sampled by the cube labelling is unchanged
when the character cutoff is enlarged. -/
theorem unitCube_edgeCoefficient_cutoff_eq_two
    {K edge : Nat} (hK : 2 ≤ K)
    (hedge : edge ∈ usedResolutionEdges 2) :
    coeffAt (gaugeHeatKernelBoxPacketsAtCutoff K 2 edge)
        (unitCubeSurfaceLabel 2 edge) =
      coeffAt (gaugeHeatKernelBoxPackets 2 edge)
        (unitCubeSurfaceLabel 2 edge) := by
  have hold := boundedEdgeLabellings_sound 2
    (usedResolutionEdges 2) (unitCubeSurfaceLabel 2)
    unitCubeSurfaceLabel_mem_bounded
  have htwo := hold.1 edge hedge
  have hlarge : unitCubeSurfaceLabel 2 edge < K + 1 := by omega
  unfold gaugeHeatKernelBoxPacketsAtCutoff gaugeHeatKernelBoxPackets
  by_cases hp : edge < plaquetteEdgeCount 2
  · rw [if_pos hp, if_pos hp,
      coeffAt_heatKernelPacket hlarge, coeffAt_heatKernelPacket htwo]
  · rw [if_neg hp, if_neg hp]
    by_cases hv : edge ∈ vacuumBaseEdgeIds 2
    · rw [if_pos hv, if_pos hv,
        YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.coeffAt_vacuumPacket,
        YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.coeffAt_vacuumPacket]
    · rw [if_neg hv, if_neg hv,
        coeffAt_allOnesPacket hlarge, coeffAt_allOnesPacket htwo]

/-- Exact modewise cutoff persistence of the projected cube amplitude. -/
theorem unitCube_heatKernel_amplitude_cutoff_eq_two
    {K : Nat} (hK : 2 ≤ K) :
    packetGraphProjectedAmplitude (usedResolutionEdges 2)
        (resolutionVertices 2)
        (gaugeHeatKernelBoxPacketsAtCutoff K 2)
        (unitCubeSurfaceLabel 2) ≈
      packetGraphProjectedAmplitude (usedResolutionEdges 2)
        (resolutionVertices 2) (gaugeHeatKernelBoxPackets 2)
        (unitCubeSurfaceLabel 2) := by
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  rw [if_pos unitCubeSurfaceLabel_physical,
    if_pos unitCubeSurfaceLabel_physical]
  unfold packetGraphBareAmplitude
  exact eliminateLinks_congr_on _ _ (usedResolutionEdges 2)
    (fun edge hedge => by
      rw [unitCube_edgeCoefficient_cutoff_eq_two hK hedge]
      exact Q'.eqv_refl _)

/-- The derived six-face amplitude is independent of every cutoff `K ≥ 2`. -/
theorem unitCube_heatKernel_amplitude_exact_at_cutoff
    {K : Nat} (hK : 2 ≤ K) :
    packetGraphProjectedAmplitude (usedResolutionEdges 2)
        (resolutionVertices 2)
        (gaugeHeatKernelBoxPacketsAtCutoff K 2)
        (unitCubeSurfaceLabel 2) ≈
      unitCubeHeatKernelAmplitude :=
  Q'.eqv_trans _ _ _
    (unitCube_heatKernel_amplitude_cutoff_eq_two hK)
    unitCube_heatKernel_amplitude_exact

/-- Every cutoff at least two contains a positive-weight spectral mode with
the same exact gauge-closed heat-kernel amplitude. -/
theorem unitCube_heatKernel_nonzero_mode_at_cutoff
    {K : Nat} (hK : 2 ≤ K) :
    ∃ i, i < (physicalEdgeLabellings K (usedResolutionEdges 2)
        (resolutionVertices 2)).length ∧
      packetGraphModeWeight (usedResolutionEdges 2) (resolutionVertices 2)
        (gaugeHeatKernelBoxPacketsAtCutoff K 2) i ≈
          unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude := by
  obtain ⟨i, hi, hget⟩ :=
    List.getElem_of_mem (unitCubeSurfaceLabel_mem_physical_at_cutoff hK)
  refine ⟨i, hi, ?_⟩
  have hlabel : physicalModeLabel K (usedResolutionEdges 2)
      (resolutionVertices 2) i = unitCubeSurfaceLabel 2 := by
    unfold physicalModeLabel supportLabel
    rw [List.getElem?_eq_getElem hi, Option.getD_some, hget]
  unfold packetGraphModeWeight
  rw [hlabel]
  exact Q'.eqv_trans _
    (unitCubeHeatKernelAmplitude *
      packetGraphProjectedAmplitude (usedResolutionEdges 2)
        (resolutionVertices 2)
        (gaugeHeatKernelBoxPacketsAtCutoff K 2)
        (unitCubeSurfaceLabel 2)) _
    (Q'.mul_eqv_congr_right _ _ _
      (unitCube_heatKernel_amplitude_exact_at_cutoff hK))
    (Q'.mul_eqv_congr_left _ _ _
      (unitCube_heatKernel_amplitude_exact_at_cutoff hK))

#print axioms gaugeHeatKernelBoxStateAtCutoff_gap
#print axioms unitCubeSurfaceLabel_mem_bounded_at_cutoff
#print axioms unitCubeSurfaceLabel_mem_physical_at_cutoff
#print axioms unitCube_edgeCoefficient_cutoff_eq_two
#print axioms unitCube_heatKernel_amplitude_cutoff_eq_two
#print axioms unitCube_heatKernel_amplitude_exact_at_cutoff
#print axioms unitCube_heatKernel_nonzero_mode_at_cutoff

end YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence
