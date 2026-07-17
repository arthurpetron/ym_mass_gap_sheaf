import YMGap.Continuum.Z4FiniteBoxPacketState

namespace ScratchZ4HeatKernelBoxState

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport
open YMGap.Continuum.SU2PeterWeylWilsonBlock

local infix:50 " ≈ " => Q'.eqv

def usedAuxiliaryEdges (n : Nat) : List Nat :=
  (((resolutionVertices n).flatMap vertexEdgeIds).filter
    fun edge => decide (plaquetteEdgeCount n ≤ edge)).eraseDups

def usedResolutionEdges (n : Nat) : List Nat :=
  List.range (plaquetteEdgeCount n) ++ usedAuxiliaryEdges n

def heatKernelPacket (K : Nat) (w : Q') : CharacterPacket K where
  coeff spin := coeffW w spin

theorem coeffAt_heatKernelPacket {K spin : Nat} {w : Q'}
    (hspin : spin < K + 1) :
    coeffAt (heatKernelPacket K w) spin = coeffW w spin := by
  rw [coeffAt_of_lt _ hspin]
  rfl

def heatKernelBoxPackets (n : Nat) : Nat → CharacterPacket 2 :=
  fun edge => if edge < plaquetteEdgeCount n
    then heatKernelPacket 2 coupling
    else allOnesPacket 2

def heatKernelBoxState (n : Nat) : CompensatedGraphState 2 where
  edges := usedResolutionEdges n
  vertices := resolutionVertices n
  packet := heatKernelBoxPackets n
  copiedEdges := []
  copied_mem := by intro edge h; cases h

theorem heatKernelBoxState_gap (n : Nat) :
    SpectralGapBound (supportedGraphSpectralModel (heatKernelBoxState n))
      (eighth * eighth) :=
  path_supported_gap_from_uncompensated (.refl _) rfl

def heatKernelSpinOneLabel (n : Nat) : EdgeLabelling :=
  fun edge => if edge ∈ usedResolutionEdges n then 2 else 0

theorem heatKernelSpinOneLabel_mem_bounded (n : Nat) :
    heatKernelSpinOneLabel n ∈ boundedEdgeLabellings 2
      (usedResolutionEdges n) := by
  apply boundedEdgeLabellings_complete
  · intro edge he
    simp [heatKernelSpinOneLabel, he]
  · intro edge he
    simp [heatKernelSpinOneLabel, he]

theorem usedResolutionEdges_unbounded (bound : Nat) :
    ∃ n : Nat, bound ≤ (usedResolutionEdges n).length := by
  obtain ⟨n, hn⟩ :=
    YMGap.Continuum.Z4FiniteBoxExhaustion.boxPlaquetteCount_unbounded bound
  refine ⟨n, ?_⟩
  unfold usedResolutionEdges
  rw [List.length_append, List.length_range]
  unfold plaquetteEdgeCount
  omega

#eval usedResolutionEdges 1

theorem firstBox_heatKernelSpinOne_physical :
    GraphPhysical (usedResolutionEdges 1) (resolutionVertices 1)
      (heatKernelSpinOneLabel 1) := by decide

theorem firstBox_heatKernelSpinOne_mem_physical :
    heatKernelSpinOneLabel 1 ∈ physicalEdgeLabellings 2
      (usedResolutionEdges 1) (resolutionVertices 1) := by
  exact List.mem_filter.mpr
    ⟨heatKernelSpinOneLabel_mem_bounded 1,
      firstBox_heatKernelSpinOne_physical⟩

def firstBoxHeatKernelAmplitude : Q' :=
  Q'.mkPos 729 281474976710656 (by decide)

theorem firstBox_heatKernel_amplitude_exact :
    packetGraphProjectedAmplitude (usedResolutionEdges 1)
      (resolutionVertices 1) (heatKernelBoxPackets 1)
      (heatKernelSpinOneLabel 1) ≈ firstBoxHeatKernelAmplitude := by decide

theorem firstBoxHeatKernelAmplitude_pos :
    (0 : Q') < firstBoxHeatKernelAmplitude := by decide

theorem firstBox_heatKernel_nonzero_mode :
    ∃ i, i < (physicalEdgeLabellings 2 (usedResolutionEdges 1)
        (resolutionVertices 1)).length ∧
      packetGraphModeWeight (usedResolutionEdges 1) (resolutionVertices 1)
        (heatKernelBoxPackets 1) i ≈
          firstBoxHeatKernelAmplitude * firstBoxHeatKernelAmplitude := by
  obtain ⟨i, hi, hget⟩ :=
    List.getElem_of_mem firstBox_heatKernelSpinOne_mem_physical
  refine ⟨i, hi, ?_⟩
  have hlabel : physicalModeLabel 2 (usedResolutionEdges 1)
      (resolutionVertices 1) i = heatKernelSpinOneLabel 1 := by
    unfold physicalModeLabel supportLabel
    rw [List.getElem?_eq_getElem hi, Option.getD_some, hget]
  unfold packetGraphModeWeight
  rw [hlabel]
  exact Q'.eqv_trans _
    (firstBoxHeatKernelAmplitude *
      packetGraphProjectedAmplitude (usedResolutionEdges 1)
        (resolutionVertices 1) (heatKernelBoxPackets 1)
        (heatKernelSpinOneLabel 1)) _
    (Q'.mul_eqv_congr_right _ _ _ firstBox_heatKernel_amplitude_exact)
    (Q'.mul_eqv_congr_left _ _ _ firstBox_heatKernel_amplitude_exact)

def unitCubeSurface : List YMGap.Continuum.ClusterCount4DProgress.Z4Plaq :=
  [((0, 0, 0, 0), .p01), ((0, 0, 1, 0), .p01),
   ((0, 0, 0, 0), .p02), ((0, 1, 0, 0), .p02),
   ((0, 0, 0, 0), .p12), ((1, 0, 0, 0), .p12)]

def unitCubeSurfaceIds (n : Nat) : List Nat :=
  ((enumerate (YMGap.Continuum.Z4FiniteBoxExhaustion.boxPlaquettes n)).filter
    fun indexed => decide (indexed.2 ∈ unitCubeSurface)).map Prod.fst

def vacuumBaseEdgeIds (n : Nat) : List Nat :=
  (enumerate (distinctBoxLinks n)).map fun indexed =>
    linkBlockBase n indexed.1

def gaugeHeatKernelBoxPackets (n : Nat) : Nat → CharacterPacket 2 :=
  fun edge => if edge < plaquetteEdgeCount n
    then heatKernelPacket 2 coupling
    else if edge ∈ vacuumBaseEdgeIds n
      then vacuumPacket 2
      else allOnesPacket 2

def incidentPlaqIdsByLinkId (n linkId : Nat) : List Nat :=
  match (enumerate (distinctBoxLinks n))[linkId]? with
  | none => []
  | some indexed => incidentPlaqIds n indexed.2

def selectedPrefixCount (n linkId prefixLength : Nat) : Nat :=
  (((incidentPlaqIdsByLinkId n linkId).take prefixLength).filter
    fun plaquetteId => decide (plaquetteId ∈ unitCubeSurfaceIds n)).length

def unitCubeSurfaceLabel (n : Nat) : EdgeLabelling :=
  fun edge =>
    if edge ∈ usedResolutionEdges n then
      if edge < plaquetteEdgeCount n then
        if edge ∈ unitCubeSurfaceIds n then 2 else 0
      else
        let delta := edge - plaquetteEdgeCount n
        let offset := delta % 8
        if offset = 0 then 0
        else if selectedPrefixCount n (delta / 8) (offset + 1) % 2 = 1
          then 2 else 0
    else 0

#eval unitCubeSurfaceIds 2

example : GraphPhysical (usedResolutionEdges 2) (resolutionVertices 2)
    (unitCubeSurfaceLabel 2) := by decide

example : unitCubeSurfaceLabel 2 ∈ boundedEdgeLabellings 2
    (usedResolutionEdges 2) := by
  apply boundedEdgeLabellings_complete
  · intro edge he
    simp only [unitCubeSurfaceLabel, if_pos he]
    split
    · split <;> omega
    · split
      · omega
      · split <;> omega
  · intro edge he
    simp [unitCubeSurfaceLabel, he]

example : packetGraphProjectedAmplitude (usedResolutionEdges 2)
    (resolutionVertices 2) (gaugeHeatKernelBoxPackets 2)
    (unitCubeSurfaceLabel 2) ≈ firstBoxHeatKernelAmplitude := by decide

example : GraphPhysical (usedResolutionEdges 1) (resolutionVertices 1)
    (heatKernelSpinOneLabel 1) := by decide

example : packetGraphProjectedAmplitude (usedResolutionEdges 1)
    (resolutionVertices 1) (heatKernelBoxPackets 1)
    (heatKernelSpinOneLabel 1) ≈
      Q'.mkPos 729 281474976710656 (by decide) := by decide

end ScratchZ4HeatKernelBoxState
