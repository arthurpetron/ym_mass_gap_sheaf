import YMGap.Continuum.Z4FiniteBoxTrivalentResolution
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport

namespace ScratchZ4FiniteBoxPacketState

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport
open YMGap.Continuum.SU2PeterWeylWilsonBlock

local infix:50 " ≈ " => Q'.eqv

def vertexEdgeIds (v : TrivalentVertex) : List Nat :=
  [v.1, v.2.1, v.2.2]

def closedResolutionEdges (n : Nat) : List Nat :=
  resolutionEdges n ++ (resolutionVertices n).flatMap vertexEdgeIds

def boxPacketState (n : Nat) : CompensatedGraphState 2 where
  edges := closedResolutionEdges n
  vertices := resolutionVertices n
  packet := fun _ => allOnesPacket 2
  copiedEdges := []
  copied_mem := by
    intro edge h
    cases h

theorem boxPacketState_uncompensated (n : Nat) :
    (boxPacketState n).copiedEdges = [] := rfl

theorem boxPacketState_uniform_gap (n : Nat) :
    SpectralGapBound (supportedGraphSpectralModel (boxPacketState n))
      (eighth * eighth) :=
  path_supported_gap_from_uncompensated (.refl _) rfl

def resolutionSpinOneLabel (n : Nat) : EdgeLabelling :=
  fun edge => if edge ∈ closedResolutionEdges n then 2 else 0

theorem resolutionSpinOneLabel_mem_bounded (n : Nat) :
    resolutionSpinOneLabel n ∈ boundedEdgeLabellings 2
      (closedResolutionEdges n) := by
  apply boundedEdgeLabellings_complete
  · intro edge he
    simp [resolutionSpinOneLabel, he]
  · intro edge he
    simp [resolutionSpinOneLabel, he]

theorem vertex_mem_closedResolutionEdges {n : Nat} {v : TrivalentVertex}
    (hv : v ∈ resolutionVertices n) :
    v.1 ∈ closedResolutionEdges n ∧
      v.2.1 ∈ closedResolutionEdges n ∧
      v.2.2 ∈ closedResolutionEdges n := by
  have hflat : v.1 ∈ (resolutionVertices n).flatMap vertexEdgeIds ∧
      v.2.1 ∈ (resolutionVertices n).flatMap vertexEdgeIds ∧
      v.2.2 ∈ (resolutionVertices n).flatMap vertexEdgeIds := by
    constructor
    · exact List.mem_flatMap.mpr ⟨v, hv, by simp [vertexEdgeIds]⟩
    constructor
    · exact List.mem_flatMap.mpr ⟨v, hv, by simp [vertexEdgeIds]⟩
    · exact List.mem_flatMap.mpr ⟨v, hv, by simp [vertexEdgeIds]⟩
  exact ⟨List.mem_append_right _ hflat.1,
    List.mem_append_right _ hflat.2.1,
    List.mem_append_right _ hflat.2.2⟩

theorem verticesAdmissibleB_resolutionSpinOne (n : Nat) :
    verticesAdmissibleB (resolutionVertices n) (resolutionSpinOneLabel n) =
      true := by
  have general : ∀ vertices : List TrivalentVertex,
      (∀ v, v ∈ vertices →
        v.1 ∈ closedResolutionEdges n ∧
          v.2.1 ∈ closedResolutionEdges n ∧
          v.2.2 ∈ closedResolutionEdges n) →
      verticesAdmissibleB vertices (resolutionSpinOneLabel n) = true := by
    intro vertices hvertices
    induction vertices with
    | nil => rfl
    | cons v rest ih =>
        have hv := hvertices v List.mem_cons_self
        have hrest : ∀ w, w ∈ rest →
            w.1 ∈ closedResolutionEdges n ∧
              w.2.1 ∈ closedResolutionEdges n ∧
              w.2.2 ∈ closedResolutionEdges n :=
          fun w hw => hvertices w (List.mem_cons_of_mem v hw)
        simp only [verticesAdmissibleB]
        simp only [resolutionSpinOneLabel, if_pos hv.1, if_pos hv.2.1,
          if_pos hv.2.2]
        change (if YMGap.Continuum.BondMovingStep.fusionOK 2 2 2 = true
          then verticesAdmissibleB rest (resolutionSpinOneLabel n)
          else false) = true
        rw [if_pos (by decide)]
        exact ih hrest
  exact general (resolutionVertices n)
    (fun v hv => vertex_mem_closedResolutionEdges hv)

theorem hasExcitedB_true_of_mem (label : EdgeLabelling) :
    ∀ {edges : List Nat} {edge : Nat}, edge ∈ edges → 1 ≤ label edge →
      hasExcitedB label edges = true
  | [], _, h, _ => by cases h
  | head :: rest, edge, h, he => by
      simp only [List.mem_cons] at h
      rcases h with rfl | hrest
      · simp [hasExcitedB, he]
      · by_cases hhead : 1 ≤ label head
        · simp [hasExcitedB, hhead]
        · simp [hasExcitedB, hhead,
            hasExcitedB_true_of_mem label hrest he]

theorem zero_mem_closedResolutionEdges (n : Nat) :
    0 ∈ closedResolutionEdges (n + 1) := by
  apply List.mem_append_left
  unfold resolutionEdges
  apply List.mem_append_left
  apply List.mem_range.mpr
  unfold plaquetteEdgeCount
  rw [YMGap.Continuum.Z4FiniteBoxExhaustion.boxPlaquettes_length]
  exact Nat.mul_pos
    (Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos (by omega) (by omega))
        (by omega))
      (by omega))
    (by decide)

theorem resolutionSpinOneLabel_physical (n : Nat) :
    GraphPhysical (closedResolutionEdges (n + 1))
      (resolutionVertices (n + 1)) (resolutionSpinOneLabel (n + 1)) := by
  unfold GraphPhysical graphPhysicalB
  have hzero := zero_mem_closedResolutionEdges n
  have hlabel : resolutionSpinOneLabel (n + 1) 0 = 2 := by
    simp [resolutionSpinOneLabel, hzero]
  have hexc : hasExcitedB (resolutionSpinOneLabel (n + 1))
      (closedResolutionEdges (n + 1)) = true := by
    apply hasExcitedB_true_of_mem _ hzero
    rw [hlabel]
    omega
  rw [hexc, verticesAdmissibleB_resolutionSpinOne]
  rfl

theorem eliminateLinks_allOnes_eqv_one (label : EdgeLabelling) :
    ∀ edges : List Nat, (∀ edge, edge ∈ edges → label edge < 3) →
      YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork.eliminateLinks
        (fun edge => YMGap.Continuum.SU2CharacterVacuumHaar.coeffAt
          (allOnesPacket 2) (label edge)) edges ≈ 1
  | [], _ => Q'.eqv_refl 1
  | edge :: rest, h => by
      have hedge : label edge < 3 := h edge List.mem_cons_self
      have hrest : ∀ e, e ∈ rest → label e < 3 :=
        fun e he => h e (List.mem_cons_of_mem edge he)
      simp only [YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork.eliminateLinks]
      rw [coeffAt_allOnesPacket hedge]
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (eliminateLinks_allOnes_eqv_one label rest hrest))
        (Q'.one_mul_eqv 1)

theorem boxAllOnesProjectedAmplitude_eqv_one {n : Nat}
    (hphysical : GraphPhysical (closedResolutionEdges n) (resolutionVertices n)
      (resolutionSpinOneLabel n)) :
    packetGraphProjectedAmplitude (closedResolutionEdges n) (resolutionVertices n)
        (fun _ => allOnesPacket 2) (resolutionSpinOneLabel n) ≈ 1 := by
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  rw [if_pos hphysical]
  unfold packetGraphBareAmplitude
  apply eliminateLinks_allOnes_eqv_one
  intro edge he
  simp [resolutionSpinOneLabel, he]

theorem resolutionSpinOneLabel_one_physical :
    GraphPhysical (closedResolutionEdges 1) (resolutionVertices 1)
      (resolutionSpinOneLabel 1) := by
  simpa using resolutionSpinOneLabel_physical 0

theorem resolutionSpinOneLabel_one_mem_physical :
    resolutionSpinOneLabel 1 ∈ physicalEdgeLabellings 2
      (closedResolutionEdges 1) (resolutionVertices 1) := by
  exact List.mem_filter.mpr
    ⟨resolutionSpinOneLabel_mem_bounded 1,
      resolutionSpinOneLabel_one_physical⟩

theorem boxPacketState_one_nonzero_mode :
    ∃ i, i < (physicalEdgeLabellings 2 (closedResolutionEdges 1)
        (resolutionVertices 1)).length ∧
      packetGraphModeWeight (closedResolutionEdges 1) (resolutionVertices 1)
        (fun _ => allOnesPacket 2) i ≈ 1 := by
  obtain ⟨i, hi, hget⟩ :=
    List.getElem_of_mem resolutionSpinOneLabel_one_mem_physical
  refine ⟨i, hi, ?_⟩
  have hlabel : physicalModeLabel 2 (closedResolutionEdges 1)
      (resolutionVertices 1) i = resolutionSpinOneLabel 1 := by
    unfold physicalModeLabel supportLabel
    rw [List.getElem?_eq_getElem hi, Option.getD_some, hget]
  unfold packetGraphModeWeight
  rw [hlabel]
  exact Q'.eqv_trans _ (1 * 1) _
    (Q'.eqv_trans _
      (1 * packetGraphProjectedAmplitude (closedResolutionEdges 1)
        (resolutionVertices 1) (fun _ => allOnesPacket 2)
        (resolutionSpinOneLabel 1)) _
      (Q'.mul_eqv_congr_right _ _ _
        (boxAllOnesProjectedAmplitude_eqv_one
          resolutionSpinOneLabel_one_physical))
      (Q'.mul_eqv_congr_left _ _ _
        (boxAllOnesProjectedAmplitude_eqv_one
          resolutionSpinOneLabel_one_physical)))
    (Q'.one_mul_eqv 1)

theorem boxPacketState_edgeCountUnbounded (bound : Nat) :
    ∃ n : Nat, bound ≤ (boxPacketState n).edges.length := by
  obtain ⟨n, hn⟩ :=
    YMGap.Continuum.Z4FiniteBoxExhaustion.boxPlaquetteCount_unbounded bound
  refine ⟨n, ?_⟩
  change bound ≤ (closedResolutionEdges n).length
  unfold closedResolutionEdges
  rw [List.length_append]
  have hres : bound ≤ (resolutionEdges n).length := by
    rw [resolutionEdges_length]
    unfold plaquetteEdgeCount
    omega
  omega

theorem boxPacketState_nonzero_mode (n : Nat) :
    ∃ i, i < (physicalEdgeLabellings 2 (closedResolutionEdges (n + 1))
        (resolutionVertices (n + 1))).length ∧
      packetGraphModeWeight (closedResolutionEdges (n + 1))
        (resolutionVertices (n + 1)) (fun _ => allOnesPacket 2)
        i ≈ 1 := by
  have hphysical := resolutionSpinOneLabel_physical n
  have hmem : resolutionSpinOneLabel (n + 1) ∈
      physicalEdgeLabellings 2 (closedResolutionEdges (n + 1))
        (resolutionVertices (n + 1)) :=
    List.mem_filter.mpr
      ⟨resolutionSpinOneLabel_mem_bounded (n + 1), hphysical⟩
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  refine ⟨i, hi, ?_⟩
  have hlabel : physicalModeLabel 2 (closedResolutionEdges (n + 1))
      (resolutionVertices (n + 1)) i = resolutionSpinOneLabel (n + 1) := by
    unfold physicalModeLabel supportLabel
    rw [List.getElem?_eq_getElem hi, Option.getD_some, hget]
  unfold packetGraphModeWeight
  rw [hlabel]
  have hamp := boxAllOnesProjectedAmplitude_eqv_one hphysical
  exact Q'.eqv_trans _ (1 * 1) _
    (Q'.eqv_trans _
      (1 * packetGraphProjectedAmplitude (closedResolutionEdges (n + 1))
        (resolutionVertices (n + 1)) (fun _ => allOnesPacket 2)
        (resolutionSpinOneLabel (n + 1))) _
      (Q'.mul_eqv_congr_right _ _ _ hamp)
      (Q'.mul_eqv_congr_left _ _ _ hamp))
    (Q'.one_mul_eqv 1)

end ScratchZ4FiniteBoxPacketState
