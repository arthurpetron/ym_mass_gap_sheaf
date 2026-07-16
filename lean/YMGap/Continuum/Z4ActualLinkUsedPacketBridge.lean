/-
# The production packet agrees with the exact local resolver packet

The uniform local Haar theorem used a complete reserved block, assigning
normalized vacuum packets to coordinates that no resolver vertex reads.  The
production graph instead lists only identifiers that do occur in vertices.
This module transports the reduced canonical coordinate list directly to an
actually enumerated finite-box link and proves pointwise agreement with the
production fusion-complete heat-kernel packet.
-/

import YMGap.Continuum.Z4AllActualLinkGraphHaar
import YMGap.Continuum.Z4FiniteGraphVacuumFloor

namespace YMGap.Continuum.Z4ActualLinkUsedPacketBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4AllActualLinkGraphHaar
open YMGap.Continuum.Z4CanonicalLinkCartesianTransport
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4GraphIdentifierCartesianTransport
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge
open YMGap.Continuum.Z4VertexCartesianVacuumRemoval

local infix:50 " ≈ " => Q'.eqv

/-- Actual identifiers read by one resolver, with all unused positions of its
reserved block omitted. -/
def actualLinkUsedCoordinates (n i : Nat) (ell : Z4Link) : List Nat :=
  let labels := incidentPlaqIds n ell
  (canonicalUsedCoordinates labels.length).map
    (localIdentifierRename labels (linkBlockBase n i))

/-- The actual production packet and vertex syntax, restricted to one
enumerated link's genuinely used identifiers. -/
def productionActualLinkUsedVertexCartesianSum (K n i : Nat)
    (ell : Z4Link) : Q' :=
  vertexCartesianSum (actualLinkUsedCoordinates n i ell)
    (linkResolutionVertices n i ell)
    (gaugeHeatKernelBoxPacketsFusionComplete K n)

/-! ## 1. The canonical used list is exactly vertex-covering -/

theorem canonicalUsed_verticesCovered {degree : Nat}
    (hdegree : degree ≤ linkIncidenceBound) :
    VerticesCoveredBy (canonicalUsedCoordinates degree)
      (fuseLabels degree (degree + 1) (List.range degree)) := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro v hv
    cases hv
  · intro v hv edge hedge
    change v ∈ [(0, 1, 1)] at hv
    simp only [List.mem_singleton] at hv
    subst v
    unfold VertexContains at hedge
    rcases hedge with rfl | rfl | rfl <;> simp [canonicalUsedCoordinates]
  · intro v hv edge hedge
    change v ∈ [(0, 1, 2)] at hv
    simp only [List.mem_singleton] at hv
    subst v
    unfold VertexContains at hedge
    rcases hedge with rfl | rfl | rfl <;> simp [canonicalUsedCoordinates]
  · intro v hv edge hedge
    change v ∈ [(0, 1, 2)] at hv
    simp only [List.mem_singleton] at hv
    subst v
    unfold VertexContains at hedge
    rcases hedge with rfl | rfl | rfl <;> simp [canonicalUsedCoordinates]
  · intro v hv edge hedge
    change v ∈ [(0, 1, 5), (5, 2, 3)] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;>
      unfold VertexContains at hedge <;>
      rcases hedge with rfl | rfl | rfl <;> simp [canonicalUsedCoordinates]
  · intro v hv edge hedge
    change v ∈ [(0, 1, 6), (6, 2, 7), (7, 3, 4)] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;>
      unfold VertexContains at hedge <;>
      rcases hedge with rfl | rfl | rfl <;> simp [canonicalUsedCoordinates]
  · intro v hv edge hedge
    change v ∈ [(0, 1, 7), (7, 2, 8), (8, 3, 9), (9, 4, 5)] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;>
      unfold VertexContains at hedge <;>
      rcases hedge with rfl | rfl | rfl <;> simp [canonicalUsedCoordinates]

theorem canonicalUsed_mem_localCoordinates {degree edge : Nat}
    (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalUsedCoordinates degree) :
    edge ∈ canonicalLocalCoordinates degree := by
  have hp := canonicalCoordinates_perm_unused_used hdegree
  exact hp.mem_iff.mpr (List.mem_append_right _ hedge)

private theorem localRename_injective_used
    (n i : Nat) (ell : Z4Link) :
    InjectiveOnList
      (localIdentifierRename (incidentPlaqIds n ell) (linkBlockBase n i))
      (canonicalUsedCoordinates (incidentPlaqIds n ell).length) := by
  let labels := incidentPlaqIds n ell
  let f := localIdentifierRename labels (linkBlockBase n i)
  have hfull : InjectiveOnList f
      (canonicalLocalCoordinates labels.length) :=
    injectiveOnList_of_map_nodup f _
      (renamed_canonicalLocalCoordinates_nodup n i ell)
  have hdegree : labels.length ≤ linkIncidenceBound :=
    incidentPlaqIds_length_le_six n ell
  intro x hx y hy hxy
  exact hfull x (canonicalUsed_mem_localCoordinates hdegree hx)
    y (canonicalUsed_mem_localCoordinates hdegree hy) hxy

/-! ## 2. Used-coordinate shape and vacuum-base separation -/

theorem canonicalUsed_coordinate_shape {degree edge : Nat}
    (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalUsedCoordinates degree) :
    edge < degree ∨ edge = degree ∨
      ∃ j, edge = degree + j ∧ j ≠ 0 ∧ j < 8 ∧ j + 3 ≤ degree := by
  cases degree with
  | zero =>
      simp [canonicalUsedCoordinates] at hedge
  | succ d1 =>
      cases d1 with
      | zero =>
          simp only [canonicalUsedCoordinates, List.mem_cons,
            List.not_mem_nil, or_false] at hedge
          rcases hedge with rfl | rfl
          · exact Or.inl (by decide)
          · exact Or.inr (Or.inl rfl)
      | succ d2 =>
          cases d2 with
          | zero =>
              simp only [canonicalUsedCoordinates, List.mem_cons,
                List.not_mem_nil, or_false] at hedge
              rcases hedge with rfl | rfl | rfl
              · exact Or.inl (by decide)
              · exact Or.inl (by decide)
              · exact Or.inr (Or.inl rfl)
          | succ d3 =>
              cases d3 with
              | zero =>
                  simp only [canonicalUsedCoordinates, List.mem_cons,
                    List.not_mem_nil, or_false] at hedge
                  rcases hedge with rfl | rfl | rfl <;>
                    exact Or.inl (by decide)
              | succ d4 =>
                  cases d4 with
                  | zero =>
                      simp only [canonicalUsedCoordinates, List.mem_cons,
                        List.not_mem_nil, or_false] at hedge
                      rcases hedge with rfl | rfl | rfl | rfl | rfl
                      · exact Or.inl (by decide)
                      · exact Or.inl (by decide)
                      · exact Or.inl (by decide)
                      · exact Or.inl (by decide)
                      · exact Or.inr (Or.inr ⟨1, by decide⟩)
                  | succ d5 =>
                      cases d5 with
                      | zero =>
                          simp only [canonicalUsedCoordinates, List.mem_cons,
                            List.not_mem_nil, or_false] at hedge
                          rcases hedge with rfl | rfl | rfl | rfl | rfl |
                              rfl | rfl
                          · exact Or.inl (by decide)
                          · exact Or.inl (by decide)
                          · exact Or.inl (by decide)
                          · exact Or.inl (by decide)
                          · exact Or.inl (by decide)
                          · exact Or.inr (Or.inr ⟨1, by decide⟩)
                          · exact Or.inr (Or.inr ⟨2, by decide⟩)
                      | succ d6 =>
                          cases d6 with
                          | zero =>
                              simp only [canonicalUsedCoordinates,
                                List.mem_cons, List.not_mem_nil, or_false]
                                at hedge
                              rcases hedge with rfl | rfl | rfl | rfl |
                                  rfl | rfl | rfl | rfl | rfl
                              · exact Or.inl (by decide)
                              · exact Or.inl (by decide)
                              · exact Or.inl (by decide)
                              · exact Or.inl (by decide)
                              · exact Or.inl (by decide)
                              · exact Or.inl (by decide)
                              · exact Or.inr (Or.inr ⟨1, by decide⟩)
                              · exact Or.inr (Or.inr ⟨2, by decide⟩)
                              · exact Or.inr (Or.inr ⟨3, by decide⟩)
                          | succ beyond =>
                              exfalso
                              unfold linkIncidenceBound at hdegree
                              omega

private theorem canonicalVertices_two_exact :
    fuseLabels 2 3 (List.range 2) = [(0, 1, 2)] := by rfl

private theorem canonicalVertices_three_exact :
    fuseLabels 3 4 (List.range 3) = [(0, 1, 2)] := by rfl

private theorem canonicalVertices_four_exact :
    fuseLabels 4 5 (List.range 4) = [(0, 1, 5), (5, 2, 3)] := by rfl

private theorem canonicalVertices_five_exact :
    fuseLabels 5 6 (List.range 5) =
      [(0, 1, 6), (6, 2, 7), (7, 3, 4)] := by rfl

private theorem canonicalVertices_six_exact :
    fuseLabels 6 7 (List.range 6) =
      [(0, 1, 7), (7, 2, 8), (8, 3, 9), (9, 4, 5)] := by rfl

/-- Every coordinate retained in the reduced canonical list actually occurs
in at least one resolver vertex. -/
theorem canonicalUsed_coordinate_occurs {degree edge : Nat}
    (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalUsedCoordinates degree) :
    ∃ v, v ∈ fuseLabels degree (degree + 1) (List.range degree) ∧
      VertexContains edge v := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [canonicalUsedCoordinates] at hedge
  · simp only [canonicalUsedCoordinates, List.mem_cons,
      List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl
    · exact ⟨(0, 1, 1), by simp [fuseLabels], Or.inl rfl⟩
    · exact ⟨(0, 1, 1), by simp [fuseLabels], Or.inr (Or.inl rfl)⟩
  · simp only [canonicalUsedCoordinates, List.mem_cons,
      List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact ⟨(0, 1, 2), by rw [canonicalVertices_two_exact]; simp,
        Or.inl rfl⟩
    · exact ⟨(0, 1, 2), by rw [canonicalVertices_two_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(0, 1, 2), by rw [canonicalVertices_two_exact]; simp,
        Or.inr (Or.inr rfl)⟩
  · simp only [canonicalUsedCoordinates, List.mem_cons,
      List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact ⟨(0, 1, 2), by rw [canonicalVertices_three_exact]; simp,
        Or.inl rfl⟩
    · exact ⟨(0, 1, 2), by rw [canonicalVertices_three_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(0, 1, 2), by rw [canonicalVertices_three_exact]; simp,
        Or.inr (Or.inr rfl)⟩
  · simp only [canonicalUsedCoordinates, List.mem_cons,
      List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(0, 1, 5), by rw [canonicalVertices_four_exact]; simp,
        Or.inl rfl⟩
    · exact ⟨(0, 1, 5), by rw [canonicalVertices_four_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(5, 2, 3), by rw [canonicalVertices_four_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(5, 2, 3), by rw [canonicalVertices_four_exact]; simp,
        Or.inr (Or.inr rfl)⟩
    · exact ⟨(0, 1, 5), by rw [canonicalVertices_four_exact]; simp,
        Or.inr (Or.inr rfl)⟩
  · simp only [canonicalUsedCoordinates, List.mem_cons,
      List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(0, 1, 6), by rw [canonicalVertices_five_exact]; simp,
        Or.inl rfl⟩
    · exact ⟨(0, 1, 6), by rw [canonicalVertices_five_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(6, 2, 7), by rw [canonicalVertices_five_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(7, 3, 4), by rw [canonicalVertices_five_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(7, 3, 4), by rw [canonicalVertices_five_exact]; simp,
        Or.inr (Or.inr rfl)⟩
    · exact ⟨(0, 1, 6), by rw [canonicalVertices_five_exact]; simp,
        Or.inr (Or.inr rfl)⟩
    · exact ⟨(6, 2, 7), by rw [canonicalVertices_five_exact]; simp,
        Or.inr (Or.inr rfl)⟩
  · simp only [canonicalUsedCoordinates, List.mem_cons,
      List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(0, 1, 7), by rw [canonicalVertices_six_exact]; simp,
        Or.inl rfl⟩
    · exact ⟨(0, 1, 7), by rw [canonicalVertices_six_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(7, 2, 8), by rw [canonicalVertices_six_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(8, 3, 9), by rw [canonicalVertices_six_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(9, 4, 5), by rw [canonicalVertices_six_exact]; simp,
        Or.inr (Or.inl rfl)⟩
    · exact ⟨(9, 4, 5), by rw [canonicalVertices_six_exact]; simp,
        Or.inr (Or.inr rfl)⟩
    · exact ⟨(0, 1, 7), by rw [canonicalVertices_six_exact]; simp,
        Or.inr (Or.inr rfl)⟩
    · exact ⟨(7, 2, 8), by rw [canonicalVertices_six_exact]; simp,
        Or.inr (Or.inr rfl)⟩
    · exact ⟨(8, 3, 9), by rw [canonicalVertices_six_exact]; simp,
        Or.inr (Or.inr rfl)⟩

private theorem renamedVertex_edge_mem
    (f : Nat → Nat) {edge : Nat} {v : TrivalentVertex}
    (hedge : VertexContains edge v) :
    f edge ∈ vertexEdgeIds (mapTrivalentVertex f v) := by
  unfold VertexContains at hedge
  rcases hedge with rfl | rfl | rfl <;>
    simp [vertexEdgeIds, mapTrivalentVertex]

private theorem productionVertexEdge_mem_usedResolutionEdges
    {n : Nat} {v : TrivalentVertex} (hv : v ∈ resolutionVertices n)
    {edge : Nat} (hedge : edge ∈ vertexEdgeIds v) :
    edge ∈ usedResolutionEdges n := by
  by_cases hphysical : edge < plaquetteEdgeCount n
  · exact List.mem_append_left _ (List.mem_range.mpr hphysical)
  · apply List.mem_append_right
    unfold usedAuxiliaryEdges
    apply List.mem_eraseDups.mpr
    apply List.mem_filter.mpr
    refine ⟨List.mem_flatMap.mpr ⟨v, hv, hedge⟩, ?_⟩
    simpa only [decide_eq_true_eq] using (show plaquetteEdgeCount n ≤ edge by
      omega)

/-- Every identifier in an actually enumerated link's reduced coordinate
list is one of the production graph's globally listed identifiers. -/
theorem actualLinkUsedCoordinates_mem_usedResolutionEdges
    {n i : Nat} {ell : Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n)) :
    ∀ edge, edge ∈ actualLinkUsedCoordinates n i ell →
      edge ∈ usedResolutionEdges n := by
  intro actualEdge hactual
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let f := localIdentifierRename labels base
  change actualEdge ∈ (canonicalUsedCoordinates degree).map f at hactual
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hactual
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  obtain ⟨v, hv, hcontains⟩ :=
    canonicalUsed_coordinate_occurs hdegree hedge
  have hvlocal : mapTrivalentVertex f v ∈
      linkResolutionVertices n i ell := by
    have hvmap : mapTrivalentVertex f v ∈
        (fuseLabels degree (degree + 1) (List.range degree)).map
          (mapTrivalentVertex f) :=
      List.mem_map.mpr ⟨v, hv, rfl⟩
    have hvertices := canonical_linkResolutionVertices_map n i ell
    dsimp only at hvertices
    change (fuseLabels degree (degree + 1) (List.range degree)).map
        (mapTrivalentVertex f) = linkResolutionVertices n i ell at hvertices
    rw [hvertices] at hvmap
    exact hvmap
  have hvglobal : mapTrivalentVertex f v ∈ resolutionVertices n := by
    unfold resolutionVertices
    exact List.mem_flatMap.mpr ⟨(i, ell), hindexed, hvlocal⟩
  exact productionVertexEdge_mem_usedResolutionEdges hvglobal
    (renamedVertex_edge_mem f hcontains)

theorem linkBlockBase_mem_vacuumBaseEdgeIds
    {n i : Nat} {ell : Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n)) :
    linkBlockBase n i ∈ vacuumBaseEdgeIds n := by
  unfold vacuumBaseEdgeIds
  exact List.mem_map.mpr ⟨(i, ell), hindexed, rfl⟩

theorem linkBlockBase_add_not_mem_vacuumBaseEdgeIds
    {n i j : Nat} (hjpos : j ≠ 0) (hjlt : j < 8) :
    linkBlockBase n i + j ∉ vacuumBaseEdgeIds n := by
  intro hmem
  unfold vacuumBaseEdgeIds at hmem
  obtain ⟨indexed, _, heq⟩ := List.mem_map.mp hmem
  change linkBlockBase n indexed.1 = linkBlockBase n i + j at heq
  unfold linkBlockBase at heq
  omega

/-! ## 3. Pointwise production-packet agreement -/

theorem productionPacket_agrees_on_actualLinkUsed
    {K n i : Nat} {ell : Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n)) :
    ∀ edge,
      edge ∈ canonicalUsedCoordinates (incidentPlaqIds n ell).length →
      gaugeHeatKernelBoxPacketsFusionComplete K n
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) edge) =
        canonicalLinkGraphPacket (heatKernelPacket K coupling)
          (incidentPlaqIds n ell).length edge := by
  intro edge hedge
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let f := localIdentifierRename labels base
  change edge ∈ canonicalUsedCoordinates degree at hedge
  change gaugeHeatKernelBoxPacketsFusionComplete K n (f edge) =
    canonicalLinkGraphPacket (heatKernelPacket K coupling) degree edge
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  obtain hphysical | hbase | ⟨j, hedgeEq, hjpos, hjlt, hjinternal⟩ :=
    canonicalUsed_coordinate_shape hdegree hedge
  · have hedgeRange : edge ∈ List.range labels.length :=
      List.mem_range.mpr hphysical
    have hmapped : f edge ∈ labels := by
      have hmappedRange : f edge ∈
          (List.range labels.length).map f :=
        List.mem_map.mpr ⟨edge, hedgeRange, rfl⟩
      rw [map_localIdentifierRename_range labels base] at hmappedRange
      exact hmappedRange
    have hmappedLt : f edge < plaquetteEdgeCount n :=
      incidentPlaqId_lt_count hmapped
    unfold gaugeHeatKernelBoxPacketsFusionComplete canonicalLinkGraphPacket
    rw [if_pos hmappedLt, if_pos hphysical]
    rfl
  · subst edge
    have hrename : f degree = base := by
      dsimp [f, degree, base]
      simpa using localIdentifierRename_length_add labels (linkBlockBase n i) 0
    have hnotPhysical : ¬ base < plaquetteEdgeCount n := by
      have hge := linkBlockBase_ge_count n i
      dsimp [base]
      omega
    have hvac : base ∈ vacuumBaseEdgeIds n := by
      dsimp [base]
      exact linkBlockBase_mem_vacuumBaseEdgeIds hindexed
    unfold gaugeHeatKernelBoxPacketsFusionComplete canonicalLinkGraphPacket
    rw [hrename, if_neg hnotPhysical, if_pos hvac]
    simp
  · subst edge
    have hrename : f (degree + j) = base + j := by
      dsimp [f, degree, base]
      exact localIdentifierRename_length_add labels (linkBlockBase n i) j
    have hnotPhysical : ¬ base + j < plaquetteEdgeCount n := by
      have hge := linkBlockBase_ge_count n i
      dsimp [base]
      omega
    have hnotVac : base + j ∉ vacuumBaseEdgeIds n := by
      dsimp [base]
      exact linkBlockBase_add_not_mem_vacuumBaseEdgeIds hjpos hjlt
    have hcanonicalNotPhysical : ¬ degree + j < degree := by omega
    unfold gaugeHeatKernelBoxPacketsFusionComplete canonicalLinkGraphPacket
    rw [hrename, if_neg hnotPhysical, if_neg hnotVac,
      if_neg hcanonicalNotPhysical]
    simp only [Nat.add_sub_cancel_left]
    rw [if_neg hjpos, if_pos hjinternal]

/-! ## 4. The reduced production block is the exact local Haar moment -/

theorem productionActualLinkUsedVertexCartesianSum_eq_canonical
    {K n i : Nat} {ell : Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n)) :
    productionActualLinkUsedVertexCartesianSum K n i ell ≈
      canonicalUsedVertexCartesianSum (heatKernelPacket K coupling)
        (incidentPlaqIds n ell).length := by
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let f := localIdentifierRename labels base
  let edges := canonicalUsedCoordinates degree
  let vertices := fuseLabels degree (degree + 1) (List.range degree)
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  have htransport := vertexCartesianSum_rename
    (K := linkAuxiliaryCutoff K) f edges vertices
    (canonicalLinkGraphPacket (heatKernelPacket K coupling) degree)
    (gaugeHeatKernelBoxPacketsFusionComplete K n)
    (by
      dsimp [f, edges, degree, labels, base]
      exact localRename_injective_used n i ell)
    (by
      dsimp [edges, vertices]
      exact canonicalUsed_verticesCovered hdegree)
    (by
      intro edge hedge
      dsimp [f, edges, degree, labels, base] at hedge ⊢
      exact productionPacket_agrees_on_actualLinkUsed hindexed edge hedge)
  have hvertices : vertices.map (mapTrivalentVertex f) =
      linkResolutionVertices n i ell := by
    dsimp [vertices, f, degree, labels, base]
    exact canonical_linkResolutionVertices_map n i ell
  rw [hvertices] at htransport
  exact htransport

theorem productionActualLinkUsedVertexCartesianSum_eq_bareHaar
    {K n i : Nat} {ell : Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n)) :
    productionActualLinkUsedVertexCartesianSum K n i ell ≈
      bareVacuumHaar
        (characterPow (synthesis (heatKernelPacket K coupling))
          (incidentPlaqIds n ell).length) := by
  have hdegree : (incidentPlaqIds n ell).length ≤ linkIncidenceBound :=
    incidentPlaqIds_length_le_six n ell
  exact Q'.eqv_trans _
    (canonicalUsedVertexCartesianSum (heatKernelPacket K coupling)
      (incidentPlaqIds n ell).length) _
    (productionActualLinkUsedVertexCartesianSum_eq_canonical hindexed)
    (canonicalUsedVertexCartesianSum_eq_bareHaar
      (heatKernelPacket K coupling) hdegree)

end YMGap.Continuum.Z4ActualLinkUsedPacketBridge

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ActualLinkUsedPacketBridge.canonicalUsed_verticesCovered
#print axioms YMGap.Continuum.Z4ActualLinkUsedPacketBridge.canonicalUsed_coordinate_shape
#print axioms YMGap.Continuum.Z4ActualLinkUsedPacketBridge.canonicalUsed_coordinate_occurs
#print axioms YMGap.Continuum.Z4ActualLinkUsedPacketBridge.actualLinkUsedCoordinates_mem_usedResolutionEdges
#print axioms YMGap.Continuum.Z4ActualLinkUsedPacketBridge.linkBlockBase_add_not_mem_vacuumBaseEdgeIds
#print axioms YMGap.Continuum.Z4ActualLinkUsedPacketBridge.productionPacket_agrees_on_actualLinkUsed
#print axioms YMGap.Continuum.Z4ActualLinkUsedPacketBridge.productionActualLinkUsedVertexCartesianSum_eq_canonical
#print axioms YMGap.Continuum.Z4ActualLinkUsedPacketBridge.productionActualLinkUsedVertexCartesianSum_eq_bareHaar
