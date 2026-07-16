/-
# Coupling-parametric arbitrary-cutoff Z4 packet-graph identity

This module closes the graph interface isolated by
`Z4ParametricPhysicalCutoffPartition`.  It defines the literal
fusion-complete finite-box packet graph at arbitrary rational coupling `w`
and arbitrary physical representation cutoff `K`, separates physical and
auxiliary labels, and identifies its Cartesian sum with the parametric
physical spin-foam partition.

The key reuse is exact: changing `w` changes only physical plaquette packets.
Every auxiliary packet, vertex-admissibility guard, and fusion multiplicity is
the same as in the already checked `w = 1/2` construction.  No positivity
assumption on `w` is required for the identity.
-/

import YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

namespace YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. The literal parameterized fusion-complete graph -/

def parametricFusionCompleteBoxPackets (w : Q') (K n : Nat) :
    Nat → CharacterPacket (linkAuxiliaryCutoff K) :=
  fun edge =>
    if edge < plaquetteEdgeCount n then
      padPacket (externalCutoff_le_linkAuxiliaryCutoff K)
        (heatKernelPacket K w)
    else if edge ∈ vacuumBaseEdgeIds n then
      vacuumPacket (linkAuxiliaryCutoff K)
    else
      allOnesPacket (linkAuxiliaryCutoff K)

def parametricFusionCompleteBoxState (w : Q') (K n : Nat) :
    CompensatedGraphState (linkAuxiliaryCutoff K) where
  edges := usedResolutionEdges n
  vertices := resolutionVertices n
  packet := parametricFusionCompleteBoxPackets w K n
  copiedEdges := []
  copied_mem := by intro edge h; cases h

def parametricFusionCompleteBoxVertexIntegrand
    (w : Q') (K n : Nat) : GraphPacket :=
  graphVertexProject (resolutionVertices n)
    (packetGraphBareAmplitude (usedResolutionEdges n)
      (parametricFusionCompleteBoxPackets w K n))

def parametricFusionCompleteBoxVertexCartesianSum
    (w : Q') (K n : Nat) : Q' :=
  listQSum
    (parametricFusionCompleteBoxVertexIntegrand w K n)
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (usedResolutionEdges n))

def parametricFusionConditionalAuxiliarySum
    (w : Q') (K n : Nat) (physical : EdgeLabelling) : Q' :=
  listQSum
    (fun auxiliary =>
      graphVertexProject (resolutionVertices n)
        (packetGraphBareAmplitude (usedAuxiliaryEdges n)
          (parametricFusionCompleteBoxPackets w K n))
        (overlayOn (physicalFaceEdges n) physical auxiliary))
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (usedAuxiliaryEdges n))

def parametricFusionPhysicalPacketFactor
    (w : Q') (K n : Nat) (physical : EdgeLabelling) : Q' :=
  packetGraphBareAmplitude (physicalFaceEdges n)
    (parametricFusionCompleteBoxPackets w K n) physical

theorem parametricFusionPhysicalPacketFactor_eq_faceFactor
    (w : Q') (K n : Nat) (physical : EdgeLabelling) :
    parametricFusionPhysicalPacketFactor w K n physical =
      parametricKPhysicalFaceFactor w K n physical := by
  unfold parametricFusionPhysicalPacketFactor
    parametricKPhysicalFaceFactor packetGraphBareAmplitude
    physicalFaceEdges
  apply eliminateLinks_congr_eq
  intro edge hedge
  have hedgeLt : edge < plaquetteEdgeCount n := List.mem_range.mp hedge
  unfold parametricFusionCompleteBoxPackets
  rw [if_pos hedgeLt, coeffAt_padPacket]

theorem parametricFusionPhysicalPacketFactor_overlay
    (w : Q') (K n : Nat) (physical auxiliary : EdgeLabelling) :
    packetGraphBareAmplitude (physicalFaceEdges n)
        (parametricFusionCompleteBoxPackets w K n)
        (overlayOn (physicalFaceEdges n) physical auxiliary) =
      parametricFusionPhysicalPacketFactor w K n physical := by
  unfold parametricFusionPhysicalPacketFactor
  apply packetGraphBareAmplitude_label_eq_on
  intro edge hedge
  exact overlayOn_apply_of_mem hedge

/-! ## 2. Exact physical/auxiliary Fubini separation -/

theorem parametricFusionCompleteBoxVertexIntegrand_overlay_factor
    (w : Q') (K n : Nat) (physical auxiliary : EdgeLabelling) :
    parametricFusionCompleteBoxVertexIntegrand w K n
        (overlayOn (physicalFaceEdges n) physical auxiliary) ≈
      parametricFusionPhysicalPacketFactor w K n physical *
        graphVertexProject (resolutionVertices n)
          (packetGraphBareAmplitude (usedAuxiliaryEdges n)
            (parametricFusionCompleteBoxPackets w K n))
          (overlayOn (physicalFaceEdges n) physical auxiliary) := by
  let label := overlayOn (physicalFaceEdges n) physical auxiliary
  let packet := parametricFusionCompleteBoxPackets w K n
  have hsplit :
      packetGraphBareAmplitude (usedResolutionEdges n) packet label ≈
        packetGraphBareAmplitude (physicalFaceEdges n) packet label *
          packetGraphBareAmplitude (usedAuxiliaryEdges n) packet label := by
    unfold physicalFaceEdges
    simpa only [usedResolutionEdges] using
      (packetGraphBareAmplitude_append
        (List.range (plaquetteEdgeCount n)) (usedAuxiliaryEdges n)
        packet label)
  have hphysical :
      packetGraphBareAmplitude (physicalFaceEdges n) packet label =
        parametricFusionPhysicalPacketFactor w K n physical := by
    dsimp [packet, label]
    exact parametricFusionPhysicalPacketFactor_overlay
      w K n physical auxiliary
  by_cases hadmissible :
      verticesAdmissibleB (resolutionVertices n) label = true
  · unfold parametricFusionCompleteBoxVertexIntegrand graphVertexProject
    dsimp only [label] at hadmissible ⊢
    rw [if_pos hadmissible, if_pos hadmissible]
    dsimp only [packet] at hsplit hphysical ⊢
    rw [hphysical] at hsplit
    exact hsplit
  · unfold parametricFusionCompleteBoxVertexIntegrand graphVertexProject
    dsimp only [label] at hadmissible ⊢
    rw [if_neg hadmissible, if_neg hadmissible]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)

theorem parametricFusionConditionalInnerSum_factor
    (w : Q') (K n : Nat) (physical : EdgeLabelling) :
    listQSum
        (fun auxiliary =>
          parametricFusionCompleteBoxVertexIntegrand w K n
            (overlayOn (physicalFaceEdges n) physical auxiliary))
        (boundedEdgeLabellings (linkAuxiliaryCutoff K)
          (usedAuxiliaryEdges n)) ≈
      parametricFusionPhysicalPacketFactor w K n physical *
        parametricFusionConditionalAuxiliarySum w K n physical := by
  refine Q'.eqv_trans _
    (listQSum
      (fun auxiliary =>
        parametricFusionPhysicalPacketFactor w K n physical *
          graphVertexProject (resolutionVertices n)
            (packetGraphBareAmplitude (usedAuxiliaryEdges n)
              (parametricFusionCompleteBoxPackets w K n))
            (overlayOn (physicalFaceEdges n) physical auxiliary))
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (usedAuxiliaryEdges n))) _ ?_ ?_
  · apply listQSum_congr
    intro auxiliary
    exact parametricFusionCompleteBoxVertexIntegrand_overlay_factor
      w K n physical auxiliary
  · unfold parametricFusionConditionalAuxiliarySum
    exact listQSum_const_mul
      (parametricFusionPhysicalPacketFactor w K n physical)
      (fun auxiliary =>
        graphVertexProject (resolutionVertices n)
          (packetGraphBareAmplitude (usedAuxiliaryEdges n)
            (parametricFusionCompleteBoxPackets w K n))
          (overlayOn (physicalFaceEdges n) physical auxiliary))
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (usedAuxiliaryEdges n))

theorem parametricFusionCompleteBoxVertexCartesianSum_eq_conditional
    (w : Q') (K n : Nat) :
    parametricFusionCompleteBoxVertexCartesianSum w K n ≈
      listQSum
        (fun physical =>
          parametricFusionPhysicalPacketFactor w K n physical *
            parametricFusionConditionalAuxiliarySum w K n physical)
        (boundedEdgeLabellings (linkAuxiliaryCutoff K)
          (physicalFaceEdges n)) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        listQSum
          (fun auxiliary =>
            parametricFusionCompleteBoxVertexIntegrand w K n
              (overlayOn (physicalFaceEdges n) physical auxiliary))
          (boundedEdgeLabellings (linkAuxiliaryCutoff K)
            (usedAuxiliaryEdges n)))
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (physicalFaceEdges n))) _ ?_ ?_
  · unfold parametricFusionCompleteBoxVertexCartesianSum physicalFaceEdges
    simpa only [usedResolutionEdges] using
      (listQSum_bounded_append_fubini (linkAuxiliaryCutoff K)
        (List.range (plaquetteEdgeCount n)) (usedAuxiliaryEdges n)
        (parametricFusionCompleteBoxVertexIntegrand w K n))
  · apply listQSum_congr
    intro physical
    exact parametricFusionConditionalInnerSum_factor w K n physical

/-! ## 3. Auxiliary fusion is exactly coupling-independent -/

theorem parametricFusionAuxiliaryCoefficient_eq_production
    (w : Q') (K n edge spin : Nat)
    (hge : plaquetteEdgeCount n ≤ edge) :
    coeffAt (parametricFusionCompleteBoxPackets w K n edge) spin =
      coeffAt (gaugeHeatKernelBoxPacketsFusionComplete K n edge) spin := by
  have hnotPhysical : ¬ edge < plaquetteEdgeCount n := by omega
  unfold parametricFusionCompleteBoxPackets
    gaugeHeatKernelBoxPacketsFusionComplete
  rw [if_neg hnotPhysical, if_neg hnotPhysical]

theorem parametricFusionAuxiliaryBareAmplitude_eq_production
    (w : Q') (K n : Nat) (label : EdgeLabelling) :
    packetGraphBareAmplitude (usedAuxiliaryEdges n)
        (parametricFusionCompleteBoxPackets w K n) label =
      packetGraphBareAmplitude (usedAuxiliaryEdges n)
        (gaugeHeatKernelBoxPacketsFusionComplete K n) label := by
  unfold packetGraphBareAmplitude
  apply eliminateLinks_congr_eq
  intro edge hedge
  exact parametricFusionAuxiliaryCoefficient_eq_production
    w K n edge (label edge) (usedAuxiliaryEdge_ge_count hedge)

theorem parametricFusionAuxiliaryProject_eqv_production
    (w : Q') (K n : Nat) (label : EdgeLabelling) :
    graphVertexProject (resolutionVertices n)
        (packetGraphBareAmplitude (usedAuxiliaryEdges n)
          (parametricFusionCompleteBoxPackets w K n)) label ≈
      graphVertexProject (resolutionVertices n)
        (packetGraphBareAmplitude (usedAuxiliaryEdges n)
          (gaugeHeatKernelBoxPacketsFusionComplete K n)) label := by
  unfold graphVertexProject
  by_cases hadmissible :
      verticesAdmissibleB (resolutionVertices n) label = true
  · rw [if_pos hadmissible, if_pos hadmissible]
    exact Q'.eqv_of_eq
      (parametricFusionAuxiliaryBareAmplitude_eq_production
        w K n label)
  · rw [if_neg hadmissible, if_neg hadmissible]
    exact Q'.eqv_refl 0

theorem parametricFusionConditionalAuxiliarySum_eq_production
    (w : Q') (K n : Nat) (physical : EdgeLabelling) :
    parametricFusionConditionalAuxiliarySum w K n physical ≈
      conditionalBoxAuxiliarySum K n physical := by
  unfold parametricFusionConditionalAuxiliarySum
    conditionalBoxAuxiliarySum physicalFaceEdges
  apply listQSum_congr
  intro auxiliary
  exact parametricFusionAuxiliaryProject_eqv_production w K n
    (overlayOn (List.range (plaquetteEdgeCount n)) physical auxiliary)

theorem parametricFusionConditionalAuxiliarySum_eq_link_product
    (w : Q') (K n : Nat) (physical : EdgeLabelling) :
    parametricFusionConditionalAuxiliarySum w K n physical ≈
      explicitLinkMultiplicityProduct K n physical
        (enumerate (distinctBoxLinks n)) := by
  exact Q'.eqv_trans _ (conditionalBoxAuxiliarySum K n physical) _
    (parametricFusionConditionalAuxiliarySum_eq_production
      w K n physical)
    (Q'.eqv_trans _
      (linkAuxiliaryMultiplicityProduct K n physical
        (enumerate (distinctBoxLinks n))) _
      (conditionalBoxAuxiliarySum_eq_link_product K n physical)
      (enumeratedLinkMultiplicityProduct_eq_explicit K n physical))

theorem parametricFusionCompleteBoxVertexCartesianSum_eq_linkSpinFoam
    (w : Q') (K n : Nat) :
    parametricFusionCompleteBoxVertexCartesianSum w K n ≈
      listQSum
        (fun physical =>
          parametricKPhysicalFaceFactor w K n physical *
            explicitLinkMultiplicityProduct K n physical
              (enumerate (distinctBoxLinks n)))
        (boundedEdgeLabellings (linkAuxiliaryCutoff K)
          (physicalFaceEdges n)) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        parametricFusionPhysicalPacketFactor w K n physical *
          parametricFusionConditionalAuxiliarySum w K n physical)
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (physicalFaceEdges n))) _
    (parametricFusionCompleteBoxVertexCartesianSum_eq_conditional
      w K n) ?_
  apply listQSum_congr
  intro physical
  exact qmul_congr
    (Q'.eqv_of_eq
      (parametricFusionPhysicalPacketFactor_eq_faceFactor
        w K n physical))
    (parametricFusionConditionalAuxiliarySum_eq_link_product
      w K n physical)

/-! ## 4. Exact physical-cutoff reduction and endpoint identity -/

private theorem eliminateLinks_zero_of_mem_local
    (f : Nat → Q') {edge : Nat} : ∀ {edges : List Nat},
    edge ∈ edges → f edge ≈ 0 → eliminateLinks f edges ≈ 0
  | [], hmem, _ => by cases hmem
  | head :: rest, hmem, hz => by
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact Q'.eqv_trans _ (0 * eliminateLinks f rest) _
          (qmul_congr hz (Q'.eqv_refl _)) (Q'.zero_mul_eqv _)
      · exact Q'.eqv_trans _ (f head * 0) _
          (qmul_congr (Q'.eqv_refl _)
            (eliminateLinks_zero_of_mem_local f hrest hz))
          (Q'.mul_zero_eqv _)

theorem parametricKPhysicalFaceFactor_zero_of_rejected
    (w : Q') (K n : Nat) (physical : EdgeLabelling)
    (hrejected :
      labelWithinB K (physicalFaceEdges n) physical = false) :
    parametricKPhysicalFaceFactor w K n physical ≈ 0 := by
  obtain ⟨edge, hedge, hlarge⟩ := labelWithinB_false_exists K
    (physicalFaceEdges n) physical hrejected
  unfold parametricKPhysicalFaceFactor
  apply eliminateLinks_zero_of_mem_local _ hedge
  rw [coeffAt_of_gt (heatKernelPacket K w) hlarge]
  exact Q'.eqv_refl 0

theorem parametricKPhysicalTerm_zero_of_rejected
    (w : Q') (K n : Nat) (physical : EdgeLabelling)
    (hrejected :
      labelWithinB K (physicalFaceEdges n) physical = false) :
    parametricKPhysicalTerm w K n physical ≈ 0 := by
  unfold parametricKPhysicalTerm
  exact Q'.eqv_trans _
    (0 * explicitLinkMultiplicityProduct K n physical
      (enumerate (distinctBoxLinks n))) _
    (qmul_congr
      (parametricKPhysicalFaceFactor_zero_of_rejected
        w K n physical hrejected)
      (Q'.eqv_refl _))
    (Q'.zero_mul_eqv _)

private theorem listQSum_eq_filter_of_zero_local
    (f : EdgeLabelling → Q') (p : EdgeLabelling → Bool) :
    ∀ xs : List EdgeLabelling,
      (∀ x, x ∈ xs → p x = false → f x ≈ 0) →
      listQSum f xs ≈ listQSum f (xs.filter p)
  | [], _ => Q'.eqv_refl _
  | x :: xs, hz => by
      have htail : ∀ y, y ∈ xs → p y = false → f y ≈ 0 := by
        intro y hy hp
        exact hz y (List.mem_cons_of_mem x hy) hp
      cases hp : p x with
      | false =>
          simp only [List.filter, hp, listQSum]
          exact Q'.eqv_trans _ (0 + listQSum f (xs.filter p)) _
            (Q'.add_eqv_congr' (hz x List.mem_cons_self hp)
              (listQSum_eq_filter_of_zero_local f p xs htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter, hp, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local f p xs htail)

private theorem range_nodup_local (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

/-- The literal finite packet-graph Cartesian sum is exactly the common
coupling-parametric physical spin-foam partition at every cutoff. -/
theorem parametricFusionCompleteBoxVertexCartesianSum_eq_physicalPartition
    (w : Q') (K n : Nat) :
    parametricFusionCompleteBoxVertexCartesianSum w K n ≈
      parametricKPhysicalPartition w K n := by
  let term : EdgeLabelling → Q' := parametricKPhysicalTerm w K n
  refine Q'.eqv_trans _
    (listQSum term
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (physicalFaceEdges n))) _
    (parametricFusionCompleteBoxVertexCartesianSum_eq_linkSpinFoam
      w K n) ?_
  refine Q'.eqv_trans _
    (listQSum term
      ((boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (physicalFaceEdges n)).filter
          (labelWithinB K (physicalFaceEdges n)))) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero_local
    intro physical _ hrejected
    exact parametricKPhysicalTerm_zero_of_rejected
      w K n physical hrejected
  · unfold parametricKPhysicalPartition physicalFaceEdges
    rw [boundedEdgeLabellings_filter_cutoff
      (externalCutoff_le_linkAuxiliaryCutoff K)
      (List.range (plaquetteEdgeCount n))]
    · exact Q'.eqv_refl _
    · exact range_nodup_local _

/-! ## 5. Compatibility with both previously checked endpoints -/

theorem parametricFusionCompleteBoxVertexCartesianSum_coupling
    (K n : Nat) :
    parametricFusionCompleteBoxVertexCartesianSum coupling K n =
      fusionCompleteBoxVertexCartesianSum K n := by
  rfl

theorem parametricFusionCompleteBoxVertexCartesianSum_one
    (w : Q') (n : Nat) :
    parametricFusionCompleteBoxVertexCartesianSum w 1 n =
      parametricGaugeBoxVertexCartesianSum w n := by
  rfl

theorem anchorParametricFusionCompleteBoxVertexCartesianSum_one_eqv_graph
    (n : Nat) :
    parametricFusionCompleteBoxVertexCartesianSum anchorCoupling 1 n ≈
      parametricGaugeBoxVertexCartesianSum anchorCoupling n := by
  exact Q'.eqv_of_eq
    (parametricFusionCompleteBoxVertexCartesianSum_one anchorCoupling n)

end YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity.parametricFusionAuxiliaryBareAmplitude_eq_production
#print axioms YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity.parametricFusionCompleteBoxVertexCartesianSum_eq_conditional
#print axioms YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity.parametricFusionConditionalAuxiliarySum_eq_link_product
#print axioms YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity.parametricKPhysicalTerm_zero_of_rejected
#print axioms YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity.parametricFusionCompleteBoxVertexCartesianSum_eq_physicalPartition
#print axioms YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity.parametricFusionCompleteBoxVertexCartesianSum_coupling
#print axioms YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity.parametricFusionCompleteBoxVertexCartesianSum_one
