/-
# Coupling-parametric cutoff-one Z4 spin-foam identity

The original finite-box packet graph was specialized to coupling `1/2`.
This module repairs that interface at physical cutoff one.  It constructs the
actual fusion-complete packet graph at an arbitrary rational coupling `w`,
replays the constructive physical/auxiliary Fubini split, and leaves all
auxiliary fusion constraints unchanged.  The endpoint theorem identifies the
literal graph Cartesian sum with the localized cutoff-one spin-foam sum used
by `Z4StrongCouplingParametricAnchor`.

No positivity assumption on `w` is needed for the exact identity.  Positivity
and the concrete `w = 1/400` estimate enter only in the analytic anchor.
-/

import YMGap.Continuum.Z4StrongCouplingParametricAnchor

namespace YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
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
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. The actual parameterized packet graph -/

def parametricGaugeBoxPackets (w : Q') (n : Nat) :
    Nat → CharacterPacket (linkAuxiliaryCutoff 1) :=
  fun edge =>
    if edge < plaquetteEdgeCount n then
      padPacket (externalCutoff_le_linkAuxiliaryCutoff 1)
        (heatKernelPacket 1 w)
    else if edge ∈ vacuumBaseEdgeIds n then
      vacuumPacket (linkAuxiliaryCutoff 1)
    else
      allOnesPacket (linkAuxiliaryCutoff 1)

def parametricGaugeBoxState (w : Q') (n : Nat) :
    CompensatedGraphState (linkAuxiliaryCutoff 1) where
  edges := usedResolutionEdges n
  vertices := resolutionVertices n
  packet := parametricGaugeBoxPackets w n
  copiedEdges := []
  copied_mem := by intro edge h; cases h

def parametricGaugeBoxVertexIntegrand (w : Q') (n : Nat) : GraphPacket :=
  graphVertexProject (resolutionVertices n)
    (packetGraphBareAmplitude (usedResolutionEdges n)
      (parametricGaugeBoxPackets w n))

def parametricGaugeBoxVertexCartesianSum (w : Q') (n : Nat) : Q' :=
  listQSum
    (parametricGaugeBoxVertexIntegrand w n)
    (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
      (usedResolutionEdges n))

def parametricConditionalAuxiliarySum (w : Q') (n : Nat)
    (physical : EdgeLabelling) : Q' :=
  listQSum
    (fun auxiliary =>
      graphVertexProject (resolutionVertices n)
        (packetGraphBareAmplitude (usedAuxiliaryEdges n)
          (parametricGaugeBoxPackets w n))
        (overlayOn (physicalFaceEdges n) physical auxiliary))
    (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
      (usedAuxiliaryEdges n))

def parametricPhysicalPacketFactor (w : Q') (n : Nat)
    (physical : EdgeLabelling) : Q' :=
  packetGraphBareAmplitude (physicalFaceEdges n)
    (parametricGaugeBoxPackets w n) physical

theorem parametricPhysicalPacketFactor_eq_faceFactor
    (w : Q') (n : Nat) (physical : EdgeLabelling) :
    parametricPhysicalPacketFactor w n physical =
      parametricPhysicalFaceFactor w n physical := by
  unfold parametricPhysicalPacketFactor parametricPhysicalFaceFactor
    packetGraphBareAmplitude physicalFaceEdges
  apply eliminateLinks_congr_eq
  intro edge hedge
  have hedgeLt : edge < plaquetteEdgeCount n := List.mem_range.mp hedge
  unfold parametricGaugeBoxPackets
  rw [if_pos hedgeLt, coeffAt_padPacket]

theorem parametricPhysicalPacketFactor_overlay
    (w : Q') (n : Nat) (physical auxiliary : EdgeLabelling) :
    packetGraphBareAmplitude (physicalFaceEdges n)
        (parametricGaugeBoxPackets w n)
        (overlayOn (physicalFaceEdges n) physical auxiliary) =
      parametricPhysicalPacketFactor w n physical := by
  unfold parametricPhysicalPacketFactor
  apply packetGraphBareAmplitude_label_eq_on
  intro edge hedge
  exact overlayOn_apply_of_mem hedge

/-! ## 2. Exact physical/auxiliary Fubini factorization -/

theorem parametricGaugeBoxVertexIntegrand_overlay_factor
    (w : Q') (n : Nat) (physical auxiliary : EdgeLabelling) :
    parametricGaugeBoxVertexIntegrand w n
        (overlayOn (physicalFaceEdges n) physical auxiliary) ≈
      parametricPhysicalPacketFactor w n physical *
        graphVertexProject (resolutionVertices n)
          (packetGraphBareAmplitude (usedAuxiliaryEdges n)
            (parametricGaugeBoxPackets w n))
          (overlayOn (physicalFaceEdges n) physical auxiliary) := by
  let label := overlayOn (physicalFaceEdges n) physical auxiliary
  let packet := parametricGaugeBoxPackets w n
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
        parametricPhysicalPacketFactor w n physical := by
    dsimp [packet, label]
    exact parametricPhysicalPacketFactor_overlay w n physical auxiliary
  by_cases hadmissible :
      verticesAdmissibleB (resolutionVertices n) label = true
  · unfold parametricGaugeBoxVertexIntegrand graphVertexProject
    dsimp only [label] at hadmissible ⊢
    rw [if_pos hadmissible, if_pos hadmissible]
    dsimp only [packet] at hsplit hphysical ⊢
    rw [hphysical] at hsplit
    exact hsplit
  · unfold parametricGaugeBoxVertexIntegrand graphVertexProject
    dsimp only [label] at hadmissible ⊢
    rw [if_neg hadmissible, if_neg hadmissible]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)

theorem parametricConditionalInnerSum_factor
    (w : Q') (n : Nat) (physical : EdgeLabelling) :
    listQSum
        (fun auxiliary =>
          parametricGaugeBoxVertexIntegrand w n
            (overlayOn (physicalFaceEdges n) physical auxiliary))
        (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
          (usedAuxiliaryEdges n)) ≈
      parametricPhysicalPacketFactor w n physical *
        parametricConditionalAuxiliarySum w n physical := by
  refine Q'.eqv_trans _
    (listQSum
      (fun auxiliary =>
        parametricPhysicalPacketFactor w n physical *
          graphVertexProject (resolutionVertices n)
            (packetGraphBareAmplitude (usedAuxiliaryEdges n)
              (parametricGaugeBoxPackets w n))
            (overlayOn (physicalFaceEdges n) physical auxiliary))
      (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
        (usedAuxiliaryEdges n))) _ ?_ ?_
  · apply listQSum_congr
    intro auxiliary
    exact parametricGaugeBoxVertexIntegrand_overlay_factor
      w n physical auxiliary
  · unfold parametricConditionalAuxiliarySum
    exact listQSum_const_mul (parametricPhysicalPacketFactor w n physical)
      (fun auxiliary =>
        graphVertexProject (resolutionVertices n)
          (packetGraphBareAmplitude (usedAuxiliaryEdges n)
            (parametricGaugeBoxPackets w n))
          (overlayOn (physicalFaceEdges n) physical auxiliary))
      (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
        (usedAuxiliaryEdges n))

theorem parametricGaugeBoxVertexCartesianSum_eq_conditional
    (w : Q') (n : Nat) :
    parametricGaugeBoxVertexCartesianSum w n ≈
      listQSum
        (fun physical =>
          parametricPhysicalPacketFactor w n physical *
            parametricConditionalAuxiliarySum w n physical)
        (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
          (physicalFaceEdges n)) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        listQSum
          (fun auxiliary =>
            parametricGaugeBoxVertexIntegrand w n
              (overlayOn (physicalFaceEdges n) physical auxiliary))
          (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
            (usedAuxiliaryEdges n)))
      (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
        (physicalFaceEdges n))) _ ?_ ?_
  · unfold parametricGaugeBoxVertexCartesianSum physicalFaceEdges
    simpa only [usedResolutionEdges] using
      (listQSum_bounded_append_fubini (linkAuxiliaryCutoff 1)
        (List.range (plaquetteEdgeCount n)) (usedAuxiliaryEdges n)
        (parametricGaugeBoxVertexIntegrand w n))
  · apply listQSum_congr
    intro physical
    exact parametricConditionalInnerSum_factor w n physical

/-! ## 3. The auxiliary sum is the same exact fusion multiplicity -/

theorem parametricAuxiliaryEdgeCoefficient_eq_indicator
    {w : Q'} {n edge : Nat} {label : EdgeLabelling}
    (hge : plaquetteEdgeCount n ≤ edge)
    (hbound : label edge < linkAuxiliaryCutoff 1 + 1) :
    coeffAt (parametricGaugeBoxPackets w n edge) (label edge) =
      if auxiliaryEdgeAllowedB n label edge then 1 else 0 := by
  have hnotPhysical : ¬ edge < plaquetteEdgeCount n := by omega
  unfold parametricGaugeBoxPackets
  rw [if_neg hnotPhysical]
  by_cases hvacuum : edge ∈ vacuumBaseEdgeIds n
  · rw [if_pos hvacuum, coeffAt_vacuumPacket]
    unfold auxiliaryEdgeAllowedB
    rw [if_pos hvacuum]
    by_cases hzero : label edge = 0 <;> simp [hzero]
  · rw [if_neg hvacuum, coeffAt_allOnesPacket hbound]
    unfold auxiliaryEdgeAllowedB
    rw [if_neg hvacuum]
    rfl

theorem parametricAuxiliaryPacketBareAmplitude_eq_indicator
    (w : Q') (n : Nat) (label : EdgeLabelling)
    (hbound : ∀ edge, edge ∈ usedAuxiliaryEdges n →
      label edge < linkAuxiliaryCutoff 1 + 1) :
    packetGraphBareAmplitude (usedAuxiliaryEdges n)
        (parametricGaugeBoxPackets w n) label ≈
      if auxiliaryPacketAllowedB n label then 1 else 0 := by
  unfold packetGraphBareAmplitude auxiliaryPacketAllowedB
  refine Q'.eqv_trans _
    (eliminateLinks
      (fun edge => if auxiliaryEdgeAllowedB n label edge
        then (1 : Q') else 0)
      (usedAuxiliaryEdges n)) _ ?_
    (eliminateLinks_indicator_eq_all
      (auxiliaryEdgeAllowedB n label) (usedAuxiliaryEdges n))
  exact Q'.eqv_of_eq
    (eliminateLinks_congr_eq
      (fun edge => coeffAt
        (parametricGaugeBoxPackets w n edge) (label edge))
      (fun edge => if auxiliaryEdgeAllowedB n label edge
        then (1 : Q') else 0)
      (usedAuxiliaryEdges n)
      (fun edge hedge =>
        parametricAuxiliaryEdgeCoefficient_eq_indicator
          (usedAuxiliaryEdge_ge_count hedge) (hbound edge hedge)))

theorem parametricConditionalAuxiliaryIntegrand_eq_indicator
    {w : Q'} {n : Nat} (physical auxiliary : EdgeLabelling)
    (hauxiliary : auxiliary ∈
      boundedEdgeLabellings (linkAuxiliaryCutoff 1)
        (usedAuxiliaryEdges n)) :
    graphVertexProject (resolutionVertices n)
        (packetGraphBareAmplitude (usedAuxiliaryEdges n)
          (parametricGaugeBoxPackets w n))
        (overlayOn (physicalFaceEdges n) physical auxiliary) ≈
      conditionalAuxiliaryMultiplicityTerm n physical auxiliary := by
  let label := overlayOn (physicalFaceEdges n) physical auxiliary
  have hsound := boundedEdgeLabellings_sound
    (linkAuxiliaryCutoff 1) (usedAuxiliaryEdges n)
    auxiliary hauxiliary
  have hbound : ∀ edge, edge ∈ usedAuxiliaryEdges n →
      label edge < linkAuxiliaryCutoff 1 + 1 := by
    intro edge hedge
    have hover : label edge = auxiliary edge := by
      dsimp [label]
      apply overlayOn_apply_of_not_mem
      unfold physicalFaceEdges
      exact usedAuxiliaryEdge_not_physical hedge
    rw [hover]
    exact hsound.1 edge hedge
  have hpacket := parametricAuxiliaryPacketBareAmplitude_eq_indicator
    w n label hbound
  by_cases hvertices :
      verticesAdmissibleB (resolutionVertices n) label = true
  · unfold graphVertexProject conditionalAuxiliaryMultiplicityTerm
      conditionalAuxiliaryAllowedB
    dsimp [label, physicalFaceEdges] at hvertices hpacket ⊢
    rw [if_pos hvertices]
    simp only [hvertices, Bool.true_and]
    exact hpacket
  · unfold graphVertexProject conditionalAuxiliaryMultiplicityTerm
      conditionalAuxiliaryAllowedB
    dsimp [label, physicalFaceEdges] at hvertices ⊢
    rw [if_neg hvertices]
    simp [hvertices]
    exact Q'.eqv_refl 0

theorem parametricConditionalAuxiliarySum_eq_multiplicity
    (w : Q') (n : Nat) (physical : EdgeLabelling) :
    parametricConditionalAuxiliarySum w n physical ≈
      conditionalAuxiliaryMultiplicity 1 n physical := by
  unfold parametricConditionalAuxiliarySum
    conditionalAuxiliaryMultiplicity
  apply listQSum_congr_on
  intro auxiliary hauxiliary
  exact parametricConditionalAuxiliaryIntegrand_eq_indicator
    physical auxiliary hauxiliary

theorem parametricConditionalAuxiliarySum_eq_link_product
    (w : Q') (n : Nat) (physical : EdgeLabelling) :
    parametricConditionalAuxiliarySum w n physical ≈
      linkAuxiliaryMultiplicityProduct 1 n physical
        (enumerate (distinctBoxLinks n)) :=
  Q'.eqv_trans _ _ _
    (parametricConditionalAuxiliarySum_eq_multiplicity w n physical)
    (conditionalAuxiliaryMultiplicity_eq_link_product 1 n physical)

theorem parametricGaugeBoxVertexCartesianSum_eq_linkSpinFoam
    (w : Q') (n : Nat) :
    parametricGaugeBoxVertexCartesianSum w n ≈
      listQSum
        (fun physical =>
          parametricPhysicalFaceFactor w n physical *
            explicitLinkMultiplicityProduct 1 n physical
              (enumerate (distinctBoxLinks n)))
        (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
          (physicalFaceEdges n)) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        parametricPhysicalPacketFactor w n physical *
          parametricConditionalAuxiliarySum w n physical)
      (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
        (physicalFaceEdges n))) _
    (parametricGaugeBoxVertexCartesianSum_eq_conditional w n) ?_
  apply listQSum_congr
  intro physical
  exact qmul_congr
    (Q'.eqv_of_eq
      (parametricPhysicalPacketFactor_eq_faceFactor w n physical))
    (Q'.eqv_trans _
      (linkAuxiliaryMultiplicityProduct 1 n physical
        (enumerate (distinctBoxLinks n))) _
      (parametricConditionalAuxiliarySum_eq_link_product w n physical)
      (enumeratedLinkMultiplicityProduct_eq_explicit 1 n physical))

/-! ## 4. Exact reduction to the physical binary face support -/

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

theorem parametricPhysicalFaceFactor_zero_of_rejected
    (w : Q') (n : Nat) (physical : EdgeLabelling)
    (hrejected : labelWithinB 1 (physicalFaceEdges n) physical = false) :
    parametricPhysicalFaceFactor w n physical ≈ 0 := by
  obtain ⟨edge, hedge, hlarge⟩ := labelWithinB_false_exists 1
    (physicalFaceEdges n) physical hrejected
  unfold parametricPhysicalFaceFactor
  apply eliminateLinks_zero_of_mem_local _ hedge
  rw [coeffAt_of_gt (heatKernelPacket 1 w) hlarge]
  exact Q'.eqv_refl 0

theorem parametricSpinFoamSummand_zero_of_rejected
    (w : Q') (n : Nat) (physical : EdgeLabelling)
    (hrejected : labelWithinB 1 (physicalFaceEdges n) physical = false) :
    parametricPhysicalFaceFactor w n physical *
        explicitLinkMultiplicityProduct 1 n physical
          (enumerate (distinctBoxLinks n)) ≈ 0 := by
  exact Q'.eqv_trans _
    (0 * explicitLinkMultiplicityProduct 1 n physical
      (enumerate (distinctBoxLinks n))) _
    (qmul_congr
      (parametricPhysicalFaceFactor_zero_of_rejected
        w n physical hrejected)
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

theorem parametricGaugeBoxVertexCartesianSum_eq_physicalCutoffSpinFoam
    (w : Q') (n : Nat) :
    parametricGaugeBoxVertexCartesianSum w n ≈
      listQSum
        (fun physical =>
          parametricPhysicalFaceFactor w n physical *
            explicitLinkMultiplicityProduct 1 n physical
              (enumerate (distinctBoxLinks n)))
        (explicitPhysicalLabellings 1 n) := by
  let term : EdgeLabelling → Q' := fun physical =>
    parametricPhysicalFaceFactor w n physical *
      explicitLinkMultiplicityProduct 1 n physical
        (enumerate (distinctBoxLinks n))
  refine Q'.eqv_trans _
    (listQSum term
      (boundedEdgeLabellings (linkAuxiliaryCutoff 1)
        (physicalFaceEdges n))) _
    (parametricGaugeBoxVertexCartesianSum_eq_linkSpinFoam w n) ?_
  refine Q'.eqv_trans _
    (listQSum term
      ((boundedEdgeLabellings (linkAuxiliaryCutoff 1)
        (physicalFaceEdges n)).filter
          (labelWithinB 1 (physicalFaceEdges n)))) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero_local
    intro physical _ hrejected
    exact parametricSpinFoamSummand_zero_of_rejected
      w n physical hrejected
  · unfold explicitPhysicalLabellings
    rw [boundedEdgeLabellings_filter_cutoff
      (externalCutoff_le_linkAuxiliaryCutoff 1)
      (physicalFaceEdges n)]
    · exact Q'.eqv_refl _
    · unfold physicalFaceEdges
      exact range_nodup_local _

/-! ## 5. Exact localization and attachment of the analytic anchor -/

theorem parametricSpinFoamWeight_eq_localized
    (w : Q') (n : Nat) (physical : EdgeLabelling) :
    parametricPhysicalFaceFactor w n physical *
        explicitLinkMultiplicityProduct 1 n physical
          (enumerate (distinctBoxLinks n)) ≈
      parametricLocalizedSpinFoamWeight w n physical := by
  unfold parametricLocalizedSpinFoamWeight
  exact qmul_congr (Q'.eqv_refl _)
    (explicitLinkMultiplicityProduct_eq_touched 1 n physical _)

theorem parametricGaugeBoxVertexCartesianSum_eq_localizedSpinFoam
    (w : Q') (n : Nat) :
    parametricGaugeBoxVertexCartesianSum w n ≈
      listQSum (parametricLocalizedSpinFoamWeight w n)
        (explicitPhysicalLabellings 1 n) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        parametricPhysicalFaceFactor w n physical *
          explicitLinkMultiplicityProduct 1 n physical
            (enumerate (distinctBoxLinks n)))
      (explicitPhysicalLabellings 1 n)) _
    (parametricGaugeBoxVertexCartesianSum_eq_physicalCutoffSpinFoam w n) ?_
  apply listQSum_congr
  intro physical
  exact parametricSpinFoamWeight_eq_localized w n physical

theorem anchorGaugeBoxSummand_le_envelopePow
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n) :
    parametricLocalizedSpinFoamWeight anchorCoupling n physical ≤
      anchorPerFaceEnvelope ^
        (excitedPlaquetteEntries n physical).length :=
  parametricLocalizedSpinFoamWeight_anchor_le_envelopePow hphysical

/-! ## 6. Exact vacuum separation for the parameterized graph -/

def parametricLocalizedSpinFoamPartition (w : Q') (n : Nat) : Q' :=
  listQSum (parametricLocalizedSpinFoamWeight w n)
    (explicitPhysicalLabellings 1 n)

def parametricExcitedLocalizedSpinFoamSum (w : Q') (n : Nat) : Q' :=
  listQSum (parametricLocalizedSpinFoamWeight w n)
    (explicitExcitedPhysicalLabellings 1 n)

private theorem eliminateLinks_eqv_one_local (value : Nat → Q') :
    ∀ edges : List Nat, (∀ edge, edge ∈ edges → value edge ≈ 1) →
      eliminateLinks value edges ≈ 1
  | [], _ => Q'.eqv_refl 1
  | edge :: rest, hvalue => by
      have hhead := hvalue edge List.mem_cons_self
      have hrest := eliminateLinks_eqv_one_local value rest
        (fun item hitem => hvalue item (List.mem_cons_of_mem edge hitem))
      exact Q'.eqv_trans _ (1 * 1) _
        (qmul_congr hhead hrest) (Q'.one_mul_eqv 1)

theorem parametricPhysicalFaceFactor_zero_eqv_one
    (w : Q') (n : Nat) :
    parametricPhysicalFaceFactor w n zeroEdgeLabelling ≈ 1 := by
  unfold parametricPhysicalFaceFactor
  apply eliminateLinks_eqv_one_local
  intro edge _
  change coeffAt (heatKernelPacket 1 w) 0 ≈ 1
  rw [coeffAt_heatKernelPacket (by decide), coeffW_zero]
  exact Q'.eqv_refl 1

theorem parametricLocalizedSpinFoamWeight_zero_eqv_one
    (w : Q') (n : Nat) :
    parametricLocalizedSpinFoamWeight w n zeroEdgeLabelling ≈ 1 := by
  have hlocalize :=
    parametricSpinFoamWeight_eq_localized w n zeroEdgeLabelling
  refine Q'.eqv_trans _
    (parametricPhysicalFaceFactor w n zeroEdgeLabelling *
      explicitLinkMultiplicityProduct 1 n zeroEdgeLabelling
        (enumerate (distinctBoxLinks n))) _
    (Q'.eqv_symm hlocalize) ?_
  exact Q'.eqv_trans _ (1 * 1) _
    (qmul_congr
      (parametricPhysicalFaceFactor_zero_eqv_one w n)
      (explicitLinkMultiplicityProduct_zero_eqv_one 1 n _))
    (Q'.one_mul_eqv 1)

private theorem listQSum_add_local {A : Type} (f g : A → Q') :
    ∀ xs : List A,
      listQSum (fun x => f x + g x) xs ≈
        listQSum f xs + listQSum g xs
  | [] => Q'.eqv_symm (q_zero_add_eqv 0)
  | x :: xs => by
      change (f x + g x) + listQSum (fun y => f y + g y) xs ≈
        (f x + listQSum f xs) + (g x + listQSum g xs)
      refine Q'.eqv_trans _
        ((f x + g x) + (listQSum f xs + listQSum g xs)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_add_local f g xs)) ?_
      refine Q'.eqv_trans _
        (f x + (g x + (listQSum f xs + listQSum g xs))) _
        (Q'.add_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _
        (f x + ((g x + listQSum f xs) + listQSum g xs)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))) ?_
      refine Q'.eqv_trans _
        (f x + ((listQSum f xs + g x) + listQSum g xs)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.add_eqv_congr' (Q'.add_comm_eqv _ _)
            (Q'.eqv_refl _))) ?_
      exact Q'.eqv_trans _
        (f x + (listQSum f xs + (g x + listQSum g xs))) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.add_assoc_eqv _ _ _))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem listQSum_congr_mem_local {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | x :: xs, h =>
      Q'.add_eqv_congr' (h x List.mem_cons_self)
        (listQSum_congr_mem_local xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem zeroSlice_sum_local (edges : List Nat)
    (hnodup : edges.Nodup) (vacuum : Q') :
    listQSum
        (fun label => if labelWithinB 0 edges label then vacuum else 0)
        (boundedEdgeLabellings 1 edges) ≈ vacuum := by
  have hfilter := boundedEdgeLabellings_filter_cutoff
    (K := 0) (L := 1) (Nat.zero_le 1) edges hnodup
  have hsum := listQSum_filter (fun _ : EdgeLabelling => vacuum)
    (labelWithinB 0 edges) (boundedEdgeLabellings 1 edges)
  refine Q'.eqv_trans _
    (listQSum (fun _ : EdgeLabelling => vacuum)
      ((boundedEdgeLabellings 1 edges).filter (labelWithinB 0 edges))) _
    (Q'.eqv_symm hsum) ?_
  rw [hfilter, boundedEdgeLabellings_zero]
  exact Q'.eqv_of_eq (Q'.add_zero' vacuum)

private theorem parametricWeight_eq_excited_add_zeroSlice
    {w : Q'} {n : Nat} {physical : EdgeLabelling}
    (hmem : physical ∈ explicitPhysicalLabellings 1 n) :
    parametricLocalizedSpinFoamWeight w n physical ≈
      (if hasExcitedB physical (physicalFaceEdges n) then
          parametricLocalizedSpinFoamWeight w n physical else 0) +
        (if labelWithinB 0 (physicalFaceEdges n) physical then
          parametricLocalizedSpinFoamWeight w n zeroEdgeLabelling else 0) := by
  have hzeroIff := enumerated_labelWithinB_zero_iff
    (K := 1) (edges := physicalFaceEdges n) hmem
  by_cases hexcited : hasExcitedB physical (physicalFaceEdges n) = true
  · have hnotzero : physical ≠ zeroEdgeLabelling := by
      intro hlabel
      subst physical
      have hzfalse : hasExcitedB zeroEdgeLabelling
          (physicalFaceEdges n) = false :=
        (hasExcitedB_false_iff_zero_on zeroEdgeLabelling
          (physicalFaceEdges n)).2 (fun _ _ => rfl)
      rw [hzfalse] at hexcited
      cases hexcited
    have hwithin : labelWithinB 0 (physicalFaceEdges n) physical = false := by
      cases h : labelWithinB 0 (physicalFaceEdges n) physical with
      | false => rfl
      | true => exact False.elim (hnotzero (hzeroIff.mp h))
    rw [hexcited, hwithin]
    exact Q'.eqv_symm (q_add_zero_eqv _)
  · have hexcitedFalse : hasExcitedB physical
        (physicalFaceEdges n) = false := by
      cases h : hasExcitedB physical (physicalFaceEdges n) with
      | false => rfl
      | true => exact False.elim (hexcited h)
    have hzeroOn :=
      (hasExcitedB_false_iff_zero_on physical (physicalFaceEdges n)).1
        hexcitedFalse
    have hsound := boundedEdgeLabellings_sound 1
      (physicalFaceEdges n) physical hmem
    have hlabel : physical = zeroEdgeLabelling := by
      funext edge
      by_cases hedge : edge ∈ physicalFaceEdges n
      · change physical edge = zeroEdgeLabelling edge
        simpa only [zeroEdgeLabelling] using hzeroOn edge hedge
      · change physical edge = zeroEdgeLabelling edge
        simpa only [zeroEdgeLabelling] using hsound.2 edge hedge
    have hwithin : labelWithinB 0 (physicalFaceEdges n) physical = true :=
      hzeroIff.mpr hlabel
    rw [hexcitedFalse, hwithin, hlabel]
    exact Q'.eqv_symm (q_zero_add_eqv _)

theorem parametricLocalizedSpinFoamPartition_eq_one_add_excited
    (w : Q') (n : Nat) :
    parametricLocalizedSpinFoamPartition w n ≈
      1 + parametricExcitedLocalizedSpinFoamSum w n := by
  let support := explicitPhysicalLabellings 1 n
  let excitedTerm : EdgeLabelling → Q' := fun physical =>
    if hasExcitedB physical (physicalFaceEdges n) then
      parametricLocalizedSpinFoamWeight w n physical else 0
  let zeroSlice : EdgeLabelling → Q' := fun physical =>
    if labelWithinB 0 (physicalFaceEdges n) physical then
      parametricLocalizedSpinFoamWeight w n zeroEdgeLabelling else 0
  have hpoint :
      listQSum (parametricLocalizedSpinFoamWeight w n) support ≈
        listQSum
          (fun physical => excitedTerm physical + zeroSlice physical)
          support :=
    listQSum_congr_mem_local support
      (fun physical hphysical =>
        parametricWeight_eq_excited_add_zeroSlice hphysical)
  refine Q'.eqv_trans _ _ _ hpoint ?_
  refine Q'.eqv_trans _
    (listQSum excitedTerm support + listQSum zeroSlice support) _
    (listQSum_add_local excitedTerm zeroSlice support) ?_
  have hexcited : listQSum excitedTerm support ≈
      parametricExcitedLocalizedSpinFoamSum w n := by
    exact Q'.eqv_symm
      (listQSum_filter (parametricLocalizedSpinFoamWeight w n)
        (fun physical => hasExcitedB physical (physicalFaceEdges n))
        support)
  have hzero : listQSum zeroSlice support ≈
      parametricLocalizedSpinFoamWeight w n zeroEdgeLabelling := by
    exact zeroSlice_sum_local (physicalFaceEdges n)
      (by unfold physicalFaceEdges; exact range_nodup_local _)
      (parametricLocalizedSpinFoamWeight w n zeroEdgeLabelling)
  exact Q'.eqv_trans _
    (parametricExcitedLocalizedSpinFoamSum w n +
      parametricLocalizedSpinFoamWeight w n zeroEdgeLabelling) _
    (Q'.add_eqv_congr' hexcited hzero)
    (Q'.eqv_trans _
      (parametricLocalizedSpinFoamWeight w n zeroEdgeLabelling +
        parametricExcitedLocalizedSpinFoamSum w n) _
      (Q'.add_comm_eqv _ _)
      (Q'.add_eqv_congr'
        (parametricLocalizedSpinFoamWeight_zero_eqv_one w n)
        (Q'.eqv_refl _)))

theorem parametricGaugeBoxVertexCartesianSum_eq_one_add_excited
    (w : Q') (n : Nat) :
    parametricGaugeBoxVertexCartesianSum w n ≈
      1 + parametricExcitedLocalizedSpinFoamSum w n :=
  Q'.eqv_trans _ _ _
    (parametricGaugeBoxVertexCartesianSum_eq_localizedSpinFoam w n)
    (parametricLocalizedSpinFoamPartition_eq_one_add_excited w n)

private theorem parametricCoefficient_nonnegative_local
    {w : Q'} (hw : (0 : Q') ≤ w) (spin : Nat) :
    (0 : Q') ≤ coeffAt (heatKernelPacket 1 w) spin := by
  by_cases hspin : spin < 2
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg hw spin
  · have hlarge : 1 < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket 1 w) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative_local (value : Nat → Q')
    (hvalue : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat, (0 : Q') ≤ eliminateLinks value edges
  | [] => Q'.zero_le_one
  | edge :: rest => Q'.mul_nonneg _ _ (hvalue edge)
      (eliminateLinks_nonnegative_local value hvalue rest)

theorem parametricLocalizedSpinFoamWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (n : Nat)
    (physical : EdgeLabelling) :
    (0 : Q') ≤ parametricLocalizedSpinFoamWeight w n physical := by
  unfold parametricLocalizedSpinFoamWeight parametricPhysicalFaceFactor
  exact Q'.mul_nonneg _ _
    (eliminateLinks_nonnegative_local _
      (fun edge => parametricCoefficient_nonnegative_local hw
        (physical edge)) _)
    (explicitLinkMultiplicityProduct_nonnegative 1 n physical _)

private theorem listQSum_nonnegative_local {A : Type} (value : A → Q')
    (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ xs : List A, (0 : Q') ≤ listQSum value xs
  | [] => Q'.le_refl' 0
  | x :: rest => Q'.zero_le_add _ _ (hvalue x)
      (listQSum_nonnegative_local value hvalue rest)

theorem parametricExcitedLocalizedSpinFoamSum_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (n : Nat) :
    (0 : Q') ≤ parametricExcitedLocalizedSpinFoamSum w n := by
  unfold parametricExcitedLocalizedSpinFoamSum
  exact listQSum_nonnegative_local _
    (parametricLocalizedSpinFoamWeight_nonnegative hw n) _

theorem one_le_anchorGaugeBoxVertexCartesianSum (n : Nat) :
    (1 : Q') ≤
      parametricGaugeBoxVertexCartesianSum anchorCoupling n := by
  have hadd : (1 : Q') ≤
      1 + parametricExcitedLocalizedSpinFoamSum anchorCoupling n :=
    Q'.add_le_self_of_nonneg _ _
      (parametricExcitedLocalizedSpinFoamSum_nonnegative (by decide) n)
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv
      (parametricGaugeBoxVertexCartesianSum_eq_one_add_excited
        anchorCoupling n))

end YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricPhysicalPacketFactor_eq_faceFactor
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricGaugeBoxVertexIntegrand_overlay_factor
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricGaugeBoxVertexCartesianSum_eq_conditional
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricAuxiliaryPacketBareAmplitude_eq_indicator
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricConditionalAuxiliarySum_eq_multiplicity
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricGaugeBoxVertexCartesianSum_eq_linkSpinFoam
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricGaugeBoxVertexCartesianSum_eq_physicalCutoffSpinFoam
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricGaugeBoxVertexCartesianSum_eq_localizedSpinFoam
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.anchorGaugeBoxSummand_le_envelopePow
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricLocalizedSpinFoamWeight_zero_eqv_one
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricGaugeBoxVertexCartesianSum_eq_one_add_excited
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.parametricExcitedLocalizedSpinFoamSum_nonnegative
#print axioms YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity.one_le_anchorGaugeBoxVertexCartesianSum
