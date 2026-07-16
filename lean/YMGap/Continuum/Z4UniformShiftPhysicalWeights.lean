/-
# Exact spin-foam weights under uniform four-coordinate transport

This module proves that the uniformly padded physical-labelling map constructed in
`Z4UniformShiftPhysicalTransport` preserves the complete arbitrary-cutoff
finite spin-foam summand.  The proof reindexes face factors by translated
plaquettes and local link multiplicities by translated links; target cells
outside the translated subbox carry the vacuum spin and contribute one.
-/

import YMGap.Continuum.Z4FusionMultiplicityPermutationLift
import YMGap.Continuum.Z4UniformShiftPhysicalTransport

namespace YMGap.Continuum.Z4UniformShiftPhysicalWeights

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open scoped List
open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinDependentIncidenceProductBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The translated plaquette sublist as an unordered finite set -/

theorem uniformShiftedPlaquetteList_subset_target
    {padding base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ uniformShiftedPlaquetteList padding base) :
    plaquette ∈ boxPlaquettes (uniformPaddedBase padding base) := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  exact uniformShiftPlaquette_mem_padded_box hsource

def inheritedUniformShiftedPlaquettes (padding base : Nat) : List Z4Plaq :=
  (boxPlaquettes (uniformPaddedBase padding base)).filter
    (fun plaquette =>
      decide (plaquette ∈ uniformShiftedPlaquetteList padding base))

theorem inheritedUniformShiftedPlaquettes_sublist (padding base : Nat) :
    inheritedUniformShiftedPlaquettes padding base <+
      boxPlaquettes (uniformPaddedBase padding base) :=
  List.filter_sublist

theorem inheritedUniformShiftedPlaquettes_nodup (padding base : Nat) :
    (inheritedUniformShiftedPlaquettes padding base).Nodup :=
  List.filter_sublist.nodup (boxPlaquettes_nodup (uniformPaddedBase padding base))

theorem uniformShiftedPlaquetteList_perm_inherited
    (padding base : Nat) :
    (uniformShiftedPlaquetteList padding base).Perm
      (inheritedUniformShiftedPlaquettes padding base) := by
  apply perm_of_nodup_mem_iff_constructive
    (uniformShiftedPlaquetteList padding base)
    (inheritedUniformShiftedPlaquettes padding base)
    (uniformShiftedPlaquetteList_nodup padding base)
    (inheritedUniformShiftedPlaquettes_nodup padding base)
  intro plaquette
  unfold inheritedUniformShiftedPlaquettes
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hmem
    exact ⟨uniformShiftedPlaquetteList_subset_target hmem, hmem⟩
  · exact fun hmem => hmem.2

/-! ## 2. Exact face-factor invariance -/

theorem geometricFaceFactor_uniformShiftTransport
    (w : Q') (K padding base : Nat) (physical : EdgeLabelling) :
    geometricFaceFactor w K
        (geometricSpinOfPhysical (uniformPaddedBase padding base)
          (uniformShiftTransportPhysical padding base physical))
        (boxPlaquettes (uniformPaddedBase padding base)) ≈
      geometricFaceFactor w K
        (geometricSpinOfPhysical base physical)
        (boxPlaquettes base) := by
  let targetValue : Z4Plaq → Q' := fun plaquette =>
    coeffAt (heatKernelPacket K w)
      (geometricSpinOfPhysical (uniformPaddedBase padding base)
        (uniformShiftTransportPhysical padding base physical) plaquette)
  let sourceValue : Z4Plaq → Q' := fun plaquette =>
    coeffAt (heatKernelPacket K w)
      (geometricSpinOfPhysical base physical plaquette)
  have hvacuum : ∀ plaquette,
      plaquette ∈ boxPlaquettes (uniformPaddedBase padding base) →
      plaquette ∉ inheritedUniformShiftedPlaquettes padding base →
      targetValue plaquette ≈ 1 := by
    intro plaquette htarget hnot
    have hnotShifted :
        plaquette ∉ uniformShiftedPlaquetteList padding base := by
      intro hshifted
      apply hnot
      unfold inheritedUniformShiftedPlaquettes
      exact List.mem_filter.mpr
        ⟨htarget, by simpa only [decide_eq_true_eq]⟩
    unfold targetValue
    rw [geometricSpinOfUniformShiftTransport_eq_of_mem_box htarget,
      uniformShiftedGeometricSpin_zero_of_not_mem
        padding base physical hnotShifted,
      coeffAt_heatKernelPacket (show 0 < K + 1 by omega),
      coeffW_zero]
    exact Q'.eqv_refl 1
  have hremove :
      listQProduct targetValue (boxPlaquettes (uniformPaddedBase padding base)) ≈
        listQProduct targetValue
          (inheritedUniformShiftedPlaquettes padding base) := by
    exact listQProduct_sublist_vacuum targetValue
      (inheritedUniformShiftedPlaquettes_sublist padding base)
      (boxPlaquettes_nodup (uniformPaddedBase padding base)) hvacuum
  have hperm :
      listQProduct targetValue
          (inheritedUniformShiftedPlaquettes padding base) ≈
        listQProduct targetValue
          (uniformShiftedPlaquetteList padding base) :=
    listQProduct_perm targetValue
      (uniformShiftedPlaquetteList_perm_inherited padding base).symm
  have hmap :
      listQProduct targetValue
          (uniformShiftedPlaquetteList padding base) =
        listQProduct
          (fun plaquette =>
            targetValue (uniformShiftPlaquette padding plaquette))
          (boxPlaquettes base) := by
    unfold uniformShiftedPlaquetteList
    exact listQProduct_map targetValue (uniformShiftPlaquette padding)
      (boxPlaquettes base)
  have hagree : ∀ plaquette, plaquette ∈ boxPlaquettes base →
      targetValue (uniformShiftPlaquette padding plaquette) =
        sourceValue plaquette := by
    intro plaquette hplaquette
    unfold targetValue sourceValue
    rw [geometricSpinOfUniformShiftTransport_eq_of_mem_box
          (uniformShiftPlaquette_mem_padded_box hplaquette),
      uniformShiftedGeometricSpin_recover]
  have hsource :
      listQProduct
          (fun plaquette =>
            targetValue (uniformShiftPlaquette padding plaquette))
          (boxPlaquettes base) =
        listQProduct sourceValue (boxPlaquettes base) :=
    listQProduct_congr _ _ _ hagree
  unfold geometricFaceFactor
  exact Q'.eqv_trans _ _ _ hremove
    (Q'.eqv_trans _ _ _ hperm
      (Q'.eqv_of_eq (hmap.trans hsource)))

theorem parametricKPhysicalFaceFactor_uniformShift
    (w : Q') (K padding base : Nat) (physical : EdgeLabelling) :
    parametricKPhysicalFaceFactor w K (uniformPaddedBase padding base)
        (uniformShiftTransportPhysical padding base physical) ≈
      parametricKPhysicalFaceFactor w K base physical := by
  rw [parametricKPhysicalFaceFactor_eq_geometric,
    parametricKPhysicalFaceFactor_eq_geometric]
  exact geometricFaceFactor_uniformShiftTransport
    w K padding base physical

/-! ## 3. Translated links and incident-spin lists -/

theorem uniformShiftLink_injective (padding : Nat) :
    Function.Injective (uniformShiftLink padding) := by
  intro left right heq
  apply Prod.ext
  · apply uniformShiftVertex_injective padding
    simpa only [uniformShiftLink] using congrArg Prod.fst heq
  · simpa only [uniformShiftLink] using congrArg Prod.snd heq

def uniformShiftedLinkList (padding base : Nat) : List Z4Link :=
  (distinctBoxLinks base).map (uniformShiftLink padding)

theorem uniformShiftedLinkList_nodup (padding base : Nat) :
    (uniformShiftedLinkList padding base).Nodup := by
  unfold uniformShiftedLinkList
  exact nodup_map_of_injOn (uniformShiftLink padding)
    (distinctBoxLinks base) (distinctBoxLinks_nodup base)
    (fun _ _ _ _ heq => uniformShiftLink_injective padding heq)

theorem uniformShiftedLinkList_subset_target
    {padding base : Nat} {link : Z4Link}
    (hlink : link ∈ uniformShiftedLinkList padding base) :
    link ∈ distinctBoxLinks (uniformPaddedBase padding base) := by
  obtain ⟨sourceLink, hsourceLink, rfl⟩ := List.mem_map.mp hlink
  unfold distinctBoxLinks at hsourceLink ⊢
  have hsourceBox : sourceLink ∈ boxLinks base :=
    List.mem_eraseDups.mp hsourceLink
  unfold boxLinks at hsourceBox
  obtain ⟨sourcePlaquette, hsourcePlaquette, hboundary⟩ :=
    List.mem_flatMap.mp hsourceBox
  apply List.mem_eraseDups.mpr
  unfold boxLinks
  apply List.mem_flatMap.mpr
  refine ⟨uniformShiftPlaquette padding sourcePlaquette,
    uniformShiftPlaquette_mem_padded_box hsourcePlaquette, ?_⟩
  rw [edgesOf_uniformShiftPlaquette]
  exact List.mem_map.mpr ⟨sourceLink, hboundary, rfl⟩

def inheritedUniformShiftedLinks (padding base : Nat) : List Z4Link :=
  (distinctBoxLinks (uniformPaddedBase padding base)).filter
    (fun link => decide (link ∈ uniformShiftedLinkList padding base))

theorem inheritedUniformShiftedLinks_sublist (padding base : Nat) :
    inheritedUniformShiftedLinks padding base <+
      distinctBoxLinks (uniformPaddedBase padding base) :=
  List.filter_sublist

theorem inheritedUniformShiftedLinks_nodup (padding base : Nat) :
    (inheritedUniformShiftedLinks padding base).Nodup :=
  List.filter_sublist.nodup (distinctBoxLinks_nodup (uniformPaddedBase padding base))

theorem uniformShiftedLinkList_perm_inherited (padding base : Nat) :
    (uniformShiftedLinkList padding base).Perm
      (inheritedUniformShiftedLinks padding base) := by
  apply perm_of_nodup_mem_iff_constructive
    (uniformShiftedLinkList padding base)
    (inheritedUniformShiftedLinks padding base)
    (uniformShiftedLinkList_nodup padding base)
    (inheritedUniformShiftedLinks_nodup padding base)
  intro link
  unfold inheritedUniformShiftedLinks
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hlink
    exact ⟨uniformShiftedLinkList_subset_target hlink, hlink⟩
  · exact fun hlink => hlink.2

theorem uniformShiftLink_mem_edges_iff
    (padding : Nat) (link : Z4Link) (plaquette : Z4Plaq) :
    uniformShiftLink padding link ∈
        edgesOf (uniformShiftPlaquette padding plaquette) ↔
      link ∈ edgesOf plaquette := by
  rw [edgesOf_uniformShiftPlaquette]
  constructor
  · intro hmem
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
    have hid : source = link := uniformShiftLink_injective padding heq
    simpa only [hid] using hsource
  · intro hmem
    exact List.mem_map.mpr ⟨link, hmem, rfl⟩

def sourceIncidentPlaquettes (base : Nat) (link : Z4Link) :
    List Z4Plaq :=
  (boxPlaquettes base).filter
    (fun plaquette => decide (link ∈ edgesOf plaquette))

def targetIncidentPlaquettes (padding base : Nat) (link : Z4Link) :
    List Z4Plaq :=
  (boxPlaquettes (uniformPaddedBase padding base)).filter
    (fun plaquette =>
      decide (uniformShiftLink padding link ∈ edgesOf plaquette))

def activeUniformShiftedIncidentPlaquettes
    (padding base : Nat) (link : Z4Link) : List Z4Plaq :=
  (targetIncidentPlaquettes padding base link).filter
    (fun plaquette =>
      decide (plaquette ∈ uniformShiftedPlaquetteList padding base))

theorem mappedSourceIncidentPlaquettes_nodup
    (padding base : Nat) (link : Z4Link) :
    ((sourceIncidentPlaquettes base link).map
      (uniformShiftPlaquette padding)).Nodup := by
  apply nodup_map_of_injOn (uniformShiftPlaquette padding)
    (sourceIncidentPlaquettes base link)
  · unfold sourceIncidentPlaquettes
    exact List.filter_sublist.nodup (boxPlaquettes_nodup base)
  · intro _ _ _ _ heq
    exact uniformShiftPlaquette_injective padding heq

theorem activeUniformShiftedIncidentPlaquettes_nodup
    (padding base : Nat) (link : Z4Link) :
    (activeUniformShiftedIncidentPlaquettes padding base link).Nodup := by
  unfold activeUniformShiftedIncidentPlaquettes targetIncidentPlaquettes
  exact List.filter_sublist.nodup
    (List.filter_sublist.nodup
      (boxPlaquettes_nodup (uniformPaddedBase padding base)))

theorem mappedSourceIncidentPlaquettes_perm_active
    (padding base : Nat) (link : Z4Link) :
    ((sourceIncidentPlaquettes base link).map
        (uniformShiftPlaquette padding)).Perm
      (activeUniformShiftedIncidentPlaquettes padding base link) := by
  apply perm_of_nodup_mem_iff_constructive
    ((sourceIncidentPlaquettes base link).map
      (uniformShiftPlaquette padding))
    (activeUniformShiftedIncidentPlaquettes padding base link)
    (mappedSourceIncidentPlaquettes_nodup padding base link)
    (activeUniformShiftedIncidentPlaquettes_nodup padding base link)
  intro plaquette
  constructor
  · intro hmem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
    have hparts := List.mem_filter.mp hsource
    unfold activeUniformShiftedIncidentPlaquettes
      targetIncidentPlaquettes
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_filter.mpr
      exact ⟨uniformShiftPlaquette_mem_padded_box hparts.1,
        by simpa only [decide_eq_true_eq] using
          (uniformShiftLink_mem_edges_iff padding link source).2
            (of_decide_eq_true hparts.2)⟩
    · apply decide_eq_true
      unfold uniformShiftedPlaquetteList
      exact List.mem_map.mpr ⟨source, hparts.1, rfl⟩
  · intro hmem
    have hparts := List.mem_filter.mp hmem
    have hshifted :
        plaquette ∈ uniformShiftedPlaquetteList padding base :=
      of_decide_eq_true hparts.2
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hshifted
    subst plaquette
    apply List.mem_map.mpr
    refine ⟨source, ?_, rfl⟩
    have htargetParts := List.mem_filter.mp hparts.1
    apply List.mem_filter.mpr
    exact ⟨hsource,
      decide_eq_true
        ((uniformShiftLink_mem_edges_iff padding link source).1
          (of_decide_eq_true htargetParts.2))⟩

def activeUniformShiftedIncidentSpins
    (padding base : Nat) (physical : EdgeLabelling)
    (link : Z4Link) : List Nat :=
  (activeUniformShiftedIncidentPlaquettes padding base link).map
    (geometricSpinOfPhysical (uniformPaddedBase padding base)
      (uniformShiftTransportPhysical padding base physical))

theorem incidentPhysicalSpins_perm_activeUniformShifted
    (padding base : Nat) (physical : EdgeLabelling)
    (link : Z4Link) :
    (incidentPhysicalSpins base link physical).Perm
      (activeUniformShiftedIncidentSpins
        padding base physical link) := by
  let targetSpin := geometricSpinOfPhysical (uniformPaddedBase padding base)
    (uniformShiftTransportPhysical padding base physical)
  have hperm := (mappedSourceIncidentPlaquettes_perm_active
    padding base link).map targetSpin
  have hleft :
      ((sourceIncidentPlaquettes base link).map
          (uniformShiftPlaquette padding)).map targetSpin =
        incidentPhysicalSpins base link physical := by
    rw [incidentPhysicalSpins_eq_geometric]
    unfold sourceIncidentPlaquettes geometricIncidentSpins
    rw [List.map_map]
    apply List.map_congr_left
    intro plaquette hplaquette
    change targetSpin (uniformShiftPlaquette padding plaquette) =
      geometricSpinOfPhysical base physical plaquette
    unfold targetSpin
    have hmem := (List.mem_filter.mp hplaquette).1
    rw [geometricSpinOfUniformShiftTransport_eq_of_mem_box
          (uniformShiftPlaquette_mem_padded_box hmem),
      uniformShiftedGeometricSpin_recover]
  rw [hleft] at hperm
  exact hperm

theorem activeUniformShiftedIncidentSpins_zeroExtension
    (padding base : Nat) (physical : EdgeLabelling) (link : Z4Link) :
    ZeroExtension
      (activeUniformShiftedIncidentSpins padding base physical link)
      (incidentPhysicalSpins (uniformPaddedBase padding base)
        (uniformShiftLink padding link)
        (uniformShiftTransportPhysical padding base physical)) := by
  rw [incidentPhysicalSpins_eq_geometric]
  unfold activeUniformShiftedIncidentSpins geometricIncidentSpins
    activeUniformShiftedIncidentPlaquettes targetIncidentPlaquettes
  let targetSpin := geometricSpinOfPhysical (uniformPaddedBase padding base)
    (uniformShiftTransportPhysical padding base physical)
  apply ZeroExtension.map_of_sublist targetSpin List.filter_sublist
  · exact List.filter_sublist.nodup
      (boxPlaquettes_nodup (uniformPaddedBase padding base))
  · intro plaquette htarget hnotActive
    have htargetBox := (List.mem_filter.mp htarget).1
    have hnotShifted :
        plaquette ∉ uniformShiftedPlaquetteList padding base := by
      intro hshifted
      apply hnotActive
      exact List.mem_filter.mpr
        ⟨htarget, by simpa only [decide_eq_true_eq]⟩
    unfold targetSpin
    rw [geometricSpinOfUniformShiftTransport_eq_of_mem_box htargetBox,
      uniformShiftedGeometricSpin_zero_of_not_mem
        padding base physical hnotShifted]

theorem incidentPhysicalSpins_external_bounded
    {K base : Nat} {physical : EdgeLabelling} {link : Z4Link}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base))) :
    SpinsBounded K (incidentPhysicalSpins base link physical) := by
  have hsound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount base)) physical hphysical
  intro spin hspin
  obtain ⟨plaquetteId, hid, rfl⟩ := List.mem_map.mp hspin
  have hidRange : plaquetteId ∈
      List.range (plaquetteEdgeCount base) :=
    List.mem_range.mpr (incidentPlaqId_lt_count hid)
  exact Nat.le_of_lt_succ (hsound.1 plaquetteId hidRange)

/-! ## 4. Exact local link-factor invariance -/

theorem canonicalGeometricLinkFactor_uniformShift
    {K padding base : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base)))
    (link : Z4Link) :
    canonicalGeometricLinkFactor K base physical link =
      canonicalGeometricLinkFactor K (uniformPaddedBase padding base)
        (uniformShiftTransportPhysical padding base physical)
        (uniformShiftLink padding link) := by
  unfold canonicalGeometricLinkFactor explicitLinkMultiplicityFactor
  apply congrArg Q'.ofNat
  rw [actualExplicitMultiplicity_eq_incidentList,
    actualExplicitMultiplicity_eq_incidentList]
  let sourceSpins := incidentPhysicalSpins base link physical
  let activeSpins := activeUniformShiftedIncidentSpins
    padding base physical link
  let targetSpins := incidentPhysicalSpins (uniformPaddedBase padding base)
    (uniformShiftLink padding link)
    (uniformShiftTransportPhysical padding base physical)
  have hperm : sourceSpins.Perm activeSpins :=
    incidentPhysicalSpins_perm_activeUniformShifted
      padding base physical link
  have hsourceLength : sourceSpins.length ≤ 6 := by
    unfold sourceSpins
    simpa only [incidentPhysicalSpins, List.length_map] using
      incidentPlaqIds_length_le_six base link
  have hsourceBounded : SpinsBounded K sourceSpins := by
    unfold sourceSpins
    exact incidentPhysicalSpins_external_bounded hphysical
  have hpermEq :
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          sourceSpins.length (externalSpinsOfList sourceSpins) =
        explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          activeSpins.length (externalSpinsOfList activeSpins) :=
    explicitValenceMultiplicity_physical_perm
      hperm hsourceLength hsourceBounded
  have hzero : ZeroExtension activeSpins targetSpins := by
    unfold activeSpins targetSpins
    exact activeUniformShiftedIncidentSpins_zeroExtension
      padding base physical link
  have hactiveLength : activeSpins.length ≤ 6 := by
    rw [← hperm.length_eq]
    exact hsourceLength
  have htargetLength : targetSpins.length ≤ 6 := by
    unfold targetSpins
    simpa only [incidentPhysicalSpins, List.length_map] using
      incidentPlaqIds_length_le_six (uniformPaddedBase padding base)
        (uniformShiftLink padding link)
  have hsourceAux :
      SpinsBounded (linkAuxiliaryCutoff K) sourceSpins := by
    intro spin hspin
    exact Nat.le_trans (hsourceBounded spin hspin)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hactiveAux :
      SpinsBounded (linkAuxiliaryCutoff K) activeSpins :=
    spinsBounded_of_perm hperm hsourceAux
  have hzeroEq :
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          activeSpins.length (externalSpinsOfList activeSpins) =
        explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          targetSpins.length (externalSpinsOfList targetSpins) :=
    explicitValenceMultiplicity_zeroExtension
      hzero hactiveLength htargetLength hactiveAux
  exact hpermEq.trans hzeroEq

theorem canonicalGeometricLinkFactor_uniformShift_eq_one_of_new
    (K padding base : Nat) (physical : EdgeLabelling) {link : Z4Link}
    (hnew : link ∉ uniformShiftedLinkList padding base) :
    canonicalGeometricLinkFactor K (uniformPaddedBase padding base)
        (uniformShiftTransportPhysical padding base physical) link = 1 := by
  unfold canonicalGeometricLinkFactor
  apply explicitLinkMultiplicityFactor_eq_one_of_untouched
  unfold linkTouchesExcitationB
  apply (hasExcitedB_false_iff_zero_on
    (uniformShiftTransportPhysical padding base physical)
    (incidentPlaqIds (uniformPaddedBase padding base) link)).2
  intro targetId hincident
  obtain ⟨plaquette, hindexed, hboundary⟩ :=
    mem_incidentPlaqIds.mp hincident
  rw [uniformShiftTransportPhysical_eq_on_enumerate hindexed]
  by_cases hshifted :
      plaquette ∈ uniformShiftedPlaquetteList padding base
  · obtain ⟨sourcePlaquette, hsourcePlaquette, heq⟩ :=
      List.mem_map.mp hshifted
    subst plaquette
    rw [edgesOf_uniformShiftPlaquette] at hboundary
    obtain ⟨sourceLink, hsourceBoundary, hlinkEq⟩ :=
      List.mem_map.mp hboundary
    exfalso
    apply hnew
    unfold uniformShiftedLinkList
    apply List.mem_map.mpr
    refine ⟨sourceLink, ?_, hlinkEq⟩
    unfold distinctBoxLinks
    apply List.mem_eraseDups.mpr
    exact boundary_mem_boxLinks hsourcePlaquette hsourceBoundary
  · exact uniformShiftedGeometricSpin_zero_of_not_mem
      padding base physical hshifted

/-! ## 5. The full link product and spin-foam summand -/

theorem explicitLinkMultiplicityProduct_uniformShift
    {K padding base : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base))) :
    explicitLinkMultiplicityProduct K base physical
        (enumerate (distinctBoxLinks base)) ≈
      explicitLinkMultiplicityProduct K (uniformPaddedBase padding base)
        (uniformShiftTransportPhysical padding base physical)
        (enumerate (distinctBoxLinks (uniformPaddedBase padding base))) := by
  rw [explicitLinkMultiplicityProduct_full_eq_canonical,
    explicitLinkMultiplicityProduct_full_eq_canonical]
  unfold canonicalGeometricLinkProduct
  let sourceFactor := canonicalGeometricLinkFactor K base physical
  let targetFactor := canonicalGeometricLinkFactor K (uniformPaddedBase padding base)
    (uniformShiftTransportPhysical padding base physical)
  have hlocal :
      listQProduct sourceFactor (distinctBoxLinks base) ≈
        listQProduct targetFactor
          (uniformShiftedLinkList padding base) := by
    have hcongr :
        listQProduct sourceFactor (distinctBoxLinks base) ≈
          listQProduct
            (fun link => targetFactor (uniformShiftLink padding link))
            (distinctBoxLinks base) := by
      apply listQProduct_congr_eqv
      intro link _
      apply Q'.eqv_of_eq
      unfold sourceFactor targetFactor
      exact canonicalGeometricLinkFactor_uniformShift hphysical link
    have hmap :
        listQProduct targetFactor (uniformShiftedLinkList padding base) =
          listQProduct
            (fun link => targetFactor (uniformShiftLink padding link))
            (distinctBoxLinks base) := by
      unfold uniformShiftedLinkList
      exact listQProduct_map targetFactor (uniformShiftLink padding)
        (distinctBoxLinks base)
    exact Q'.eqv_trans _ _ _ hcongr
      (Q'.eqv_symm (Q'.eqv_of_eq hmap))
  have hperm :
      listQProduct targetFactor (uniformShiftedLinkList padding base) ≈
        listQProduct targetFactor
          (inheritedUniformShiftedLinks padding base) :=
    listQProduct_perm targetFactor
      (uniformShiftedLinkList_perm_inherited padding base)
  have hvacuum :
      listQProduct targetFactor (distinctBoxLinks (uniformPaddedBase padding base)) ≈
        listQProduct targetFactor
          (inheritedUniformShiftedLinks padding base) := by
    apply listQProduct_sublist_vacuum targetFactor
      (inheritedUniformShiftedLinks_sublist padding base)
      (distinctBoxLinks_nodup (uniformPaddedBase padding base))
    intro link htarget hnotInherited
    apply Q'.eqv_of_eq
    unfold targetFactor
    apply canonicalGeometricLinkFactor_uniformShift_eq_one_of_new
    intro hshifted
    apply hnotInherited
    unfold inheritedUniformShiftedLinks
    exact List.mem_filter.mpr
      ⟨htarget, by simpa only [decide_eq_true_eq]⟩
  exact Q'.eqv_trans _ _ _ hlocal
    (Q'.eqv_trans _ _ _ hperm (Q'.eqv_symm hvacuum))

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- The complete arbitrary-cutoff physical spin-foam summand is exactly
invariant under the uniform four-coordinate padded embedding. -/
theorem parametricKPhysicalTerm_uniformShift
    (w : Q') {K padding base : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base))) :
    parametricKPhysicalTerm w K base physical ≈
      parametricKPhysicalTerm w K (uniformPaddedBase padding base)
        (uniformShiftTransportPhysical padding base physical) := by
  unfold parametricKPhysicalTerm
  exact qmul_congr_local
    (Q'.eqv_symm
      (parametricKPhysicalFaceFactor_uniformShift
        w K padding base physical))
    (explicitLinkMultiplicityProduct_uniformShift hphysical)

#print axioms uniformShiftedPlaquetteList_subset_target
#print axioms uniformShiftedPlaquetteList_perm_inherited
#print axioms geometricFaceFactor_uniformShiftTransport
#print axioms parametricKPhysicalFaceFactor_uniformShift
#print axioms uniformShiftedLinkList_perm_inherited
#print axioms mappedSourceIncidentPlaquettes_perm_active
#print axioms incidentPhysicalSpins_perm_activeUniformShifted
#print axioms activeUniformShiftedIncidentSpins_zeroExtension
#print axioms canonicalGeometricLinkFactor_uniformShift
#print axioms canonicalGeometricLinkFactor_uniformShift_eq_one_of_new
#print axioms explicitLinkMultiplicityProduct_uniformShift
#print axioms parametricKPhysicalTerm_uniformShift

end YMGap.Continuum.Z4UniformShiftPhysicalWeights
