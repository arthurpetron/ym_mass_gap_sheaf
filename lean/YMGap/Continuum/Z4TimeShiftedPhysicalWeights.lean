/-
# Exact spin-foam weights under affine Euclidean-time transport

This module proves that the affine physical-labelling map constructed in
`Z4TimeShiftedPhysicalTransport` preserves the complete arbitrary-cutoff
finite spin-foam summand.  The proof reindexes face factors by translated
plaquettes and local link multiplicities by translated links; target cells
outside the translated subbox carry the vacuum spin and contribute one.
-/

import YMGap.Continuum.Z4FusionMultiplicityPermutationLift
import YMGap.Continuum.Z4TimeShiftedPhysicalTransport

namespace YMGap.Continuum.Z4TimeShiftedPhysicalWeights

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
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The translated plaquette sublist as an unordered finite set -/

theorem timeShiftedPlaquetteList_subset_target
    {shift base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ timeShiftedPlaquetteList shift base) :
    plaquette ∈ boxPlaquettes (base + shift) := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  exact timeShiftPlaquette_mem_box_add hsource

def inheritedTimeShiftedPlaquettes (shift base : Nat) : List Z4Plaq :=
  (boxPlaquettes (base + shift)).filter
    (fun plaquette =>
      decide (plaquette ∈ timeShiftedPlaquetteList shift base))

theorem inheritedTimeShiftedPlaquettes_sublist (shift base : Nat) :
    inheritedTimeShiftedPlaquettes shift base <+
      boxPlaquettes (base + shift) :=
  List.filter_sublist

theorem inheritedTimeShiftedPlaquettes_nodup (shift base : Nat) :
    (inheritedTimeShiftedPlaquettes shift base).Nodup :=
  List.filter_sublist.nodup (boxPlaquettes_nodup (base + shift))

theorem timeShiftedPlaquetteList_perm_inherited
    (shift base : Nat) :
    (timeShiftedPlaquetteList shift base).Perm
      (inheritedTimeShiftedPlaquettes shift base) := by
  apply perm_of_nodup_mem_iff_constructive
    (timeShiftedPlaquetteList shift base)
    (inheritedTimeShiftedPlaquettes shift base)
    (timeShiftedPlaquetteList_nodup shift base)
    (inheritedTimeShiftedPlaquettes_nodup shift base)
  intro plaquette
  unfold inheritedTimeShiftedPlaquettes
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hmem
    exact ⟨timeShiftedPlaquetteList_subset_target hmem, hmem⟩
  · exact fun hmem => hmem.2

/-! ## 2. Exact face-factor invariance -/

theorem geometricFaceFactor_timeShiftTransport
    (w : Q') (K shift base : Nat) (physical : EdgeLabelling) :
    geometricFaceFactor w K
        (geometricSpinOfPhysical (base + shift)
          (timeShiftTransportPhysical shift base physical))
        (boxPlaquettes (base + shift)) ≈
      geometricFaceFactor w K
        (geometricSpinOfPhysical base physical)
        (boxPlaquettes base) := by
  let targetValue : Z4Plaq → Q' := fun plaquette =>
    coeffAt (heatKernelPacket K w)
      (geometricSpinOfPhysical (base + shift)
        (timeShiftTransportPhysical shift base physical) plaquette)
  let sourceValue : Z4Plaq → Q' := fun plaquette =>
    coeffAt (heatKernelPacket K w)
      (geometricSpinOfPhysical base physical plaquette)
  have hvacuum : ∀ plaquette,
      plaquette ∈ boxPlaquettes (base + shift) →
      plaquette ∉ inheritedTimeShiftedPlaquettes shift base →
      targetValue plaquette ≈ 1 := by
    intro plaquette htarget hnot
    have hnotShifted :
        plaquette ∉ timeShiftedPlaquetteList shift base := by
      intro hshifted
      apply hnot
      unfold inheritedTimeShiftedPlaquettes
      exact List.mem_filter.mpr
        ⟨htarget, by simpa only [decide_eq_true_eq]⟩
    unfold targetValue
    rw [geometricSpinOfTimeShiftTransport_eq_of_mem_box htarget,
      timeShiftedGeometricSpin_zero_of_not_mem
        shift base physical hnotShifted,
      coeffAt_heatKernelPacket (show 0 < K + 1 by omega),
      coeffW_zero]
    exact Q'.eqv_refl 1
  have hremove :
      listQProduct targetValue (boxPlaquettes (base + shift)) ≈
        listQProduct targetValue
          (inheritedTimeShiftedPlaquettes shift base) := by
    exact listQProduct_sublist_vacuum targetValue
      (inheritedTimeShiftedPlaquettes_sublist shift base)
      (boxPlaquettes_nodup (base + shift)) hvacuum
  have hperm :
      listQProduct targetValue
          (inheritedTimeShiftedPlaquettes shift base) ≈
        listQProduct targetValue
          (timeShiftedPlaquetteList shift base) :=
    listQProduct_perm targetValue
      (timeShiftedPlaquetteList_perm_inherited shift base).symm
  have hmap :
      listQProduct targetValue
          (timeShiftedPlaquetteList shift base) =
        listQProduct
          (fun plaquette =>
            targetValue (timeShiftPlaquette shift plaquette))
          (boxPlaquettes base) := by
    unfold timeShiftedPlaquetteList
    exact listQProduct_map targetValue (timeShiftPlaquette shift)
      (boxPlaquettes base)
  have hagree : ∀ plaquette, plaquette ∈ boxPlaquettes base →
      targetValue (timeShiftPlaquette shift plaquette) =
        sourceValue plaquette := by
    intro plaquette hplaquette
    unfold targetValue sourceValue
    rw [geometricSpinOfTimeShiftTransport_eq_of_mem_box
          (timeShiftPlaquette_mem_box_add hplaquette),
      timeShiftedGeometricSpin_recover]
  have hsource :
      listQProduct
          (fun plaquette =>
            targetValue (timeShiftPlaquette shift plaquette))
          (boxPlaquettes base) =
        listQProduct sourceValue (boxPlaquettes base) :=
    listQProduct_congr _ _ _ hagree
  unfold geometricFaceFactor
  exact Q'.eqv_trans _ _ _ hremove
    (Q'.eqv_trans _ _ _ hperm
      (Q'.eqv_of_eq (hmap.trans hsource)))

theorem parametricKPhysicalFaceFactor_timeShift
    (w : Q') (K shift base : Nat) (physical : EdgeLabelling) :
    parametricKPhysicalFaceFactor w K (base + shift)
        (timeShiftTransportPhysical shift base physical) ≈
      parametricKPhysicalFaceFactor w K base physical := by
  rw [parametricKPhysicalFaceFactor_eq_geometric,
    parametricKPhysicalFaceFactor_eq_geometric]
  exact geometricFaceFactor_timeShiftTransport
    w K shift base physical

/-! ## 3. Translated links and incident-spin lists -/

theorem timeShiftLink_injective (shift : Nat) :
    Function.Injective (timeShiftLink shift) := by
  intro left right heq
  apply Prod.ext
  · apply timeShiftVertex_injective shift
    simpa only [timeShiftLink] using congrArg Prod.fst heq
  · simpa only [timeShiftLink] using congrArg Prod.snd heq

def timeShiftedLinkList (shift base : Nat) : List Z4Link :=
  (distinctBoxLinks base).map (timeShiftLink shift)

theorem timeShiftedLinkList_nodup (shift base : Nat) :
    (timeShiftedLinkList shift base).Nodup := by
  unfold timeShiftedLinkList
  exact nodup_map_of_injOn (timeShiftLink shift)
    (distinctBoxLinks base) (distinctBoxLinks_nodup base)
    (fun _ _ _ _ heq => timeShiftLink_injective shift heq)

theorem timeShiftedLinkList_subset_target
    {shift base : Nat} {link : Z4Link}
    (hlink : link ∈ timeShiftedLinkList shift base) :
    link ∈ distinctBoxLinks (base + shift) := by
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
  refine ⟨timeShiftPlaquette shift sourcePlaquette,
    timeShiftPlaquette_mem_box_add hsourcePlaquette, ?_⟩
  rw [edgesOf_timeShiftPlaquette]
  exact List.mem_map.mpr ⟨sourceLink, hboundary, rfl⟩

def inheritedTimeShiftedLinks (shift base : Nat) : List Z4Link :=
  (distinctBoxLinks (base + shift)).filter
    (fun link => decide (link ∈ timeShiftedLinkList shift base))

theorem inheritedTimeShiftedLinks_sublist (shift base : Nat) :
    inheritedTimeShiftedLinks shift base <+
      distinctBoxLinks (base + shift) :=
  List.filter_sublist

theorem inheritedTimeShiftedLinks_nodup (shift base : Nat) :
    (inheritedTimeShiftedLinks shift base).Nodup :=
  List.filter_sublist.nodup (distinctBoxLinks_nodup (base + shift))

theorem timeShiftedLinkList_perm_inherited (shift base : Nat) :
    (timeShiftedLinkList shift base).Perm
      (inheritedTimeShiftedLinks shift base) := by
  apply perm_of_nodup_mem_iff_constructive
    (timeShiftedLinkList shift base)
    (inheritedTimeShiftedLinks shift base)
    (timeShiftedLinkList_nodup shift base)
    (inheritedTimeShiftedLinks_nodup shift base)
  intro link
  unfold inheritedTimeShiftedLinks
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hlink
    exact ⟨timeShiftedLinkList_subset_target hlink, hlink⟩
  · exact fun hlink => hlink.2

theorem timeShiftLink_mem_edges_iff
    (shift : Nat) (link : Z4Link) (plaquette : Z4Plaq) :
    timeShiftLink shift link ∈
        edgesOf (timeShiftPlaquette shift plaquette) ↔
      link ∈ edgesOf plaquette := by
  rw [edgesOf_timeShiftPlaquette]
  constructor
  · intro hmem
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
    have hid : source = link := timeShiftLink_injective shift heq
    simpa only [hid] using hsource
  · intro hmem
    exact List.mem_map.mpr ⟨link, hmem, rfl⟩

def sourceIncidentPlaquettes (base : Nat) (link : Z4Link) :
    List Z4Plaq :=
  (boxPlaquettes base).filter
    (fun plaquette => decide (link ∈ edgesOf plaquette))

def targetIncidentPlaquettes (shift base : Nat) (link : Z4Link) :
    List Z4Plaq :=
  (boxPlaquettes (base + shift)).filter
    (fun plaquette =>
      decide (timeShiftLink shift link ∈ edgesOf plaquette))

def activeTimeShiftedIncidentPlaquettes
    (shift base : Nat) (link : Z4Link) : List Z4Plaq :=
  (targetIncidentPlaquettes shift base link).filter
    (fun plaquette =>
      decide (plaquette ∈ timeShiftedPlaquetteList shift base))

theorem mappedSourceIncidentPlaquettes_nodup
    (shift base : Nat) (link : Z4Link) :
    ((sourceIncidentPlaquettes base link).map
      (timeShiftPlaquette shift)).Nodup := by
  apply nodup_map_of_injOn (timeShiftPlaquette shift)
    (sourceIncidentPlaquettes base link)
  · unfold sourceIncidentPlaquettes
    exact List.filter_sublist.nodup (boxPlaquettes_nodup base)
  · intro _ _ _ _ heq
    exact timeShiftPlaquette_injective shift heq

theorem activeTimeShiftedIncidentPlaquettes_nodup
    (shift base : Nat) (link : Z4Link) :
    (activeTimeShiftedIncidentPlaquettes shift base link).Nodup := by
  unfold activeTimeShiftedIncidentPlaquettes targetIncidentPlaquettes
  exact List.filter_sublist.nodup
    (List.filter_sublist.nodup
      (boxPlaquettes_nodup (base + shift)))

theorem mappedSourceIncidentPlaquettes_perm_active
    (shift base : Nat) (link : Z4Link) :
    ((sourceIncidentPlaquettes base link).map
        (timeShiftPlaquette shift)).Perm
      (activeTimeShiftedIncidentPlaquettes shift base link) := by
  apply perm_of_nodup_mem_iff_constructive
    ((sourceIncidentPlaquettes base link).map
      (timeShiftPlaquette shift))
    (activeTimeShiftedIncidentPlaquettes shift base link)
    (mappedSourceIncidentPlaquettes_nodup shift base link)
    (activeTimeShiftedIncidentPlaquettes_nodup shift base link)
  intro plaquette
  constructor
  · intro hmem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
    have hparts := List.mem_filter.mp hsource
    unfold activeTimeShiftedIncidentPlaquettes
      targetIncidentPlaquettes
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_filter.mpr
      exact ⟨timeShiftPlaquette_mem_box_add hparts.1,
        by simpa only [decide_eq_true_eq] using
          (timeShiftLink_mem_edges_iff shift link source).2
            (of_decide_eq_true hparts.2)⟩
    · apply decide_eq_true
      unfold timeShiftedPlaquetteList
      exact List.mem_map.mpr ⟨source, hparts.1, rfl⟩
  · intro hmem
    have hparts := List.mem_filter.mp hmem
    have hshifted :
        plaquette ∈ timeShiftedPlaquetteList shift base :=
      of_decide_eq_true hparts.2
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hshifted
    subst plaquette
    apply List.mem_map.mpr
    refine ⟨source, ?_, rfl⟩
    have htargetParts := List.mem_filter.mp hparts.1
    apply List.mem_filter.mpr
    exact ⟨hsource,
      decide_eq_true
        ((timeShiftLink_mem_edges_iff shift link source).1
          (of_decide_eq_true htargetParts.2))⟩

def activeTimeShiftedIncidentSpins
    (shift base : Nat) (physical : EdgeLabelling)
    (link : Z4Link) : List Nat :=
  (activeTimeShiftedIncidentPlaquettes shift base link).map
    (geometricSpinOfPhysical (base + shift)
      (timeShiftTransportPhysical shift base physical))

theorem incidentPhysicalSpins_perm_activeTimeShifted
    (shift base : Nat) (physical : EdgeLabelling)
    (link : Z4Link) :
    (incidentPhysicalSpins base link physical).Perm
      (activeTimeShiftedIncidentSpins
        shift base physical link) := by
  let targetSpin := geometricSpinOfPhysical (base + shift)
    (timeShiftTransportPhysical shift base physical)
  have hperm := (mappedSourceIncidentPlaquettes_perm_active
    shift base link).map targetSpin
  have hleft :
      ((sourceIncidentPlaquettes base link).map
          (timeShiftPlaquette shift)).map targetSpin =
        incidentPhysicalSpins base link physical := by
    rw [incidentPhysicalSpins_eq_geometric]
    unfold sourceIncidentPlaquettes geometricIncidentSpins
    rw [List.map_map]
    apply List.map_congr_left
    intro plaquette hplaquette
    change targetSpin (timeShiftPlaquette shift plaquette) =
      geometricSpinOfPhysical base physical plaquette
    unfold targetSpin
    have hmem := (List.mem_filter.mp hplaquette).1
    rw [geometricSpinOfTimeShiftTransport_eq_of_mem_box
          (timeShiftPlaquette_mem_box_add hmem),
      timeShiftedGeometricSpin_recover]
  rw [hleft] at hperm
  exact hperm

theorem activeTimeShiftedIncidentSpins_zeroExtension
    (shift base : Nat) (physical : EdgeLabelling) (link : Z4Link) :
    ZeroExtension
      (activeTimeShiftedIncidentSpins shift base physical link)
      (incidentPhysicalSpins (base + shift)
        (timeShiftLink shift link)
        (timeShiftTransportPhysical shift base physical)) := by
  rw [incidentPhysicalSpins_eq_geometric]
  unfold activeTimeShiftedIncidentSpins geometricIncidentSpins
    activeTimeShiftedIncidentPlaquettes targetIncidentPlaquettes
  let targetSpin := geometricSpinOfPhysical (base + shift)
    (timeShiftTransportPhysical shift base physical)
  apply ZeroExtension.map_of_sublist targetSpin List.filter_sublist
  · exact List.filter_sublist.nodup
      (boxPlaquettes_nodup (base + shift))
  · intro plaquette htarget hnotActive
    have htargetBox := (List.mem_filter.mp htarget).1
    have hnotShifted :
        plaquette ∉ timeShiftedPlaquetteList shift base := by
      intro hshifted
      apply hnotActive
      exact List.mem_filter.mpr
        ⟨htarget, by simpa only [decide_eq_true_eq]⟩
    unfold targetSpin
    rw [geometricSpinOfTimeShiftTransport_eq_of_mem_box htargetBox,
      timeShiftedGeometricSpin_zero_of_not_mem
        shift base physical hnotShifted]

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

theorem canonicalGeometricLinkFactor_timeShift
    {K shift base : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base)))
    (link : Z4Link) :
    canonicalGeometricLinkFactor K base physical link =
      canonicalGeometricLinkFactor K (base + shift)
        (timeShiftTransportPhysical shift base physical)
        (timeShiftLink shift link) := by
  unfold canonicalGeometricLinkFactor explicitLinkMultiplicityFactor
  apply congrArg Q'.ofNat
  rw [actualExplicitMultiplicity_eq_incidentList,
    actualExplicitMultiplicity_eq_incidentList]
  let sourceSpins := incidentPhysicalSpins base link physical
  let activeSpins := activeTimeShiftedIncidentSpins
    shift base physical link
  let targetSpins := incidentPhysicalSpins (base + shift)
    (timeShiftLink shift link)
    (timeShiftTransportPhysical shift base physical)
  have hperm : sourceSpins.Perm activeSpins :=
    incidentPhysicalSpins_perm_activeTimeShifted
      shift base physical link
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
    exact activeTimeShiftedIncidentSpins_zeroExtension
      shift base physical link
  have hactiveLength : activeSpins.length ≤ 6 := by
    rw [← hperm.length_eq]
    exact hsourceLength
  have htargetLength : targetSpins.length ≤ 6 := by
    unfold targetSpins
    simpa only [incidentPhysicalSpins, List.length_map] using
      incidentPlaqIds_length_le_six (base + shift)
        (timeShiftLink shift link)
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

theorem canonicalGeometricLinkFactor_timeShift_eq_one_of_new
    (K shift base : Nat) (physical : EdgeLabelling) {link : Z4Link}
    (hnew : link ∉ timeShiftedLinkList shift base) :
    canonicalGeometricLinkFactor K (base + shift)
        (timeShiftTransportPhysical shift base physical) link = 1 := by
  unfold canonicalGeometricLinkFactor
  apply explicitLinkMultiplicityFactor_eq_one_of_untouched
  unfold linkTouchesExcitationB
  apply (hasExcitedB_false_iff_zero_on
    (timeShiftTransportPhysical shift base physical)
    (incidentPlaqIds (base + shift) link)).2
  intro targetId hincident
  obtain ⟨plaquette, hindexed, hboundary⟩ :=
    mem_incidentPlaqIds.mp hincident
  rw [timeShiftTransportPhysical_eq_on_enumerate hindexed]
  by_cases hshifted :
      plaquette ∈ timeShiftedPlaquetteList shift base
  · obtain ⟨sourcePlaquette, hsourcePlaquette, heq⟩ :=
      List.mem_map.mp hshifted
    subst plaquette
    rw [edgesOf_timeShiftPlaquette] at hboundary
    obtain ⟨sourceLink, hsourceBoundary, hlinkEq⟩ :=
      List.mem_map.mp hboundary
    exfalso
    apply hnew
    unfold timeShiftedLinkList
    apply List.mem_map.mpr
    refine ⟨sourceLink, ?_, hlinkEq⟩
    unfold distinctBoxLinks
    apply List.mem_eraseDups.mpr
    exact boundary_mem_boxLinks hsourcePlaquette hsourceBoundary
  · exact timeShiftedGeometricSpin_zero_of_not_mem
      shift base physical hshifted

/-! ## 5. The full link product and spin-foam summand -/

theorem explicitLinkMultiplicityProduct_timeShift
    {K shift base : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base))) :
    explicitLinkMultiplicityProduct K base physical
        (enumerate (distinctBoxLinks base)) ≈
      explicitLinkMultiplicityProduct K (base + shift)
        (timeShiftTransportPhysical shift base physical)
        (enumerate (distinctBoxLinks (base + shift))) := by
  rw [explicitLinkMultiplicityProduct_full_eq_canonical,
    explicitLinkMultiplicityProduct_full_eq_canonical]
  unfold canonicalGeometricLinkProduct
  let sourceFactor := canonicalGeometricLinkFactor K base physical
  let targetFactor := canonicalGeometricLinkFactor K (base + shift)
    (timeShiftTransportPhysical shift base physical)
  have hlocal :
      listQProduct sourceFactor (distinctBoxLinks base) ≈
        listQProduct targetFactor
          (timeShiftedLinkList shift base) := by
    have hcongr :
        listQProduct sourceFactor (distinctBoxLinks base) ≈
          listQProduct
            (fun link => targetFactor (timeShiftLink shift link))
            (distinctBoxLinks base) := by
      apply listQProduct_congr_eqv
      intro link _
      apply Q'.eqv_of_eq
      unfold sourceFactor targetFactor
      exact canonicalGeometricLinkFactor_timeShift hphysical link
    have hmap :
        listQProduct targetFactor (timeShiftedLinkList shift base) =
          listQProduct
            (fun link => targetFactor (timeShiftLink shift link))
            (distinctBoxLinks base) := by
      unfold timeShiftedLinkList
      exact listQProduct_map targetFactor (timeShiftLink shift)
        (distinctBoxLinks base)
    exact Q'.eqv_trans _ _ _ hcongr
      (Q'.eqv_symm (Q'.eqv_of_eq hmap))
  have hperm :
      listQProduct targetFactor (timeShiftedLinkList shift base) ≈
        listQProduct targetFactor
          (inheritedTimeShiftedLinks shift base) :=
    listQProduct_perm targetFactor
      (timeShiftedLinkList_perm_inherited shift base)
  have hvacuum :
      listQProduct targetFactor (distinctBoxLinks (base + shift)) ≈
        listQProduct targetFactor
          (inheritedTimeShiftedLinks shift base) := by
    apply listQProduct_sublist_vacuum targetFactor
      (inheritedTimeShiftedLinks_sublist shift base)
      (distinctBoxLinks_nodup (base + shift))
    intro link htarget hnotInherited
    apply Q'.eqv_of_eq
    unfold targetFactor
    apply canonicalGeometricLinkFactor_timeShift_eq_one_of_new
    intro hshifted
    apply hnotInherited
    unfold inheritedTimeShiftedLinks
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
invariant under the affine time-shift embedding. -/
theorem parametricKPhysicalTerm_timeShift
    (w : Q') {K shift base : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base))) :
    parametricKPhysicalTerm w K base physical ≈
      parametricKPhysicalTerm w K (base + shift)
        (timeShiftTransportPhysical shift base physical) := by
  unfold parametricKPhysicalTerm
  exact qmul_congr_local
    (Q'.eqv_symm
      (parametricKPhysicalFaceFactor_timeShift
        w K shift base physical))
    (explicitLinkMultiplicityProduct_timeShift hphysical)

#print axioms timeShiftedPlaquetteList_subset_target
#print axioms timeShiftedPlaquetteList_perm_inherited
#print axioms geometricFaceFactor_timeShiftTransport
#print axioms parametricKPhysicalFaceFactor_timeShift
#print axioms timeShiftedLinkList_perm_inherited
#print axioms mappedSourceIncidentPlaquettes_perm_active
#print axioms incidentPhysicalSpins_perm_activeTimeShifted
#print axioms activeTimeShiftedIncidentSpins_zeroExtension
#print axioms canonicalGeometricLinkFactor_timeShift
#print axioms canonicalGeometricLinkFactor_timeShift_eq_one_of_new
#print axioms explicitLinkMultiplicityProduct_timeShift
#print axioms parametricKPhysicalTerm_timeShift

end YMGap.Continuum.Z4TimeShiftedPhysicalWeights
