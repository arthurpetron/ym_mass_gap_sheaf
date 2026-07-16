/-
# Exact corrected-slab embedding into its ambient corner box

The boundary-complete reflection slab is literally a filtered plaquette
sublist of the corner box of side `extent + 1`.  This file reads a slab face
labelling geometrically, extends it by spin zero to the omitted top temporal
faces, and proves that the complete arbitrary-cutoff spin-foam summand is
unchanged.  The proof includes every local fusion multiplicity and every new
ambient link; no equality of the two full partitions is asserted.
-/

import YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
import YMGap.Continuum.Z4TimeShiftedPhysicalWeights

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open scoped List
open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4TimeShiftedPhysicalWeights
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Geometric slab lookup and zero extension -/

def slabGeometricSpin (extent : Nat) (physical : EdgeLabelling)
    (plaquette : Z4Plaq) : Nat :=
  lookupLabelFrom physical 0
    (boundaryCompleteSlabPlaquettes extent) plaquette

theorem slabGeometricSpin_eq_of_enumerate
    {extent id : Nat} {physical : EdgeLabelling} {plaquette : Z4Plaq}
    (hindexed : (id, plaquette) ∈
      enumerate (boundaryCompleteSlabPlaquettes extent)) :
    slabGeometricSpin extent physical plaquette = physical id := by
  exact lookupLabelFrom_eq_of_mem_enumerateFrom physical
    (boundaryCompleteSlabPlaquettes_nodup extent) hindexed

theorem slabGeometricSpin_zero_of_not_mem
    (extent : Nat) (physical : EdgeLabelling) {plaquette : Z4Plaq}
    (hnot : plaquette ∉ boundaryCompleteSlabPlaquettes extent) :
    slabGeometricSpin extent physical plaquette = 0 :=
  lookupLabelFrom_zero_of_not_mem physical 0
    (boundaryCompleteSlabPlaquettes extent) plaquette hnot

theorem slabGeometricSpin_le_of_bounded
    {K extent : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)) (plaquette : Z4Plaq) :
    slabGeometricSpin extent physical plaquette ≤ K := by
  by_cases hmem : plaquette ∈ boundaryCompleteSlabPlaquettes extent
  · obtain ⟨id, hindexed⟩ := exists_mem_enumerate hmem
    rw [slabGeometricSpin_eq_of_enumerate hindexed]
    have hsound := boundedEdgeLabellings_sound K
      (slabPhysicalFaceEdges extent) physical hphysical
    apply Nat.le_of_lt_succ
    apply hsound.1 id
    unfold slabPhysicalFaceEdges
    exact List.mem_range.mpr (enumerate_index_lt hindexed)
  · rw [slabGeometricSpin_zero_of_not_mem extent physical hmem]
    exact Nat.zero_le K

/-- Read the corrected slab on its geometric plaquettes and put spin zero on
every other face of the ambient corner box. -/
def slabToAmbientPhysical (extent : Nat)
    (physical : EdgeLabelling) : EdgeLabelling :=
  fun targetId =>
    if targetId < plaquetteEdgeCount (extent + 1) then
      slabGeometricSpin extent physical
        (boxPlaquetteAt (extent + 1) targetId)
    else 0

theorem slabToAmbientPhysical_eq_on_enumerate
    {extent targetId : Nat} {physical : EdgeLabelling}
    {plaquette : Z4Plaq}
    (hindexed : (targetId, plaquette) ∈
      enumerate (boxPlaquettes (extent + 1))) :
    slabToAmbientPhysical extent physical targetId =
      slabGeometricSpin extent physical plaquette := by
  have hlt : targetId < plaquetteEdgeCount (extent + 1) := by
    unfold plaquetteEdgeCount
    exact enumerate_index_lt hindexed
  unfold slabToAmbientPhysical
  rw [if_pos hlt, boxPlaquetteAt_eq_of_enumerate hindexed]

theorem slabToAmbientPhysical_zero_outside
    (extent : Nat) (physical : EdgeLabelling) {targetId : Nat}
    (hnot : targetId ∉
      List.range (plaquetteEdgeCount (extent + 1))) :
    slabToAmbientPhysical extent physical targetId = 0 := by
  unfold slabToAmbientPhysical
  rw [if_neg (by
    intro hlt
    exact hnot (List.mem_range.mpr hlt))]

theorem geometricSpinOfSlabToAmbient_eq_of_mem_box
    {extent : Nat} {physical : EdgeLabelling} {plaquette : Z4Plaq}
    (hmem : plaquette ∈ boxPlaquettes (extent + 1)) :
    geometricSpinOfPhysical (extent + 1)
        (slabToAmbientPhysical extent physical) plaquette =
      slabGeometricSpin extent physical plaquette := by
  obtain ⟨targetId, hindexed⟩ := exists_mem_enumerate hmem
  rw [geometricSpinOfPhysical_eq_of_enumerate hindexed,
    slabToAmbientPhysical_eq_on_enumerate hindexed]

theorem slabToAmbientPhysical_mem_bounded
    {K extent : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)) :
    slabToAmbientPhysical extent physical ∈
      boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount (extent + 1))) := by
  apply boundedEdgeLabellings_complete K
  · intro targetId htarget
    have hlt := List.mem_range.mp htarget
    unfold slabToAmbientPhysical
    rw [if_pos hlt]
    have hle := slabGeometricSpin_le_of_bounded hphysical
      (boxPlaquetteAt (extent + 1) targetId)
    omega
  · intro targetId hnot
    exact slabToAmbientPhysical_zero_outside extent physical hnot

/-! ## 2. Exact face-factor transport -/

def slabGeometricFaceFactor (w : Q') (K extent : Nat)
    (physical : EdgeLabelling) : Q' :=
  geometricFaceFactor w K (slabGeometricSpin extent physical)
    (boundaryCompleteSlabPlaquettes extent)

theorem slabParametricKPhysicalFaceFactor_eq_geometric
    (w : Q') (K extent : Nat) (physical : EdgeLabelling) :
    slabParametricKPhysicalFaceFactor w K extent physical =
      slabGeometricFaceFactor w K extent physical := by
  unfold slabParametricKPhysicalFaceFactor slabGeometricFaceFactor
    geometricFaceFactor slabPhysicalFaceEdges
  rw [← enumerate_map_fst_eq_range]
  rw [eliminateLinks_eq_listQProduct, listQProduct_map]
  have hagree :
      listQProduct
          (fun indexed : Nat × Z4Plaq =>
            coeffAt (heatKernelPacket K w) (physical indexed.1))
          (enumerate (boundaryCompleteSlabPlaquettes extent)) =
        listQProduct
          (fun indexed : Nat × Z4Plaq =>
            coeffAt (heatKernelPacket K w)
              (slabGeometricSpin extent physical indexed.2))
          (enumerate (boundaryCompleteSlabPlaquettes extent)) := by
    apply listQProduct_congr
    intro indexed hindexed
    rw [slabGeometricSpin_eq_of_enumerate hindexed]
  rw [hagree]
  rw [← listQProduct_map
    (fun plaquette : Z4Plaq =>
      coeffAt (heatKernelPacket K w)
        (slabGeometricSpin extent physical plaquette)) Prod.snd]
  rw [enumerate_map_snd]

theorem slabParametricKPhysicalFaceFactor_ambient
    (w : Q') (K extent : Nat) (physical : EdgeLabelling) :
    slabParametricKPhysicalFaceFactor w K extent physical ≈
      parametricKPhysicalFaceFactor w K (extent + 1)
        (slabToAmbientPhysical extent physical) := by
  rw [slabParametricKPhysicalFaceFactor_eq_geometric,
    parametricKPhysicalFaceFactor_eq_geometric]
  unfold slabGeometricFaceFactor geometricFaceFactor
  let targetValue : Z4Plaq → Q' := fun plaquette =>
    coeffAt (heatKernelPacket K w)
      (geometricSpinOfPhysical (extent + 1)
        (slabToAmbientPhysical extent physical) plaquette)
  let sourceValue : Z4Plaq → Q' := fun plaquette =>
    coeffAt (heatKernelPacket K w)
      (slabGeometricSpin extent physical plaquette)
  have hremove :
      listQProduct targetValue (boxPlaquettes (extent + 1)) ≈
        listQProduct targetValue
          (boundaryCompleteSlabPlaquettes extent) := by
    apply listQProduct_sublist_vacuum targetValue List.filter_sublist
      (boxPlaquettes_nodup (extent + 1))
    intro plaquette hbox hnotSlab
    unfold targetValue
    rw [geometricSpinOfSlabToAmbient_eq_of_mem_box hbox,
      slabGeometricSpin_zero_of_not_mem extent physical hnotSlab,
      coeffAt_heatKernelPacket (show 0 < K + 1 by omega),
      coeffW_zero]
    exact Q'.eqv_refl 1
  have hagree :
      listQProduct targetValue
          (boundaryCompleteSlabPlaquettes extent) =
        listQProduct sourceValue
          (boundaryCompleteSlabPlaquettes extent) := by
    apply listQProduct_congr
    intro plaquette hslab
    unfold targetValue sourceValue
    rw [geometricSpinOfSlabToAmbient_eq_of_mem_box]
    exact (mem_boundaryCompleteSlabPlaquettes extent plaquette).mp hslab |>.1
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ hremove (Q'.eqv_of_eq hagree))

/-! ## 3. Local link multiplicities -/

def slabIncidentPlaquettes (extent : Nat) (link : Z4Link) :
    List Z4Plaq :=
  (boundaryCompleteSlabPlaquettes extent).filter
    (fun plaquette => decide (link ∈ edgesOf plaquette))

theorem slabIncidentPhysicalSpins_eq_geometric
    (extent : Nat) (link : Z4Link) (physical : EdgeLabelling) :
    (slabIncidentPlaqIds extent link).map physical =
      (slabIncidentPlaquettes extent link).map
        (slabGeometricSpin extent physical) := by
  let entries := enumerate (boundaryCompleteSlabPlaquettes extent)
  let predicate : Z4Plaq → Bool := fun plaquette =>
    decide (link ∈ edgesOf plaquette)
  let selected := entries.filter (predicate ∘ Prod.snd)
  have hsnd : selected.map Prod.snd =
      (boundaryCompleteSlabPlaquettes extent).filter predicate := by
    dsimp only [selected, entries]
    rw [← List.filter_map, enumerate_map_snd]
  unfold slabIncidentPlaqIds slabIncidentPlaquettes
  change (selected.map Prod.fst).map physical = _
  rw [← hsnd]
  simp only [List.map_map]
  apply List.map_congr_left
  intro indexed hindexed
  exact (slabGeometricSpin_eq_of_enumerate
    (List.mem_filter.mp hindexed).1).symm

theorem slabIncidentPhysicalSpins_zeroExtension
    (extent : Nat) (physical : EdgeLabelling) (link : Z4Link) :
    ZeroExtension
      ((slabIncidentPlaqIds extent link).map physical)
      (incidentPhysicalSpins (extent + 1) link
        (slabToAmbientPhysical extent physical)) := by
  rw [slabIncidentPhysicalSpins_eq_geometric,
    incidentPhysicalSpins_eq_geometric]
  unfold slabIncidentPlaquettes geometricIncidentSpins
  let targetSpin := geometricSpinOfPhysical (extent + 1)
    (slabToAmbientPhysical extent physical)
  have hsourceMap :
      ((boundaryCompleteSlabPlaquettes extent).filter
          (fun plaquette => decide (link ∈ edgesOf plaquette))).map
          (slabGeometricSpin extent physical) =
        ((boundaryCompleteSlabPlaquettes extent).filter
          (fun plaquette => decide (link ∈ edgesOf plaquette))).map
          targetSpin := by
    apply List.map_congr_left
    intro plaquette hplaquette
    unfold targetSpin
    apply Eq.symm
    apply geometricSpinOfSlabToAmbient_eq_of_mem_box
    exact (mem_boundaryCompleteSlabPlaquettes extent plaquette).mp
      (List.mem_filter.mp hplaquette).1 |>.1
  rw [hsourceMap]
  apply ZeroExtension.map_of_sublist targetSpin
    (List.filter_sublist.filter
      (fun plaquette => decide (link ∈ edgesOf plaquette)))
  · exact List.filter_sublist.nodup
      (boxPlaquettes_nodup (extent + 1))
  · intro plaquette htarget hnotSource
    have htargetBox := (List.mem_filter.mp htarget).1
    have hnotSlab : plaquette ∉
        boundaryCompleteSlabPlaquettes extent := by
      intro hslab
      apply hnotSource
      exact List.mem_filter.mpr
        ⟨hslab, (List.mem_filter.mp htarget).2⟩
    unfold targetSpin
    rw [geometricSpinOfSlabToAmbient_eq_of_mem_box htargetBox,
      slabGeometricSpin_zero_of_not_mem extent physical hnotSlab]

theorem slabExplicitLinkMultiplicity_ambient
    {K extent : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)) (link : Z4Link) :
    Q'.ofNat (slabExplicitLinkMultiplicity K extent physical link) ≈
      canonicalGeometricLinkFactor K (extent + 1)
        (slabToAmbientPhysical extent physical) link := by
  unfold slabExplicitLinkMultiplicity canonicalGeometricLinkFactor
    explicitLinkMultiplicityFactor
  apply Q'.eqv_of_eq
  apply congrArg Q'.ofNat
  rw [actualExplicitMultiplicity_eq_incidentList]
  apply explicitValenceMultiplicity_zeroExtension
    (slabIncidentPhysicalSpins_zeroExtension extent physical link)
  · simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six extent link
  · simpa only [incidentPhysicalSpins, List.length_map] using
      incidentPlaqIds_length_le_six (extent + 1) link
  · intro spin hspin
    obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hspin
    exact Nat.le_trans
      (Nat.le_of_lt_succ ((boundedEdgeLabellings_sound K
        (slabPhysicalFaceEdges extent) physical hphysical).1 id
          (slabIncidentPlaqId_physical hid)))
      (externalCutoff_le_linkAuxiliaryCutoff K)

/-! ## 4. The global link product -/

theorem boundaryCompleteSlabLinks_subset_ambient
    {extent : Nat} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    link ∈ distinctBoxLinks (extent + 1) := by
  obtain ⟨plaquette, hplaquette, hboundary⟩ :=
    (mem_boundaryCompleteSlabLinks_iff extent link).mp hlink
  unfold distinctBoxLinks
  apply List.mem_eraseDups.mpr
  exact boundary_mem_boxLinks
    ((mem_boundaryCompleteSlabPlaquettes extent plaquette).mp
      hplaquette).1 hboundary

def inheritedSlabLinks (extent : Nat) : List Z4Link :=
  (distinctBoxLinks (extent + 1)).filter
    (fun link => decide (link ∈ boundaryCompleteSlabLinks extent))

theorem inheritedSlabLinks_sublist (extent : Nat) :
    inheritedSlabLinks extent <+ distinctBoxLinks (extent + 1) :=
  List.filter_sublist

theorem inheritedSlabLinks_nodup (extent : Nat) :
    (inheritedSlabLinks extent).Nodup :=
  List.filter_sublist.nodup
    (Z4SpinDependentIncidenceProductBound.distinctBoxLinks_nodup
      (extent + 1))

theorem boundaryCompleteSlabLinks_perm_inherited (extent : Nat) :
    (boundaryCompleteSlabLinks extent).Perm
      (inheritedSlabLinks extent) := by
  apply perm_of_nodup_mem_iff_constructive
    (boundaryCompleteSlabLinks extent) (inheritedSlabLinks extent)
    (boundaryCompleteSlabLinks_nodup extent)
    (inheritedSlabLinks_nodup extent)
  intro link
  unfold inheritedSlabLinks
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hlink
    exact ⟨boundaryCompleteSlabLinks_subset_ambient hlink, hlink⟩
  · exact fun hlink => hlink.2

theorem ambientLinkFactor_eq_one_of_not_slab
    (K extent : Nat) (physical : EdgeLabelling) {link : Z4Link}
    (hnew : link ∉ boundaryCompleteSlabLinks extent) :
    canonicalGeometricLinkFactor K (extent + 1)
        (slabToAmbientPhysical extent physical) link = 1 := by
  unfold canonicalGeometricLinkFactor
  apply explicitLinkMultiplicityFactor_eq_one_of_untouched
  unfold linkTouchesExcitationB
  apply (hasExcitedB_false_iff_zero_on
    (slabToAmbientPhysical extent physical)
    (incidentPlaqIds (extent + 1) link)).2
  intro targetId hincident
  obtain ⟨plaquette, hindexed, hboundary⟩ :=
    mem_incidentPlaqIds.mp hincident
  rw [slabToAmbientPhysical_eq_on_enumerate hindexed]
  by_cases hslab : plaquette ∈ boundaryCompleteSlabPlaquettes extent
  · exfalso
    apply hnew
    apply (mem_boundaryCompleteSlabLinks_iff extent link).mpr
    exact ⟨plaquette, hslab, hboundary⟩
  · exact slabGeometricSpin_zero_of_not_mem
      extent physical hslab

private theorem ofNat_natListProduct_eqv_listQProduct
    {A : Type} (value : A → Nat) : ∀ items : List A,
    Q'.ofNat (natListProduct value items) ≈
      listQProduct (fun item => Q'.ofNat (value item)) items
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      simp only [natListProduct, listQProduct]
      exact Q'.eqv_trans _
        (Q'.ofNat (value head) *
          Q'.ofNat (natListProduct value tail)) _
        (YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv
          (value head) (natListProduct value tail))
        (Q'.mul_eqv_congr_left _ _ _
          (ofNat_natListProduct_eqv_listQProduct value tail))

theorem slabExplicitLinkMultiplicityProduct_ambient
    {K extent : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)) :
    Q'.ofNat (slabExplicitLinkMultiplicityProduct
        K extent physical) ≈
      explicitLinkMultiplicityProduct K (extent + 1)
        (slabToAmbientPhysical extent physical)
        (enumerate (distinctBoxLinks (extent + 1))) := by
  rw [explicitLinkMultiplicityProduct_full_eq_canonical]
  unfold slabExplicitLinkMultiplicityProduct
    canonicalGeometricLinkProduct
  let sourceFactor : Z4Link → Q' := fun link =>
    Q'.ofNat (slabExplicitLinkMultiplicity K extent physical link)
  let targetFactor := canonicalGeometricLinkFactor K (extent + 1)
    (slabToAmbientPhysical extent physical)
  have hsource :
      Q'.ofNat
          (natListProduct
            (slabExplicitLinkMultiplicity K extent physical)
            (boundaryCompleteSlabLinks extent)) ≈
        listQProduct sourceFactor
          (boundaryCompleteSlabLinks extent) := by
    exact ofNat_natListProduct_eqv_listQProduct
      (slabExplicitLinkMultiplicity K extent physical)
      (boundaryCompleteSlabLinks extent)
  have hlocal :
      listQProduct sourceFactor
          (boundaryCompleteSlabLinks extent) ≈
        listQProduct targetFactor
          (boundaryCompleteSlabLinks extent) := by
    apply listQProduct_congr_eqv
    intro link _
    unfold sourceFactor targetFactor
    exact slabExplicitLinkMultiplicity_ambient hphysical link
  have hperm :
      listQProduct targetFactor
          (boundaryCompleteSlabLinks extent) ≈
        listQProduct targetFactor (inheritedSlabLinks extent) :=
    listQProduct_perm targetFactor
      (boundaryCompleteSlabLinks_perm_inherited extent)
  have hvacuum :
      listQProduct targetFactor
          (distinctBoxLinks (extent + 1)) ≈
        listQProduct targetFactor (inheritedSlabLinks extent) := by
    apply listQProduct_sublist_vacuum targetFactor
      (inheritedSlabLinks_sublist extent)
      (Z4SpinDependentIncidenceProductBound.distinctBoxLinks_nodup
        (extent + 1))
    intro link htarget hnotInherited
    apply Q'.eqv_of_eq
    unfold targetFactor
    apply ambientLinkFactor_eq_one_of_not_slab
    intro hslab
    apply hnotInherited
    unfold inheritedSlabLinks
    exact List.mem_filter.mpr
      ⟨htarget, by simpa only [decide_eq_true_eq]⟩
  exact Q'.eqv_trans _ _ _ hsource
    (Q'.eqv_trans _ _ _ hlocal
      (Q'.eqv_trans _ _ _ hperm (Q'.eqv_symm hvacuum)))

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- Exact equality of one corrected-slab summand with its zero-extended
ambient corner-box summand. -/
theorem slabParametricKPhysicalTerm_ambient
    (w : Q') {K extent : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)) :
    slabParametricKPhysicalTerm w K extent physical ≈
      parametricKPhysicalTerm w K (extent + 1)
        (slabToAmbientPhysical extent physical) := by
  unfold slabParametricKPhysicalTerm parametricKPhysicalTerm
  exact qmul_congr_local
    (slabParametricKPhysicalFaceFactor_ambient
      w K extent physical)
    (slabExplicitLinkMultiplicityProduct_ambient hphysical)

#print axioms slabGeometricSpin_eq_of_enumerate
#print axioms slabToAmbientPhysical_mem_bounded
#print axioms slabParametricKPhysicalFaceFactor_ambient
#print axioms slabIncidentPhysicalSpins_zeroExtension
#print axioms slabExplicitLinkMultiplicity_ambient
#print axioms boundaryCompleteSlabLinks_perm_inherited
#print axioms ambientLinkFactor_eq_one_of_not_slab
#print axioms slabExplicitLinkMultiplicityProduct_ambient
#print axioms slabParametricKPhysicalTerm_ambient

end YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
