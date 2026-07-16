/-
# Exact image of the corrected slab inside the ambient corner ensemble

The zero-extension map from the corrected slab is not merely injective.  Its
literal image is exactly the bounded ambient labellings that vanish on every
top temporal face omitted by the boundary-complete slab.  This file proves
that statement as a permutation of duplicate-free finite lists and also
records the equivalent excited-support characterization.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4UnitCubeEnumerationParity

private theorem rangeNodupLocal : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨rangeNodupLocal n,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyEq : y = n := List.mem_singleton.mp hy
      rw [hxy, hyEq] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl n)

/-! ## 1. Removed face coordinates and the supported ambient list -/

def ambientNonSlabFaceIds (extent : Nat) : List Nat :=
  (List.range (plaquetteEdgeCount (extent + 1))).filter
    (fun id => decide
      (boxPlaquetteAt (extent + 1) id ∉
        boundaryCompleteSlabPlaquettes extent))

def ambientSlabSupportedB (extent : Nat)
    (physical : EdgeLabelling) : Bool :=
  !(hasExcitedB physical (ambientNonSlabFaceIds extent))

def ambientSlabSupportedLabellings (K extent : Nat) :
    List EdgeLabelling :=
  (boundedEdgeLabellings K
    (List.range (plaquetteEdgeCount (extent + 1)))).filter
      (ambientSlabSupportedB extent)

def embeddedSlabLabellings (K extent : Nat) : List EdgeLabelling :=
  (boundedEdgeLabellings K (slabPhysicalFaceEdges extent)).map
    (slabToAmbientPhysical extent)

theorem mem_ambientNonSlabFaceIds_iff
    (extent id : Nat) :
    id ∈ ambientNonSlabFaceIds extent ↔
      id ∈ List.range (plaquetteEdgeCount (extent + 1)) ∧
        boxPlaquetteAt (extent + 1) id ∉
          boundaryCompleteSlabPlaquettes extent := by
  unfold ambientNonSlabFaceIds
  simp only [List.mem_filter, decide_eq_true_eq]

theorem ambientSlabSupportedB_true_iff_zero
    (extent : Nat) (physical : EdgeLabelling) :
    ambientSlabSupportedB extent physical = true ↔
      ∀ id, id ∈ ambientNonSlabFaceIds extent →
        physical id = 0 := by
  unfold ambientSlabSupportedB
  constructor
  · intro hnot
    have hfalse : hasExcitedB physical
        (ambientNonSlabFaceIds extent) = false := by
      cases h : hasExcitedB physical (ambientNonSlabFaceIds extent)
      · rfl
      · simp only [h, Bool.not_true] at hnot
        cases hnot
    exact (hasExcitedB_false_iff_zero_on physical _).1 hfalse
  · intro hzero
    have hfalse :=
      (hasExcitedB_false_iff_zero_on physical _).2 hzero
    rw [hfalse]
    rfl

/-! ## 2. Injectivity of slab zero extension -/

theorem slabToAmbientPhysical_injective_on
    {K extent : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent))
    (hright : right ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent))
    (heq : slabToAmbientPhysical extent left =
      slabToAmbientPhysical extent right) :
    left = right := by
  funext sourceId
  by_cases hsource : sourceId ∈ slabPhysicalFaceEdges extent
  · have hsourceIndexed := slabPlaquetteAt_mem_enumerate hsource
    have hsourceSlab := slabPlaquetteAt_mem hsource
    have hsourceBox :=
      (mem_boundaryCompleteSlabPlaquettes extent _).mp hsourceSlab |>.1
    obtain ⟨targetId, htargetIndexed⟩ :=
      exists_mem_enumerate hsourceBox
    have hleftRecover :
        slabToAmbientPhysical extent left targetId = left sourceId := by
      rw [slabToAmbientPhysical_eq_on_enumerate htargetIndexed,
        slabGeometricSpin_eq_of_enumerate hsourceIndexed]
    have hrightRecover :
        slabToAmbientPhysical extent right targetId = right sourceId := by
      rw [slabToAmbientPhysical_eq_on_enumerate htargetIndexed,
        slabGeometricSpin_eq_of_enumerate hsourceIndexed]
    have hcoordinate := congrFun heq targetId
    rw [hleftRecover, hrightRecover] at hcoordinate
    exact hcoordinate
  · have hleftSound := boundedEdgeLabellings_sound K
      (slabPhysicalFaceEdges extent) left hleft
    have hrightSound := boundedEdgeLabellings_sound K
      (slabPhysicalFaceEdges extent) right hright
    rw [hleftSound.2 sourceId hsource,
      hrightSound.2 sourceId hsource]

theorem embeddedSlabLabellings_nodup (K extent : Nat) :
    (embeddedSlabLabellings K extent).Nodup := by
  unfold embeddedSlabLabellings
  apply nodup_map_of_injOn (slabToAmbientPhysical extent)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges extent))
  · apply boundedEdgeLabellings_nodup
    unfold slabPhysicalFaceEdges
    exact rangeNodupLocal _
  · intro left hleft right hright heq
    exact slabToAmbientPhysical_injective_on hleft hright heq

theorem ambientSlabSupportedLabellings_nodup (K extent : Nat) :
    (ambientSlabSupportedLabellings K extent).Nodup := by
  unfold ambientSlabSupportedLabellings
  exact List.filter_sublist.nodup
    (boundedEdgeLabellings_nodup K _ (rangeNodupLocal _))

/-! ## 3. Every embedded slab labelling has exactly the support predicate -/

theorem slabToAmbientPhysical_supported
    (extent : Nat) (physical : EdgeLabelling) :
    ambientSlabSupportedB extent
      (slabToAmbientPhysical extent physical) = true := by
  apply (ambientSlabSupportedB_true_iff_zero extent _).2
  intro targetId htarget
  have hparts := (mem_ambientNonSlabFaceIds_iff extent targetId).1 htarget
  have hlt := List.mem_range.mp hparts.1
  unfold slabToAmbientPhysical
  rw [if_pos hlt]
  exact slabGeometricSpin_zero_of_not_mem extent physical hparts.2

theorem embeddedSlabLabellings_mem_supported
    {K extent : Nat} {target : EdgeLabelling}
    (htarget : target ∈ embeddedSlabLabellings K extent) :
    target ∈ ambientSlabSupportedLabellings K extent := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htarget
  unfold ambientSlabSupportedLabellings
  apply List.mem_filter.mpr
  exact ⟨slabToAmbientPhysical_mem_bounded hsource,
    slabToAmbientPhysical_supported extent source⟩

/-! ## 4. Explicit restriction and the ambient round trip -/

def ambientToSlabPhysical (extent : Nat)
    (target : EdgeLabelling) : EdgeLabelling :=
  fun sourceId =>
    if sourceId < (boundaryCompleteSlabPlaquettes extent).length then
      geometricSpinOfPhysical (extent + 1) target
        (slabPlaquetteAt extent sourceId)
    else 0

theorem ambientToSlabPhysical_eq_on_physical
    {extent : Nat} {target : EdgeLabelling} {sourceId : Nat}
    (hsource : sourceId ∈ slabPhysicalFaceEdges extent) :
    ambientToSlabPhysical extent target sourceId =
      geometricSpinOfPhysical (extent + 1) target
        (slabPlaquetteAt extent sourceId) := by
  unfold ambientToSlabPhysical
  rw [if_pos (slabPhysicalFaceId_lt hsource)]

theorem ambientToSlabPhysical_mem_bounded
    {K extent : Nat} {target : EdgeLabelling}
    (htarget : target ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount (extent + 1)))) :
    ambientToSlabPhysical extent target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges extent) := by
  apply boundedEdgeLabellings_complete K
  · intro sourceId hsource
    rw [ambientToSlabPhysical_eq_on_physical hsource]
    have hle := geometricSpinOfPhysical_le_of_bounded htarget
      (slabPlaquetteAt extent sourceId)
    omega
  · intro sourceId hnot
    unfold ambientToSlabPhysical
    rw [if_neg (by
      intro hlt
      apply hnot
      unfold slabPhysicalFaceEdges
      exact List.mem_range.mpr hlt)]

theorem slabToAmbientPhysical_ambientToSlab
    {K extent : Nat} {target : EdgeLabelling}
    (htarget : target ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount (extent + 1))))
    (hsupported : ambientSlabSupportedB extent target = true) :
    slabToAmbientPhysical extent
        (ambientToSlabPhysical extent target) = target := by
  have htargetSound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount (extent + 1))) target htarget
  have hzero :=
    (ambientSlabSupportedB_true_iff_zero extent target).1 hsupported
  funext targetId
  by_cases htargetId : targetId ∈
      List.range (plaquetteEdgeCount (extent + 1))
  · have htargetIndexed :
        (targetId, boxPlaquetteAt (extent + 1) targetId) ∈
          enumerate (boxPlaquettes (extent + 1)) :=
      boxPlaquetteAt_mem_enumerate (physicalFaceId_lt htargetId)
    rw [slabToAmbientPhysical_eq_on_enumerate htargetIndexed]
    by_cases hslab : boxPlaquetteAt (extent + 1) targetId ∈
        boundaryCompleteSlabPlaquettes extent
    · obtain ⟨sourceId, hsourceIndexed⟩ :=
        exists_mem_enumerate hslab
      have hsourcePhysical : sourceId ∈
          slabPhysicalFaceEdges extent := by
        unfold slabPhysicalFaceEdges
        exact List.mem_range.mpr (enumerate_index_lt hsourceIndexed)
      have hslabAt : slabPlaquetteAt extent sourceId =
          boxPlaquetteAt (extent + 1) targetId := by
        unfold slabPlaquetteAt
        exact enumerate_getD_of_mem fallbackPlaquette hsourceIndexed
      have hslabRecover :
          slabGeometricSpin extent
              (ambientToSlabPhysical extent target)
              (boxPlaquetteAt (extent + 1) targetId) =
            ambientToSlabPhysical extent target sourceId :=
        slabGeometricSpin_eq_of_enumerate hsourceIndexed
      rw [hslabRecover,
        ambientToSlabPhysical_eq_on_physical hsourcePhysical, hslabAt,
        geometricSpinOfPhysical_eq_of_enumerate htargetIndexed]
    · rw [slabGeometricSpin_zero_of_not_mem extent _ hslab]
      exact (hzero targetId
        ((mem_ambientNonSlabFaceIds_iff extent targetId).2
          ⟨htargetId, hslab⟩)).symm
  · rw [slabToAmbientPhysical_zero_outside
      extent (ambientToSlabPhysical extent target) htargetId,
      htargetSound.2 targetId htargetId]

theorem supportedLabelling_mem_embedded
    {K extent : Nat} {target : EdgeLabelling}
    (htarget : target ∈ ambientSlabSupportedLabellings K extent) :
    target ∈ embeddedSlabLabellings K extent := by
  have hparts := List.mem_filter.mp htarget
  unfold embeddedSlabLabellings
  apply List.mem_map.mpr
  refine ⟨ambientToSlabPhysical extent target,
    ambientToSlabPhysical_mem_bounded hparts.1, ?_⟩
  exact slabToAmbientPhysical_ambientToSlab hparts.1 hparts.2

/-! ## 5. Literal image permutation and support characterization -/

/-- The zero-extended corrected-slab ensemble is exactly, as a finite list,
the ambient bounded ensemble with no excitation on an omitted face. -/
theorem embeddedSlabLabellings_perm_supported (K extent : Nat) :
    (embeddedSlabLabellings K extent).Perm
      (ambientSlabSupportedLabellings K extent) := by
  apply perm_of_nodup_mem_iff_constructive
    (embeddedSlabLabellings K extent)
    (ambientSlabSupportedLabellings K extent)
    (embeddedSlabLabellings_nodup K extent)
    (ambientSlabSupportedLabellings_nodup K extent)
  intro target
  constructor
  · exact embeddedSlabLabellings_mem_supported
  · exact supportedLabelling_mem_embedded

theorem ambientSlabSupportedB_true_iff_excited_support
    (extent : Nat) (physical : EdgeLabelling) :
    ambientSlabSupportedB extent physical = true ↔
      ∀ id, id ∈ excitedPlaquetteIds (extent + 1) physical →
        boxPlaquetteAt (extent + 1) id ∈
          boundaryCompleteSlabPlaquettes extent := by
  constructor
  · intro hsupported id hid
    have hidParts := List.mem_filter.mp hid
    by_cases hslab : boxPlaquetteAt (extent + 1) id ∈
        boundaryCompleteSlabPlaquettes extent
    · exact hslab
    · have hzero :=
        (ambientSlabSupportedB_true_iff_zero extent physical).1
          hsupported id
          ((mem_ambientNonSlabFaceIds_iff extent id).2
            ⟨hidParts.1, hslab⟩)
      have hpositive : 1 ≤ physical id := by
        simpa only [decide_eq_true_eq] using hidParts.2
      omega
  · intro hsupport
    apply (ambientSlabSupportedB_true_iff_zero extent physical).2
    intro id hid
    have hidParts :=
      (mem_ambientNonSlabFaceIds_iff extent id).1 hid
    by_cases hzero : physical id = 0
    · exact hzero
    · have hpositive : 1 ≤ physical id := by omega
      have hexcited : id ∈ excitedPlaquetteIds (extent + 1) physical := by
        unfold excitedPlaquetteIds physicalFaceEdges
        exact List.mem_filter.mpr
          ⟨hidParts.1, by simpa only [decide_eq_true_eq]⟩
      exact False.elim (hidParts.2 (hsupport id hexcited))

#print axioms ambientSlabSupportedB_true_iff_zero
#print axioms slabToAmbientPhysical_injective_on
#print axioms slabToAmbientPhysical_ambientToSlab
#print axioms embeddedSlabLabellings_perm_supported
#print axioms ambientSlabSupportedB_true_iff_excited_support

end YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
