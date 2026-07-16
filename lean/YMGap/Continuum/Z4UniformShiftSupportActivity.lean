/-
# Exact support-activity covariance for uniform four-coordinate shifts

The uniformly padded affine labelling map is now upgraded from an injective embedding to a
bijection on every exact uniformly translated support fibre.  Pullback reads the target
spin at the uniformly translated source plaquette.  Exact-support target labellings are
zero off the uniformly translated face list, so pullback followed by affine transport
is the identity.  Combined with exact term invariance, this yields covariance
of the complete support activity at every coupling and representation cutoff in the symmetrically padded box.
-/

import YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
import YMGap.Continuum.Z4UniformShiftPhysicalWeights

namespace YMGap.Continuum.Z4UniformShiftSupportActivity

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportPartition
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4UniformShiftPhysicalWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pullback of a target labelling -/

def uniformUnshiftPhysical (padding base : Nat)
    (target : EdgeLabelling) : EdgeLabelling :=
  fun sourceId =>
    if sourceId < plaquetteEdgeCount base then
      geometricSpinOfPhysical (uniformPaddedBase padding base) target
        (uniformShiftPlaquette padding (boxPlaquetteAt base sourceId))
    else 0

theorem uniformUnshiftPhysical_zero_outside
    (padding base : Nat) (target : EdgeLabelling) {sourceId : Nat}
    (hnot : sourceId ∉ List.range (plaquetteEdgeCount base)) :
    uniformUnshiftPhysical padding base target sourceId = 0 := by
  unfold uniformUnshiftPhysical
  rw [if_neg (by
    intro hlt
    exact hnot (List.mem_range.mpr hlt))]

theorem geometricSpinOfUniformUnshift_eq_of_mem_box
    {padding base : Nat} {target : EdgeLabelling}
    {plaquette : Z4Plaq} (hmem : plaquette ∈ boxPlaquettes base) :
    geometricSpinOfPhysical base
        (uniformUnshiftPhysical padding base target) plaquette =
      geometricSpinOfPhysical (uniformPaddedBase padding base) target
        (uniformShiftPlaquette padding plaquette) := by
  obtain ⟨sourceId, hindexed⟩ := exists_mem_enumerate hmem
  rw [geometricSpinOfPhysical_eq_of_enumerate hindexed]
  have hlt : sourceId < plaquetteEdgeCount base := by
    unfold plaquetteEdgeCount
    exact enumerate_index_lt hindexed
  unfold uniformUnshiftPhysical
  rw [if_pos hlt, boxPlaquetteAt_eq_of_enumerate hindexed]

theorem uniformUnshiftPhysical_mem_bounded
    {K padding base : Nat} {target : EdgeLabelling}
    (htarget : target ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount (uniformPaddedBase padding base)))) :
    uniformUnshiftPhysical padding base target ∈
      boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount base)) := by
  apply boundedEdgeLabellings_complete K
  · intro sourceId hsource
    have hlt := List.mem_range.mp hsource
    unfold uniformUnshiftPhysical
    rw [if_pos hlt]
    have hle := geometricSpinOfPhysical_le_of_bounded htarget
      (uniformShiftPlaquette padding (boxPlaquetteAt base sourceId))
    omega
  · intro sourceId hnot
    exact uniformUnshiftPhysical_zero_outside padding base target hnot

/-! ## 2. Translated support geometry for arbitrary cutoff-one supports -/

theorem uniformShiftFaceSupport_sameSupport
    {padding base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (uniformPaddedBase padding base)
        (uniformShiftCanonicalRoot padding base support))
      ((geometricPolymer base support).map
        (uniformShiftPlaquette padding)) := by
  unfold uniformShiftCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  exact uniformShiftPlaquette_mem_padded_box
    (geometricPolymer_subset_box hsupport source hsource)

private theorem sameSupport_of_map_injective_local
    {left right : List Z4Plaq} {mapP : Z4Plaq → Z4Plaq}
    (hinjective : Function.Injective mapP)
    (h : sameSupport (L := z4Chain.toLattice)
      (left.map mapP) (right.map mapP)) :
    sameSupport (L := z4Chain.toLattice) left right := by
  constructor
  · intro plaquette hplaquette
    have hmapped : mapP plaquette ∈ left.map mapP :=
      List.mem_map.mpr ⟨plaquette, hplaquette, rfl⟩
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp (h.1 _ hmapped)
    have hid : source = plaquette := hinjective heq
    simpa only [hid] using hsource
  · intro plaquette hplaquette
    have hmapped : mapP plaquette ∈ right.map mapP :=
      List.mem_map.mpr ⟨plaquette, hplaquette, rfl⟩
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp (h.2 _ hmapped)
    have hid : source = plaquette := hinjective heq
    simpa only [hid] using hsource

/-! ## 3. Exact round trip on a translated support fibre -/

theorem uniformShiftTransportPhysical_roundtrip_of_support
    {cutoff padding base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base)
    {target : EdgeLabelling}
    (htarget : target ∈ physicalLabellingsWithSupport cutoff
      (uniformPaddedBase padding base) (uniformShiftCanonicalRoot padding base support)) :
    uniformShiftTransportPhysical padding base
        (uniformUnshiftPhysical padding base target) = target := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp htarget
  funext targetId
  by_cases htargetId : targetId ∈
      List.range (plaquetteEdgeCount (uniformPaddedBase padding base))
  · have hindexed :
        (targetId, boxPlaquetteAt (uniformPaddedBase padding base) targetId) ∈
          enumerate (boxPlaquettes (uniformPaddedBase padding base)) :=
      boxPlaquetteAt_mem_enumerate (physicalFaceId_lt htargetId)
    rw [uniformShiftTransportPhysical_eq_on_enumerate hindexed]
    by_cases hshifted : boxPlaquetteAt (uniformPaddedBase padding base) targetId ∈
        uniformShiftedPlaquetteList padding base
    · obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hshifted
      have htargetGeom := geometricSpinOfPhysical_eq_of_enumerate
        (physical := target) hindexed
      rw [← heq, uniformShiftedGeometricSpin_recover,
        geometricSpinOfUniformUnshift_eq_of_mem_box hsource,
        heq, htargetGeom]
    · rw [uniformShiftedGeometricSpin_zero_of_not_mem
        padding base (uniformUnshiftPhysical padding base target) hshifted]
      have hgeomZero :
          geometricSpinOfPhysical (uniformPaddedBase padding base) target
            (boxPlaquetteAt (uniformPaddedBase padding base) targetId) = 0 := by
        by_cases hzero : geometricSpinOfPhysical (uniformPaddedBase padding base) target
            (boxPlaquetteAt (uniformPaddedBase padding base) targetId) = 0
        · exact hzero
        · have hpositive : 1 ≤
              geometricSpinOfPhysical (uniformPaddedBase padding base) target
                (boxPlaquetteAt (uniformPaddedBase padding base) targetId) := by omega
          have hgeom :=
            (geometricSpin_positive_iff_mem_geometricSupport
              (uniformPaddedBase padding base) target
              (boxPlaquetteAt (uniformPaddedBase padding base) targetId)).1 hpositive
          rw [hparts.2] at hgeom
          have hmapped :=
            (uniformShiftFaceSupport_sameSupport hsupport).1 _ hgeom
          apply False.elim
          apply hshifted
          obtain ⟨source, hsourceGeom, heq⟩ := List.mem_map.mp hmapped
          unfold uniformShiftedPlaquetteList
          exact List.mem_map.mpr
            ⟨source,
              geometricPolymer_subset_box hsupport source hsourceGeom,
              heq⟩
      have htargetGeom := geometricSpinOfPhysical_eq_of_enumerate
        (physical := target) hindexed
      rw [hgeomZero] at htargetGeom
      exact htargetGeom
  · rw [uniformShiftTransportPhysical_zero_outside
      padding base (uniformUnshiftPhysical padding base target) htargetId]
    exact (boundedEdgeLabellings_sound cutoff
      (List.range (plaquetteEdgeCount (uniformPaddedBase padding base))) target hparts.1).2
        targetId htargetId |>.symm

theorem uniformUnshiftPhysical_mem_sourceFiber
    {cutoff padding base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base)
    {target : EdgeLabelling}
    (htarget : target ∈ physicalLabellingsWithSupport cutoff
      (uniformPaddedBase padding base) (uniformShiftCanonicalRoot padding base support)) :
    uniformUnshiftPhysical padding base target ∈
      physicalLabellingsWithSupport cutoff base support := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp htarget
  let source := uniformUnshiftPhysical padding base target
  have hsourceBounded : source ∈ boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount base)) :=
    uniformUnshiftPhysical_mem_bounded hparts.1
  have hroundtrip :
      uniformShiftTransportPhysical padding base source = target :=
    uniformShiftTransportPhysical_roundtrip_of_support hsupport htarget
  have htranslated :
      uniformShiftCanonicalRoot padding base
          (excitedPlaquetteIds base source) =
        uniformShiftCanonicalRoot padding base support := by
    rw [← excitedPlaquetteIds_uniformShiftTransportPhysical,
      hroundtrip, hparts.2]
  have hexcited : excitedPlaquetteIds base source ∈
      cutoffOneFaceSupports base :=
    excitedPlaquetteIds_mem_cutoffOneFaceSupports base source
  have hleft := uniformShiftFaceSupport_sameSupport
    (padding := padding) hexcited
  have hright := uniformShiftFaceSupport_sameSupport
    (padding := padding) hsupport
  rw [htranslated] at hleft
  have hmapped : sameSupport (L := z4Chain.toLattice)
      ((geometricPolymer base (excitedPlaquetteIds base source)).map
        (uniformShiftPlaquette padding))
      ((geometricPolymer base support).map
        (uniformShiftPlaquette padding)) :=
    sameSupport_trans (sameSupport_symm hleft) hright
  have horiginal := sameSupport_of_map_injective_local
    (uniformShiftPlaquette_injective padding) hmapped
  have hsupportEq : excitedPlaquetteIds base source = support :=
    faceSupport_eq_of_geometric_sameSupport
      hexcited hsupport horiginal
  apply mem_physicalLabellingsWithSupport_iff.mpr
  exact ⟨hsourceBounded, hsupportEq⟩

/-! ## 4. Fibre permutation and support-activity covariance -/

theorem targetFiber_mem_uniformShiftTransported
    {cutoff padding base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base)
    {target : EdgeLabelling}
    (htarget : target ∈ physicalLabellingsWithSupport cutoff
      (uniformPaddedBase padding base) (uniformShiftCanonicalRoot padding base support)) :
    target ∈ uniformShiftTransportedPhysicalFiber
      cutoff padding base support := by
  unfold uniformShiftTransportedPhysicalFiber
  apply List.mem_map.mpr
  exact ⟨uniformUnshiftPhysical padding base target,
    uniformUnshiftPhysical_mem_sourceFiber hsupport htarget,
    uniformShiftTransportPhysical_roundtrip_of_support hsupport htarget⟩

theorem uniformShiftTransportedPhysicalFiber_perm_target
    {cutoff padding base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base) :
    (uniformShiftTransportedPhysicalFiber
        cutoff padding base support).Perm
      (physicalLabellingsWithSupport cutoff (uniformPaddedBase padding base)
        (uniformShiftCanonicalRoot padding base support)) := by
  apply perm_of_nodup_mem_iff_constructive
    (uniformShiftTransportedPhysicalFiber cutoff padding base support)
    (physicalLabellingsWithSupport cutoff (uniformPaddedBase padding base)
      (uniformShiftCanonicalRoot padding base support))
    (uniformShiftTransportedPhysicalFiber_nodup support)
    (physicalLabellingsWithSupport_nodup cutoff (uniformPaddedBase padding base)
      (uniformShiftCanonicalRoot padding base support))
  intro target
  constructor
  · exact uniformShiftTransportedPhysicalFiber_mem_target
  · exact targetFiber_mem_uniformShiftTransported hsupport

def couplingUniformShiftTransportedKSupportActivity
    (coupling : Q') (cutoff padding base : Nat)
    (support : List Nat) : Q' :=
  listQSum (parametricKPhysicalTerm coupling cutoff (uniformPaddedBase padding base))
    (uniformShiftTransportedPhysicalFiber cutoff padding base support)

theorem couplingParametricKSupportActivity_eqv_uniformShiftTransported
    (coupling : Q') (cutoff padding base : Nat) (support : List Nat) :
    couplingParametricKSupportActivity coupling cutoff base support ≈
      couplingUniformShiftTransportedKSupportActivity
        coupling cutoff padding base support := by
  unfold couplingParametricKSupportActivity
    couplingUniformShiftTransportedKSupportActivity
    uniformShiftTransportedPhysicalFiber
  apply listQSum_map_eqv
  intro physical hphysical
  exact parametricKPhysicalTerm_uniformShift coupling
    (mem_physicalLabellingsWithSupport_iff.mp hphysical).1

/-- Exact arbitrary-coupling support-activity covariance for the genuinely
translated support, not the old identical-coordinate zero extension. -/
theorem couplingParametricKSupportActivity_uniformShift
    (coupling : Q') {cutoff padding base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base) :
    couplingParametricKSupportActivity coupling cutoff base support ≈
      couplingParametricKSupportActivity coupling cutoff (uniformPaddedBase padding base)
        (uniformShiftCanonicalRoot padding base support) := by
  refine Q'.eqv_trans _
    (couplingUniformShiftTransportedKSupportActivity
      coupling cutoff padding base support) _
    (couplingParametricKSupportActivity_eqv_uniformShiftTransported
      coupling cutoff padding base support) ?_
  unfold couplingUniformShiftTransportedKSupportActivity
    couplingParametricKSupportActivity
  exact Z4CanonicalPolymerRange.listQSum_perm
    (parametricKPhysicalTerm coupling cutoff (uniformPaddedBase padding base))
    (uniformShiftTransportedPhysicalFiber_perm_target hsupport)

#print axioms geometricSpinOfUniformUnshift_eq_of_mem_box
#print axioms uniformUnshiftPhysical_mem_bounded
#print axioms uniformShiftFaceSupport_sameSupport
#print axioms uniformShiftTransportPhysical_roundtrip_of_support
#print axioms uniformUnshiftPhysical_mem_sourceFiber
#print axioms targetFiber_mem_uniformShiftTransported
#print axioms uniformShiftTransportedPhysicalFiber_perm_target
#print axioms couplingParametricKSupportActivity_eqv_uniformShiftTransported
#print axioms couplingParametricKSupportActivity_uniformShift

end YMGap.Continuum.Z4UniformShiftSupportActivity
