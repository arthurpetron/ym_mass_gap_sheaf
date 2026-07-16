/-
# Exact support-activity covariance for affine time shifts

The affine labelling map is now upgraded from an injective embedding to a
bijection on every exact translated support fibre.  Pullback reads the target
spin at the translated source plaquette.  Exact-support target labellings are
zero off the translated face list, so pullback followed by affine transport
is the identity.  Combined with exact term invariance, this yields covariance
of the complete support activity at every coupling and representation cutoff.
-/

import YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
import YMGap.Continuum.Z4TimeShiftedPhysicalWeights

namespace YMGap.Continuum.Z4TimeShiftedSupportActivity

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
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport
open YMGap.Continuum.Z4TimeShiftedPhysicalWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pullback of a target labelling -/

def timeUnshiftPhysical (shift base : Nat)
    (target : EdgeLabelling) : EdgeLabelling :=
  fun sourceId =>
    if sourceId < plaquetteEdgeCount base then
      geometricSpinOfPhysical (base + shift) target
        (timeShiftPlaquette shift (boxPlaquetteAt base sourceId))
    else 0

theorem timeUnshiftPhysical_zero_outside
    (shift base : Nat) (target : EdgeLabelling) {sourceId : Nat}
    (hnot : sourceId ∉ List.range (plaquetteEdgeCount base)) :
    timeUnshiftPhysical shift base target sourceId = 0 := by
  unfold timeUnshiftPhysical
  rw [if_neg (by
    intro hlt
    exact hnot (List.mem_range.mpr hlt))]

theorem geometricSpinOfTimeUnshift_eq_of_mem_box
    {shift base : Nat} {target : EdgeLabelling}
    {plaquette : Z4Plaq} (hmem : plaquette ∈ boxPlaquettes base) :
    geometricSpinOfPhysical base
        (timeUnshiftPhysical shift base target) plaquette =
      geometricSpinOfPhysical (base + shift) target
        (timeShiftPlaquette shift plaquette) := by
  obtain ⟨sourceId, hindexed⟩ := exists_mem_enumerate hmem
  rw [geometricSpinOfPhysical_eq_of_enumerate hindexed]
  have hlt : sourceId < plaquetteEdgeCount base := by
    unfold plaquetteEdgeCount
    exact enumerate_index_lt hindexed
  unfold timeUnshiftPhysical
  rw [if_pos hlt, boxPlaquetteAt_eq_of_enumerate hindexed]

theorem timeUnshiftPhysical_mem_bounded
    {K shift base : Nat} {target : EdgeLabelling}
    (htarget : target ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount (base + shift)))) :
    timeUnshiftPhysical shift base target ∈
      boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount base)) := by
  apply boundedEdgeLabellings_complete K
  · intro sourceId hsource
    have hlt := List.mem_range.mp hsource
    unfold timeUnshiftPhysical
    rw [if_pos hlt]
    have hle := geometricSpinOfPhysical_le_of_bounded htarget
      (timeShiftPlaquette shift (boxPlaquetteAt base sourceId))
    omega
  · intro sourceId hnot
    exact timeUnshiftPhysical_zero_outside shift base target hnot

/-! ## 2. Translated support geometry for arbitrary cutoff-one supports -/

theorem timeShiftFaceSupport_sameSupport
    {shift base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (base + shift)
        (timeShiftCanonicalRoot shift base support))
      ((geometricPolymer base support).map
        (timeShiftPlaquette shift)) := by
  unfold timeShiftCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  exact timeShiftPlaquette_mem_box_add
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

theorem timeShiftTransportPhysical_roundtrip_of_support
    {cutoff shift base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base)
    {target : EdgeLabelling}
    (htarget : target ∈ physicalLabellingsWithSupport cutoff
      (base + shift) (timeShiftCanonicalRoot shift base support)) :
    timeShiftTransportPhysical shift base
        (timeUnshiftPhysical shift base target) = target := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp htarget
  funext targetId
  by_cases htargetId : targetId ∈
      List.range (plaquetteEdgeCount (base + shift))
  · have hindexed :
        (targetId, boxPlaquetteAt (base + shift) targetId) ∈
          enumerate (boxPlaquettes (base + shift)) :=
      boxPlaquetteAt_mem_enumerate (physicalFaceId_lt htargetId)
    rw [timeShiftTransportPhysical_eq_on_enumerate hindexed]
    by_cases hshifted : boxPlaquetteAt (base + shift) targetId ∈
        timeShiftedPlaquetteList shift base
    · obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hshifted
      have htargetGeom := geometricSpinOfPhysical_eq_of_enumerate
        (physical := target) hindexed
      rw [← heq, timeShiftedGeometricSpin_recover,
        geometricSpinOfTimeUnshift_eq_of_mem_box hsource,
        heq, htargetGeom]
    · rw [timeShiftedGeometricSpin_zero_of_not_mem
        shift base (timeUnshiftPhysical shift base target) hshifted]
      have hgeomZero :
          geometricSpinOfPhysical (base + shift) target
            (boxPlaquetteAt (base + shift) targetId) = 0 := by
        by_cases hzero : geometricSpinOfPhysical (base + shift) target
            (boxPlaquetteAt (base + shift) targetId) = 0
        · exact hzero
        · have hpositive : 1 ≤
              geometricSpinOfPhysical (base + shift) target
                (boxPlaquetteAt (base + shift) targetId) := by omega
          have hgeom :=
            (geometricSpin_positive_iff_mem_geometricSupport
              (base + shift) target
              (boxPlaquetteAt (base + shift) targetId)).1 hpositive
          rw [hparts.2] at hgeom
          have hmapped :=
            (timeShiftFaceSupport_sameSupport hsupport).1 _ hgeom
          apply False.elim
          apply hshifted
          obtain ⟨source, hsourceGeom, heq⟩ := List.mem_map.mp hmapped
          unfold timeShiftedPlaquetteList
          exact List.mem_map.mpr
            ⟨source,
              geometricPolymer_subset_box hsupport source hsourceGeom,
              heq⟩
      have htargetGeom := geometricSpinOfPhysical_eq_of_enumerate
        (physical := target) hindexed
      rw [hgeomZero] at htargetGeom
      exact htargetGeom
  · rw [timeShiftTransportPhysical_zero_outside
      shift base (timeUnshiftPhysical shift base target) htargetId]
    exact (boundedEdgeLabellings_sound cutoff
      (List.range (plaquetteEdgeCount (base + shift))) target hparts.1).2
        targetId htargetId |>.symm

theorem timeUnshiftPhysical_mem_sourceFiber
    {cutoff shift base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base)
    {target : EdgeLabelling}
    (htarget : target ∈ physicalLabellingsWithSupport cutoff
      (base + shift) (timeShiftCanonicalRoot shift base support)) :
    timeUnshiftPhysical shift base target ∈
      physicalLabellingsWithSupport cutoff base support := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp htarget
  let source := timeUnshiftPhysical shift base target
  have hsourceBounded : source ∈ boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount base)) :=
    timeUnshiftPhysical_mem_bounded hparts.1
  have hroundtrip :
      timeShiftTransportPhysical shift base source = target :=
    timeShiftTransportPhysical_roundtrip_of_support hsupport htarget
  have htranslated :
      timeShiftCanonicalRoot shift base
          (excitedPlaquetteIds base source) =
        timeShiftCanonicalRoot shift base support := by
    rw [← excitedPlaquetteIds_timeShiftTransportPhysical,
      hroundtrip, hparts.2]
  have hexcited : excitedPlaquetteIds base source ∈
      cutoffOneFaceSupports base :=
    excitedPlaquetteIds_mem_cutoffOneFaceSupports base source
  have hleft := timeShiftFaceSupport_sameSupport
    (shift := shift) hexcited
  have hright := timeShiftFaceSupport_sameSupport
    (shift := shift) hsupport
  rw [htranslated] at hleft
  have hmapped : sameSupport (L := z4Chain.toLattice)
      ((geometricPolymer base (excitedPlaquetteIds base source)).map
        (timeShiftPlaquette shift))
      ((geometricPolymer base support).map
        (timeShiftPlaquette shift)) :=
    sameSupport_trans (sameSupport_symm hleft) hright
  have horiginal := sameSupport_of_map_injective_local
    (timeShiftPlaquette_injective shift) hmapped
  have hsupportEq : excitedPlaquetteIds base source = support :=
    faceSupport_eq_of_geometric_sameSupport
      hexcited hsupport horiginal
  apply mem_physicalLabellingsWithSupport_iff.mpr
  exact ⟨hsourceBounded, hsupportEq⟩

/-! ## 4. Fibre permutation and support-activity covariance -/

theorem targetFiber_mem_timeShiftTransported
    {cutoff shift base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base)
    {target : EdgeLabelling}
    (htarget : target ∈ physicalLabellingsWithSupport cutoff
      (base + shift) (timeShiftCanonicalRoot shift base support)) :
    target ∈ timeShiftTransportedPhysicalFiber
      cutoff shift base support := by
  unfold timeShiftTransportedPhysicalFiber
  apply List.mem_map.mpr
  exact ⟨timeUnshiftPhysical shift base target,
    timeUnshiftPhysical_mem_sourceFiber hsupport htarget,
    timeShiftTransportPhysical_roundtrip_of_support hsupport htarget⟩

theorem timeShiftTransportedPhysicalFiber_perm_target
    {cutoff shift base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base) :
    (timeShiftTransportedPhysicalFiber
        cutoff shift base support).Perm
      (physicalLabellingsWithSupport cutoff (base + shift)
        (timeShiftCanonicalRoot shift base support)) := by
  apply perm_of_nodup_mem_iff_constructive
    (timeShiftTransportedPhysicalFiber cutoff shift base support)
    (physicalLabellingsWithSupport cutoff (base + shift)
      (timeShiftCanonicalRoot shift base support))
    (timeShiftTransportedPhysicalFiber_nodup support)
    (physicalLabellingsWithSupport_nodup cutoff (base + shift)
      (timeShiftCanonicalRoot shift base support))
  intro target
  constructor
  · exact timeShiftTransportedPhysicalFiber_mem_target
  · exact targetFiber_mem_timeShiftTransported hsupport

def couplingTimeShiftTransportedKSupportActivity
    (coupling : Q') (cutoff shift base : Nat)
    (support : List Nat) : Q' :=
  listQSum (parametricKPhysicalTerm coupling cutoff (base + shift))
    (timeShiftTransportedPhysicalFiber cutoff shift base support)

theorem couplingParametricKSupportActivity_eqv_timeShiftTransported
    (coupling : Q') (cutoff shift base : Nat) (support : List Nat) :
    couplingParametricKSupportActivity coupling cutoff base support ≈
      couplingTimeShiftTransportedKSupportActivity
        coupling cutoff shift base support := by
  unfold couplingParametricKSupportActivity
    couplingTimeShiftTransportedKSupportActivity
    timeShiftTransportedPhysicalFiber
  apply listQSum_map_eqv
  intro physical hphysical
  exact parametricKPhysicalTerm_timeShift coupling
    (mem_physicalLabellingsWithSupport_iff.mp hphysical).1

/-- Exact arbitrary-coupling support-activity covariance for the genuinely
translated support, not the old identical-coordinate zero extension. -/
theorem couplingParametricKSupportActivity_timeShift
    (coupling : Q') {cutoff shift base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base) :
    couplingParametricKSupportActivity coupling cutoff base support ≈
      couplingParametricKSupportActivity coupling cutoff (base + shift)
        (timeShiftCanonicalRoot shift base support) := by
  refine Q'.eqv_trans _
    (couplingTimeShiftTransportedKSupportActivity
      coupling cutoff shift base support) _
    (couplingParametricKSupportActivity_eqv_timeShiftTransported
      coupling cutoff shift base support) ?_
  unfold couplingTimeShiftTransportedKSupportActivity
    couplingParametricKSupportActivity
  exact Z4CanonicalPolymerRange.listQSum_perm
    (parametricKPhysicalTerm coupling cutoff (base + shift))
    (timeShiftTransportedPhysicalFiber_perm_target hsupport)

#print axioms geometricSpinOfTimeUnshift_eq_of_mem_box
#print axioms timeUnshiftPhysical_mem_bounded
#print axioms timeShiftFaceSupport_sameSupport
#print axioms timeShiftTransportPhysical_roundtrip_of_support
#print axioms timeUnshiftPhysical_mem_sourceFiber
#print axioms targetFiber_mem_timeShiftTransported
#print axioms timeShiftTransportedPhysicalFiber_perm_target
#print axioms couplingParametricKSupportActivity_eqv_timeShiftTransported
#print axioms couplingParametricKSupportActivity_timeShift

end YMGap.Continuum.Z4TimeShiftedSupportActivity
