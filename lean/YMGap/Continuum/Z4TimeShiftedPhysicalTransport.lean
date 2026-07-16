/-
# Affine Euclidean-time transport of finite physical spin labellings

The old cross-volume map is a zero extension at identical Nat coordinates.
That map cannot represent a fixed signed observable when the centered chart
moves.  Here a source labelling is instead read on the literally translated
plaquette list and extended by zero to the enlarged target box.  The map is
constructive, bounded, injective on physical labellings, and transports the
exact excited support to `timeShiftCanonicalRoot`.

This is the missing affine reindex at the configuration/support level.  The
full spin-foam term and normalized-law comparison are treated separately;
no invariance of weights is assumed here.
-/

import YMGap.Continuum.Z4FiniteCylinderTimeTranslation
import YMGap.Continuum.Z4ShiftedSubboxCarrierTail
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

namespace YMGap.Continuum.Z4TimeShiftedPhysicalTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-! ## 1. Lookup on an injectively mapped finite list -/

theorem lookupLabelFrom_map_injective
    {A B : Type} [DecidableEq A] [DecidableEq B]
    (label : Nat → Nat) (mapItem : A → B)
    (hinjective : Function.Injective mapItem) :
    ∀ (start : Nat) (items : List A) (target : A),
      lookupLabelFrom label start (items.map mapItem) (mapItem target) =
        lookupLabelFrom label start items target
  | _, [], _ => rfl
  | start, head :: tail, target => by
      by_cases heq : target = head
      · subst target
        simp [lookupLabelFrom]
      · have hmapped : mapItem target ≠ mapItem head := by
          intro h
          exact heq (hinjective h)
        simp only [List.map_cons, lookupLabelFrom, if_neg heq,
          if_neg hmapped]
        exact lookupLabelFrom_map_injective label mapItem hinjective
          (start + 1) tail target

def timeShiftedPlaquetteList (shift base : Nat) : List Z4Plaq :=
  (boxPlaquettes base).map (timeShiftPlaquette shift)

theorem timeShiftedPlaquetteList_nodup (shift base : Nat) :
    (timeShiftedPlaquetteList shift base).Nodup := by
  unfold timeShiftedPlaquetteList
  exact nodup_map_of_injOn (timeShiftPlaquette shift)
    (boxPlaquettes base) (boxPlaquettes_nodup base)
    (fun _ _ _ _ heq => timeShiftPlaquette_injective shift heq)

def timeShiftedGeometricSpin (shift base : Nat)
    (physical : EdgeLabelling) (plaquette : Z4Plaq) : Nat :=
  lookupLabelFrom physical 0
    (timeShiftedPlaquetteList shift base) plaquette

theorem timeShiftedGeometricSpin_recover
    (shift base : Nat) (physical : EdgeLabelling)
    (plaquette : Z4Plaq) :
    timeShiftedGeometricSpin shift base physical
        (timeShiftPlaquette shift plaquette) =
      geometricSpinOfPhysical base physical plaquette := by
  unfold timeShiftedGeometricSpin timeShiftedPlaquetteList
    geometricSpinOfPhysical
  exact lookupLabelFrom_map_injective physical
    (timeShiftPlaquette shift) (timeShiftPlaquette_injective shift)
    0 (boxPlaquettes base) plaquette

theorem timeShiftedGeometricSpin_zero_of_not_mem
    (shift base : Nat) (physical : EdgeLabelling) {plaquette : Z4Plaq}
    (hnot : plaquette ∉ timeShiftedPlaquetteList shift base) :
    timeShiftedGeometricSpin shift base physical plaquette = 0 := by
  unfold timeShiftedGeometricSpin
  exact lookupLabelFrom_zero_of_not_mem physical 0
    (timeShiftedPlaquetteList shift base) plaquette hnot

theorem timeShiftedGeometricSpin_le_of_bounded
    {K shift base : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base)))
    (plaquette : Z4Plaq) :
    timeShiftedGeometricSpin shift base physical plaquette ≤ K := by
  by_cases hmem : plaquette ∈ timeShiftedPlaquetteList shift base
  · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
    rw [timeShiftedGeometricSpin_recover]
    exact geometricSpinOfPhysical_le_of_bounded hphysical source
  · rw [timeShiftedGeometricSpin_zero_of_not_mem
      shift base physical hmem]
    exact Nat.zero_le K

/-! ## 2. The affine physical labelling map -/

/-- Translate the source face chart by `shift` in Euclidean time and extend
by spin zero to all other faces of the enlarged corner box. -/
def timeShiftTransportPhysical (shift base : Nat)
    (physical : EdgeLabelling) : EdgeLabelling :=
  fun targetId =>
    if targetId < plaquetteEdgeCount (base + shift) then
      timeShiftedGeometricSpin shift base physical
        (boxPlaquetteAt (base + shift) targetId)
    else 0

theorem timeShiftTransportPhysical_eq_on_enumerate
    {shift base targetId : Nat} {physical : EdgeLabelling}
    {plaquette : Z4Plaq}
    (hindexed : (targetId, plaquette) ∈
      enumerate (boxPlaquettes (base + shift))) :
    timeShiftTransportPhysical shift base physical targetId =
      timeShiftedGeometricSpin shift base physical plaquette := by
  have hlt : targetId < plaquetteEdgeCount (base + shift) := by
    unfold plaquetteEdgeCount
    exact enumerate_index_lt hindexed
  unfold timeShiftTransportPhysical
  rw [if_pos hlt, boxPlaquetteAt_eq_of_enumerate hindexed]

theorem timeShiftTransportPhysical_zero_outside
    (shift base : Nat) (physical : EdgeLabelling) {targetId : Nat}
    (hnot : targetId ∉
      List.range (plaquetteEdgeCount (base + shift))) :
    timeShiftTransportPhysical shift base physical targetId = 0 := by
  unfold timeShiftTransportPhysical
  rw [if_neg (by
    intro hlt
    exact hnot (List.mem_range.mpr hlt))]

theorem geometricSpinOfTimeShiftTransport_eq_of_mem_box
    {shift base : Nat} {physical : EdgeLabelling}
    {plaquette : Z4Plaq}
    (hmem : plaquette ∈ boxPlaquettes (base + shift)) :
    geometricSpinOfPhysical (base + shift)
        (timeShiftTransportPhysical shift base physical) plaquette =
      timeShiftedGeometricSpin shift base physical plaquette := by
  obtain ⟨targetId, hindexed⟩ := exists_mem_enumerate hmem
  rw [geometricSpinOfPhysical_eq_of_enumerate hindexed,
    timeShiftTransportPhysical_eq_on_enumerate hindexed]

theorem timeShiftTransportPhysical_mem_bounded
    {K shift base : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base))) :
    timeShiftTransportPhysical shift base physical ∈
      boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount (base + shift))) := by
  apply boundedEdgeLabellings_complete K
  · intro targetId htarget
    have hlt := List.mem_range.mp htarget
    unfold timeShiftTransportPhysical
    rw [if_pos hlt]
    have hle := timeShiftedGeometricSpin_le_of_bounded
      (shift := shift) hphysical
      (boxPlaquetteAt (base + shift) targetId)
    omega
  · intro targetId hnot
    exact timeShiftTransportPhysical_zero_outside
      shift base physical hnot

/-- Every source coordinate is recovered at its translated geometric face;
hence affine transport is injective on bounded physical labellings. -/
theorem timeShiftTransportPhysical_injective_on
    {K shift base : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base)))
    (hright : right ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base)))
    (heq : timeShiftTransportPhysical shift base left =
      timeShiftTransportPhysical shift base right) :
    left = right := by
  funext sourceId
  by_cases hsource : sourceId ∈
      List.range (plaquetteEdgeCount base)
  · have hsourceBox : boxPlaquetteAt base sourceId ∈
        boxPlaquettes base :=
      boxPlaquetteAt_mem_boxPlaquettes_of_physical hsource
    have htargetBox :
        timeShiftPlaquette shift (boxPlaquetteAt base sourceId) ∈
          boxPlaquettes (base + shift) :=
      timeShiftPlaquette_mem_box_add hsourceBox
    obtain ⟨targetId, htargetIndexed⟩ :=
      exists_mem_enumerate htargetBox
    have hsourceIndexed :
        (sourceId, boxPlaquetteAt base sourceId) ∈
          enumerate (boxPlaquettes base) :=
      boxPlaquetteAt_mem_enumerate (physicalFaceId_lt hsource)
    have hleftRecover :
        timeShiftTransportPhysical shift base left targetId =
          left sourceId := by
      rw [timeShiftTransportPhysical_eq_on_enumerate htargetIndexed,
        timeShiftedGeometricSpin_recover,
        geometricSpinOfPhysical_eq_of_enumerate hsourceIndexed]
    have hrightRecover :
        timeShiftTransportPhysical shift base right targetId =
          right sourceId := by
      rw [timeShiftTransportPhysical_eq_on_enumerate htargetIndexed,
        timeShiftedGeometricSpin_recover,
        geometricSpinOfPhysical_eq_of_enumerate hsourceIndexed]
    have hcoordinate := congrFun heq targetId
    rw [hleftRecover, hrightRecover] at hcoordinate
    exact hcoordinate
  · have hleftSound := boundedEdgeLabellings_sound K
      (List.range (plaquetteEdgeCount base)) left hleft
    have hrightSound := boundedEdgeLabellings_sound K
      (List.range (plaquetteEdgeCount base)) right hright
    rw [hleftSound.2 sourceId hsource,
      hrightSound.2 sourceId hsource]

/-! ## 3. Exact support transport -/

theorem timeShiftedGeometricSpin_positive_iff_mem
    (shift base : Nat) (physical : EdgeLabelling) (plaquette : Z4Plaq) :
    1 ≤ timeShiftedGeometricSpin shift base physical plaquette ↔
      plaquette ∈
        (geometricPolymer base
          (excitedPlaquetteIds base physical)).map
            (timeShiftPlaquette shift) := by
  constructor
  · intro hpositive
    by_cases hmem : plaquette ∈ timeShiftedPlaquetteList shift base
    · obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
      rw [← heq, timeShiftedGeometricSpin_recover] at hpositive
      have hsourceExcited :=
        (geometricSpin_positive_iff_mem_geometricSupport
          base physical source).1 hpositive
      exact List.mem_map.mpr ⟨source, hsourceExcited, heq⟩
    · rw [timeShiftedGeometricSpin_zero_of_not_mem
          shift base physical hmem] at hpositive
      omega
  · intro hmem
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
    rw [← heq, timeShiftedGeometricSpin_recover]
    exact (geometricSpin_positive_iff_mem_geometricSupport
      base physical source).2 hsource

private theorem filter_eq_of_agree_local {A : Type}
    (left right : A → Bool) :
    ∀ items : List A, (∀ item, item ∈ items → left item = right item) →
      items.filter left = items.filter right
  | [], _ => rfl
  | head :: tail, hagree => by
      have hhead := hagree head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → left item = right item :=
        fun item hitem => hagree item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, hhead]
      rw [filter_eq_of_agree_local left right tail htail]

theorem excitedPlaquetteIds_timeShiftTransportPhysical
    (shift base : Nat) (physical : EdgeLabelling) :
    excitedPlaquetteIds (base + shift)
        (timeShiftTransportPhysical shift base physical) =
      timeShiftCanonicalRoot shift base
        (excitedPlaquetteIds base physical) := by
  unfold excitedPlaquetteIds timeShiftCanonicalRoot geometricSupportIds
    physicalFaceEdges
  apply filter_eq_of_agree_local
  intro targetId htarget
  have hlt := List.mem_range.mp htarget
  have htransport :
      timeShiftTransportPhysical shift base physical targetId =
        timeShiftedGeometricSpin shift base physical
          (boxPlaquetteAt (base + shift) targetId) := by
    unfold timeShiftTransportPhysical
    rw [if_pos hlt]
  rw [htransport]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using
    (timeShiftedGeometricSpin_positive_iff_mem
      shift base physical
      (boxPlaquetteAt (base + shift) targetId))

theorem timeShiftTransportPhysical_mem_supportFiber
    {cutoff shift base : Nat} {support : List Nat}
    {physical : EdgeLabelling}
    (hphysical : physical ∈
      physicalLabellingsWithSupport cutoff base support) :
    timeShiftTransportPhysical shift base physical ∈
      physicalLabellingsWithSupport cutoff (base + shift)
        (timeShiftCanonicalRoot shift base support) := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp hphysical
  apply mem_physicalLabellingsWithSupport_iff.mpr
  constructor
  · exact timeShiftTransportPhysical_mem_bounded hparts.1
  · rw [excitedPlaquetteIds_timeShiftTransportPhysical, hparts.2]

def timeShiftTransportedPhysicalFiber
    (cutoff shift base : Nat) (support : List Nat) :
    List EdgeLabelling :=
  (physicalLabellingsWithSupport cutoff base support).map
    (timeShiftTransportPhysical shift base)

theorem timeShiftTransportedPhysicalFiber_mem_target
    {cutoff shift base : Nat} {support : List Nat}
    {target : EdgeLabelling}
    (htarget : target ∈ timeShiftTransportedPhysicalFiber
      cutoff shift base support) :
    target ∈ physicalLabellingsWithSupport cutoff (base + shift)
      (timeShiftCanonicalRoot shift base support) := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htarget
  exact timeShiftTransportPhysical_mem_supportFiber hsource

theorem timeShiftTransportedPhysicalFiber_nodup
    {cutoff shift base : Nat} (support : List Nat) :
    (timeShiftTransportedPhysicalFiber
      cutoff shift base support).Nodup := by
  unfold timeShiftTransportedPhysicalFiber
  apply nodup_map_of_injOn
    (timeShiftTransportPhysical shift base)
    (physicalLabellingsWithSupport cutoff base support)
    (physicalLabellingsWithSupport_nodup cutoff base support)
  intro left hleft right hright heq
  exact timeShiftTransportPhysical_injective_on
    (mem_physicalLabellingsWithSupport_iff.mp hleft).1
    (mem_physicalLabellingsWithSupport_iff.mp hright).1 heq

#print axioms lookupLabelFrom_map_injective
#print axioms timeShiftedPlaquetteList_nodup
#print axioms timeShiftedGeometricSpin_recover
#print axioms timeShiftedGeometricSpin_le_of_bounded
#print axioms timeShiftTransportPhysical_eq_on_enumerate
#print axioms geometricSpinOfTimeShiftTransport_eq_of_mem_box
#print axioms timeShiftTransportPhysical_mem_bounded
#print axioms timeShiftTransportPhysical_injective_on
#print axioms timeShiftedGeometricSpin_positive_iff_mem
#print axioms excitedPlaquetteIds_timeShiftTransportPhysical
#print axioms timeShiftTransportPhysical_mem_supportFiber
#print axioms timeShiftTransportedPhysicalFiber_nodup

end YMGap.Continuum.Z4TimeShiftedPhysicalTransport
