/-
# Spin-decorated cross-volume locality

This file upgrades ordered box nesting to arbitrary finite representation
cutoffs.  A smaller-box physical face labelling is read geometrically and
extended by spin zero to every new face of a larger box.  For each fixed
geometric link, the larger incident-spin sequence is then an ordered zero
extension of the smaller sequence.  Vacuum-insertion invariance gives exact
equality of the two explicit local fusion multiplicities.
-/

import YMGap.Continuum.Z4FusionPathZeroInsertion
import YMGap.Continuum.Z4CanonicalPolymerTransport
import YMGap.Continuum.Z4SpinSummedFaceActivityBound

namespace YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-! ## 1. Choice-free lookup of a numerical label by geometric face -/

def lookupLabelFrom {A : Type} [DecidableEq A]
    (label : Nat → Nat) : Nat → List A → A → Nat
  | _, [], _ => 0
  | start, head :: tail, target =>
      if target = head then label start
      else lookupLabelFrom label (start + 1) tail target

theorem lookupLabelFrom_zero_of_not_mem {A : Type} [DecidableEq A]
    (label : Nat → Nat) : ∀ (start : Nat) (xs : List A) (target : A),
    target ∉ xs → lookupLabelFrom label start xs target = 0
  | _, [], _, _ => rfl
  | start, head :: tail, target, hnot => by
      have hne : target ≠ head := by
        intro heq
        apply hnot
        subst target
        exact List.mem_cons_self
      have htail : target ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      simp only [lookupLabelFrom, if_neg hne]
      exact lookupLabelFrom_zero_of_not_mem label (start + 1)
        tail target htail

theorem lookupLabelFrom_eq_of_mem_enumerateFrom
    {A : Type} [DecidableEq A] (label : Nat → Nat) :
    ∀ {start : Nat} {xs : List A}, xs.Nodup →
    ∀ {index : Nat} {item : A},
      (index, item) ∈ enumerateFrom start xs →
      lookupLabelFrom label start xs item = label index
  | _, [], _, _, _, hmem => by cases hmem
  | start, head :: tail, hnodup, index, item, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      simp only [enumerateFrom, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · have hindex : index = start := congrArg Prod.fst hhead
        have hitem : item = head := congrArg Prod.snd hhead
        subst index
        subst item
        simp [lookupLabelFrom]
      · have hitemTail : item ∈ tail := by
          have hmapped : item ∈
              (enumerateFrom (start + 1) tail).map Prod.snd :=
            List.mem_map.mpr ⟨(index, item), htail, rfl⟩
          rw [enumerateFrom_map_snd] at hmapped
          exact hmapped
        have hne : item ≠ head := by
          intro heq
          subst item
          exact hparts.1 hitemTail
        simp only [lookupLabelFrom, if_neg hne]
        exact lookupLabelFrom_eq_of_mem_enumerateFrom label hparts.2 htail

def geometricSpinOfPhysical (n : Nat) (physical : EdgeLabelling)
    (plaquette : Z4Plaq) : Nat :=
  lookupLabelFrom physical 0 (boxPlaquettes n) plaquette

theorem geometricSpinOfPhysical_eq_of_enumerate
    {n index : Nat} {physical : EdgeLabelling} {plaquette : Z4Plaq}
    (hindexed : (index, plaquette) ∈ enumerate (boxPlaquettes n)) :
    geometricSpinOfPhysical n physical plaquette = physical index := by
  exact lookupLabelFrom_eq_of_mem_enumerateFrom physical
    (boxPlaquettes_nodup n) hindexed

theorem geometricSpinOfPhysical_zero_of_not_mem
    (n : Nat) (physical : EdgeLabelling) {plaquette : Z4Plaq}
    (hnot : plaquette ∉ boxPlaquettes n) :
    geometricSpinOfPhysical n physical plaquette = 0 :=
  lookupLabelFrom_zero_of_not_mem physical 0
    (boxPlaquettes n) plaquette hnot

/-! ## 2. Incident numerical spins equal incident geometric spins -/

def incidentPhysicalSpins (n : Nat) (ell : Z4Link)
    (physical : EdgeLabelling) : List Nat :=
  (incidentPlaqIds n ell).map physical

theorem incidentPhysicalSpins_eq_geometric
    (n : Nat) (ell : Z4Link) (physical : EdgeLabelling) :
    incidentPhysicalSpins n ell physical =
      geometricIncidentSpins n ell
        (geometricSpinOfPhysical n physical) := by
  let entries := enumerate (boxPlaquettes n)
  let pred : Z4Plaq → Bool := fun p => decide (ell ∈ edgesOf p)
  let selected := entries.filter (pred ∘ Prod.snd)
  have hsnd : selected.map Prod.snd =
      (boxPlaquettes n).filter pred := by
    dsimp only [selected, entries]
    rw [← List.filter_map, enumerate_map_snd]
  unfold incidentPhysicalSpins incidentPlaqIds geometricIncidentSpins
  change (selected.map Prod.fst).map physical = _
  rw [← hsnd]
  simp only [List.map_map]
  apply List.map_congr_left
  intro indexed hindexed
  exact (geometricSpinOfPhysical_eq_of_enumerate
    (List.mem_filter.mp hindexed).1).symm

/-! ## 3. The literal smaller-box embedding -/

def transportPhysical (small large : Nat)
    (physical : EdgeLabelling) : EdgeLabelling :=
  fun targetId =>
    if targetId < plaquetteEdgeCount large then
      geometricSpinOfPhysical small physical
        (boxPlaquetteAt large targetId)
    else 0

theorem transportPhysical_eq_on_enumerate
    {small large targetId : Nat} {physical : EdgeLabelling}
    {plaquette : Z4Plaq}
    (hindexed : (targetId, plaquette) ∈
      enumerate (boxPlaquettes large)) :
    transportPhysical small large physical targetId =
      geometricSpinOfPhysical small physical plaquette := by
  have hlt : targetId < plaquetteEdgeCount large := by
    unfold plaquetteEdgeCount
    exact enumerate_index_lt hindexed
  unfold transportPhysical
  rw [if_pos hlt, boxPlaquetteAt_eq_of_enumerate hindexed]

theorem transportPhysical_zero_outside
    (small large : Nat) (physical : EdgeLabelling) {targetId : Nat}
    (hnot : targetId ∉ List.range (plaquetteEdgeCount large)) :
    transportPhysical small large physical targetId = 0 := by
  unfold transportPhysical
  rw [if_neg (by
    intro hlt
    exact hnot (List.mem_range.mpr hlt))]

theorem geometricSpinOfTransport_eq_of_mem_box
    {small large : Nat} {physical : EdgeLabelling}
    {plaquette : Z4Plaq} (hmem : plaquette ∈ boxPlaquettes large) :
    geometricSpinOfPhysical large
        (transportPhysical small large physical) plaquette =
      geometricSpinOfPhysical small physical plaquette := by
  obtain ⟨targetId, hindexed⟩ := exists_mem_enumerate hmem
  rw [geometricSpinOfPhysical_eq_of_enumerate hindexed,
    transportPhysical_eq_on_enumerate hindexed]

theorem geometricSpinOfPhysical_le_of_bounded
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)))
    (plaquette : Z4Plaq) :
    geometricSpinOfPhysical n physical plaquette ≤ K := by
  by_cases hmem : plaquette ∈ boxPlaquettes n
  · obtain ⟨index, hindexed⟩ := exists_mem_enumerate hmem
    rw [geometricSpinOfPhysical_eq_of_enumerate hindexed]
    have hsound := boundedEdgeLabellings_sound K
      (List.range (plaquetteEdgeCount n)) physical hphysical
    have hindexRange : index ∈ List.range (plaquetteEdgeCount n) := by
      unfold plaquetteEdgeCount
      exact List.mem_range.mpr (enumerate_index_lt hindexed)
    have hlt := hsound.1 index hindexRange
    omega
  · rw [geometricSpinOfPhysical_zero_of_not_mem n physical hmem]
    exact Nat.zero_le K

theorem transportPhysical_mem_bounded
    {K small large : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount small))) :
    transportPhysical small large physical ∈
      boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount large)) := by
  apply boundedEdgeLabellings_complete K
  · intro targetId htarget
    have hlt := List.mem_range.mp htarget
    unfold transportPhysical
    rw [if_pos hlt]
    have hle := geometricSpinOfPhysical_le_of_bounded
      hphysical (boxPlaquetteAt large targetId)
    omega
  · intro targetId hnot
    exact transportPhysical_zero_outside small large physical hnot

/-- Zero extension into a larger box is injective on the bounded physical
labellings of the smaller box.  The proof recovers every source coordinate
through the geometric plaquette shared by the two enumerations. -/
theorem transportPhysical_injective_on
    {K small large : Nat} (hsmall : small ≤ large)
    {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount small)))
    (hright : right ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount small)))
    (heq : transportPhysical small large left =
      transportPhysical small large right) :
    left = right := by
  funext sourceId
  by_cases hsource : sourceId ∈
      List.range (plaquetteEdgeCount small)
  · have hsourceBox : boxPlaquetteAt small sourceId ∈
        boxPlaquettes small :=
      boxPlaquetteAt_mem_boxPlaquettes_of_physical hsource
    have htargetBox : boxPlaquetteAt small sourceId ∈
        boxPlaquettes large :=
      boxPlaquettes_mono hsmall hsourceBox
    obtain ⟨targetId, htargetIndexed⟩ :=
      exists_mem_enumerate htargetBox
    have hsourceIndexed :
        (sourceId, boxPlaquetteAt small sourceId) ∈
          enumerate (boxPlaquettes small) :=
      boxPlaquetteAt_mem_enumerate (physicalFaceId_lt hsource)
    have hleftRecover :
        transportPhysical small large left targetId = left sourceId := by
      rw [transportPhysical_eq_on_enumerate htargetIndexed,
        geometricSpinOfPhysical_eq_of_enumerate hsourceIndexed]
    have hrightRecover :
        transportPhysical small large right targetId = right sourceId := by
      rw [transportPhysical_eq_on_enumerate htargetIndexed,
        geometricSpinOfPhysical_eq_of_enumerate hsourceIndexed]
    have hcoordinate := congrFun heq targetId
    rw [hleftRecover, hrightRecover] at hcoordinate
    exact hcoordinate
  · have hleftSound := boundedEdgeLabellings_sound K
      (List.range (plaquetteEdgeCount small)) left hleft
    have hrightSound := boundedEdgeLabellings_sound K
      (List.range (plaquetteEdgeCount small)) right hright
    rw [hleftSound.2 sourceId hsource,
      hrightSound.2 sourceId hsource]

/-! ## 3a. Exact support transport -/

theorem geometricSpin_positive_iff_mem_geometricSupport
    (n : Nat) (physical : EdgeLabelling) (plaquette : Z4Plaq) :
    1 ≤ geometricSpinOfPhysical n physical plaquette ↔
      plaquette ∈ geometricPolymer n
        (excitedPlaquetteIds n physical) := by
  constructor
  · intro hpositive
    by_cases hmem : plaquette ∈ boxPlaquettes n
    · obtain ⟨index, hindexed⟩ := exists_mem_enumerate hmem
      have hvalue := geometricSpinOfPhysical_eq_of_enumerate
        (physical := physical) hindexed
      unfold geometricPolymer
      apply List.mem_map.mpr
      refine ⟨index, ?_, boxPlaquetteAt_eq_of_enumerate hindexed⟩
      unfold excitedPlaquetteIds physicalFaceEdges
      apply List.mem_filter.mpr
      constructor
      · unfold plaquetteEdgeCount
        exact List.mem_range.mpr (enumerate_index_lt hindexed)
      · simpa only [decide_eq_true_eq, ← hvalue] using hpositive
    · rw [geometricSpinOfPhysical_zero_of_not_mem n physical hmem]
        at hpositive
      omega
  · intro hmem
    unfold geometricPolymer at hmem
    obtain ⟨index, hindex, hplaquette⟩ := List.mem_map.mp hmem
    have hparts := List.mem_filter.mp hindex
    have hindexed := boxPlaquetteAt_mem_enumerate
      (physicalFaceId_lt hparts.1)
    have hpositive : 1 ≤ physical index := by
      simpa only [decide_eq_true_eq] using hparts.2
    rw [← hplaquette,
      geometricSpinOfPhysical_eq_of_enumerate hindexed]
    exact hpositive

private theorem filter_eq_of_agree {A : Type} (left right : A → Bool) :
    ∀ xs : List A, (∀ x, x ∈ xs → left x = right x) →
      xs.filter left = xs.filter right
  | [], _ => rfl
  | x :: xs, hagree => by
      have hx := hagree x List.mem_cons_self
      have htail : ∀ y, y ∈ xs → left y = right y :=
        fun y hy => hagree y (List.mem_cons_of_mem x hy)
      simp only [List.filter_cons, hx]
      rw [filter_eq_of_agree left right xs htail]

theorem excitedPlaquetteIds_transportPhysical
    (small large : Nat) (physical : EdgeLabelling) :
    excitedPlaquetteIds large
        (transportPhysical small large physical) =
      transportPolymer small large
        (excitedPlaquetteIds small physical) := by
  unfold excitedPlaquetteIds transportPolymer geometricSupportIds
    physicalFaceEdges
  apply filter_eq_of_agree
  intro targetId htarget
  have hlt := List.mem_range.mp htarget
  have htransport :
      transportPhysical small large physical targetId =
        geometricSpinOfPhysical small physical
          (boxPlaquetteAt large targetId) := by
    unfold transportPhysical
    rw [if_pos hlt]
  rw [htransport]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using
    (geometricSpin_positive_iff_mem_geometricSupport
      small physical (boxPlaquetteAt large targetId))

/-- Exact-support fibres map into the fibre of the geometrically transported
support. -/
theorem transportPhysical_mem_supportFiber
    {cutoff small large : Nat} {support : List Nat}
    {physical : EdgeLabelling}
    (hphysical : physical ∈
      physicalLabellingsWithSupport cutoff small support) :
    transportPhysical small large physical ∈
      physicalLabellingsWithSupport cutoff large
        (transportPolymer small large support) := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp hphysical
  apply mem_physicalLabellingsWithSupport_iff.mpr
  constructor
  · exact transportPhysical_mem_bounded hparts.1
  · rw [excitedPlaquetteIds_transportPhysical, hparts.2]

/-- The literal, source-ordered copy of an exact-support fibre inside the
larger physical labelling space. -/
def transportedPhysicalFiber (cutoff small large : Nat)
    (support : List Nat) : List EdgeLabelling :=
  (physicalLabellingsWithSupport cutoff small support).map
    (transportPhysical small large)

theorem mem_transportedPhysicalFiber_iff
    {cutoff small large : Nat} {support : List Nat}
    {target : EdgeLabelling} :
    target ∈ transportedPhysicalFiber cutoff small large support ↔
      ∃ source, source ∈
          physicalLabellingsWithSupport cutoff small support ∧
        transportPhysical small large source = target := by
  unfold transportedPhysicalFiber
  rw [List.mem_map]

theorem transportedPhysicalFiber_mem_target
    {cutoff small large : Nat} {support : List Nat}
    {target : EdgeLabelling}
    (htarget : target ∈
      transportedPhysicalFiber cutoff small large support) :
    target ∈ physicalLabellingsWithSupport cutoff large
      (transportPolymer small large support) := by
  obtain ⟨source, hsource, rfl⟩ :=
    mem_transportedPhysicalFiber_iff.mp htarget
  exact transportPhysical_mem_supportFiber hsource

theorem transportedPhysicalFiber_nodup
    {cutoff small large : Nat} (hsmall : small ≤ large)
    (support : List Nat) :
    (transportedPhysicalFiber cutoff small large support).Nodup := by
  unfold transportedPhysicalFiber
  apply CayleyPruferInjection.nodup_map_of_injOn
    (transportPhysical small large)
    (physicalLabellingsWithSupport cutoff small support)
    (physicalLabellingsWithSupport_nodup cutoff small support)
  intro left hleft right hright heq
  exact transportPhysical_injective_on hsmall
    (mem_physicalLabellingsWithSupport_iff.mp hleft).1
    (mem_physicalLabellingsWithSupport_iff.mp hright).1 heq

theorem incidentTransportedSpins_eq_geometric
    (small large : Nat) (ell : Z4Link) (physical : EdgeLabelling) :
    incidentPhysicalSpins large ell
        (transportPhysical small large physical) =
      geometricIncidentSpins large ell
        (geometricSpinOfPhysical small physical) := by
  rw [incidentPhysicalSpins_eq_geometric]
  unfold geometricIncidentSpins
  apply List.map_congr_left
  intro plaquette hplaquette
  exact geometricSpinOfTransport_eq_of_mem_box
    (List.mem_filter.mp hplaquette).1

/-- The actual incident-spin sequence of the embedded labelling is an ordered
zero extension of the actual smaller-box sequence. -/
theorem incidentPhysicalSpins_zeroExtension
    {small large : Nat} (hsmall : small ≤ large)
    (ell : Z4Link) (physical : EdgeLabelling) :
    ZeroExtension
      (incidentPhysicalSpins small ell physical)
      (incidentPhysicalSpins large ell
        (transportPhysical small large physical)) := by
  rw [incidentPhysicalSpins_eq_geometric,
    incidentTransportedSpins_eq_geometric]
  apply geometricIncidentSpins_zeroExtension hsmall ell
    (geometricSpinOfPhysical small physical)
  intro plaquette _ hnot
  exact geometricSpinOfPhysical_zero_of_not_mem
    small physical hnot

/-! ## 4. Cutoff and canonical-prefix facts -/

theorem incidentPhysicalSpins_bounded
    {K n : Nat} {ell : Z4Link} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    SpinsBounded (linkAuxiliaryCutoff K)
      (incidentPhysicalSpins n ell physical) := by
  have hsound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) physical hphysical
  intro spin hspin
  obtain ⟨plaquetteId, hid, rfl⟩ := List.mem_map.mp hspin
  have hidRange : plaquetteId ∈ List.range (plaquetteEdgeCount n) :=
    List.mem_range.mpr (incidentPlaqId_lt_count hid)
  have hlt := hsound.1 plaquetteId hidRange
  unfold linkAuxiliaryCutoff linkIncidenceBound
  omega

theorem localIdentifierExternal_eq_incidentList
    (physical : EdgeLabelling) (labels : List Nat) (base position : Nat)
    (hposition : position < labels.length) :
    physical (localIdentifierRename labels base position) =
      externalSpinsOfList (labels.map physical) position := by
  induction labels generalizing position with
  | nil => simp at hposition
  | cons head tail ih =>
      cases position with
      | zero => rfl
      | succ position =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hposition
          change physical (localIdentifierRename tail base position) =
            externalSpinsOfList (tail.map physical) position
          exact ih position hposition

theorem actualExplicitMultiplicity_eq_incidentList
    (K n : Nat) (ell : Z4Link) (physical : EdgeLabelling) (base : Nat) :
    explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        (incidentPlaqIds n ell).length
        (fun position => physical
          (localIdentifierRename (incidentPlaqIds n ell) base position)) =
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        (incidentPhysicalSpins n ell physical).length
        (externalSpinsOfList (incidentPhysicalSpins n ell physical)) := by
  have hlength : (incidentPhysicalSpins n ell physical).length =
      (incidentPlaqIds n ell).length := by
    simp [incidentPhysicalSpins]
  rw [hlength]
  apply explicitValenceMultiplicity_congr_prefix
    (incidentPlaqIds_length_le_six n ell)
  intro position hposition
  exact localIdentifierExternal_eq_incidentList physical
    (incidentPlaqIds n ell) base position hposition

/-! ## 5. Exact local cross-volume multiplicity -/

/-- **Arbitrary-cutoff local cross-volume locality.**  For every fixed
geometric link, extending a smaller-box physical labelling by zero to the
larger box preserves the literal natural-number fusion multiplicity exactly.
The production-private block bases may differ arbitrarily. -/
theorem explicitLinkMultiplicity_cross_volume
    {K small large : Nat} (hsmall : small ≤ large)
    {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount small)))
    (ell : Z4Link) (smallBase largeBase : Nat) :
    explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        (incidentPlaqIds small ell).length
        (fun position => physical
          (localIdentifierRename (incidentPlaqIds small ell)
            smallBase position)) =
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        (incidentPlaqIds large ell).length
        (fun position => transportPhysical small large physical
          (localIdentifierRename (incidentPlaqIds large ell)
            largeBase position)) := by
  rw [actualExplicitMultiplicity_eq_incidentList,
    actualExplicitMultiplicity_eq_incidentList]
  apply explicitValenceMultiplicity_zeroExtension
  · exact incidentPhysicalSpins_zeroExtension hsmall ell physical
  · simpa [incidentPhysicalSpins] using
      incidentPlaqIds_length_le_six small ell
  · simpa [incidentPhysicalSpins] using
      incidentPlaqIds_length_le_six large ell
  · exact incidentPhysicalSpins_bounded hphysical

#print axioms geometricSpinOfPhysical_eq_of_enumerate
#print axioms incidentPhysicalSpins_eq_geometric
#print axioms transportPhysical_mem_bounded
#print axioms transportPhysical_injective_on
#print axioms excitedPlaquetteIds_transportPhysical
#print axioms transportPhysical_mem_supportFiber
#print axioms transportedPhysicalFiber_mem_target
#print axioms transportedPhysicalFiber_nodup
#print axioms incidentPhysicalSpins_zeroExtension
#print axioms incidentPhysicalSpins_bounded
#print axioms actualExplicitMultiplicity_eq_incidentList
#print axioms explicitLinkMultiplicity_cross_volume

end YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
