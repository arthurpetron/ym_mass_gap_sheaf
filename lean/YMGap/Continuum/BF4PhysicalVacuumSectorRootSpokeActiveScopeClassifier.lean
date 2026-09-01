/-
# Active-scope BF4 vacuum-root spoke classifier

Vacuum fixed and upper coordinates contribute only inserted spin-zero entries
to every lower-link fusion word.  This module removes those entries with the
production zero-extension theorem and rewrites every local root-spoke
constraint using only the incident lower-face source labels.

The resulting constraint hypergraph has the same cutoff-independent geometry
at every `K`: 24 lower-face variables, 48 lower-link constraints, and active
scope arity at most four.  At strictly positive coupling, the routing-level
root-predecessor carrier is exactly the canonical-sector filter by these
active-scope constraints.

This still gives no asymptotic count, distributed routing, congestion bound,
gap, continuum limit, or Clay conclusion.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry
import YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier
import YMGap.Continuum.Z4FusionPathZeroInsertion

namespace YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open scoped List

/-! ## 1. Cutoff-independent active lower-link scopes -/

/-- The incident lower faces of one production lower link.  The older name
mentions cutoff two because that was its first consumer; the definition is
pure geometry and contains no cutoff. -/
def centralVacuumLowerActiveIncidentFaceIds
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) : List Nat :=
  cutoffTwoActiveIncidentFaceIds link

def centralVacuumLowerActiveLinkFaceIds : List (List Nat) :=
  (centralLowerLinks 0).map centralVacuumLowerActiveIncidentFaceIds

theorem centralVacuumLowerActiveLinkFaceIds_checked :
    centralVacuumLowerActiveLinkFaceIds =
      cutoffTwoExpectedActiveLinkFaceIds := by
  unfold centralVacuumLowerActiveLinkFaceIds
    centralVacuumLowerActiveIncidentFaceIds
  exact cutoffTwoActiveLinkFaceIds_checked

theorem centralVacuumLowerFace_count :
    (centralLowerFaceIds 0).length = 24 := by
  decide

theorem centralVacuumLowerLink_count :
    (centralLowerLinks 0).length = 48 := by
  decide

theorem centralVacuumLowerActiveScopes_arity_le_four :
    centralVacuumLowerActiveLinkFaceIds.all
      (fun scope => decide (scope.length ≤ 4)) = true := by
  decide

/-! ## 2. Removing vacuum insertions from each local multiplicity -/

def centralVacuumLowerActiveSpins
    (source : EdgeLabelling)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) : List Nat :=
  (centralVacuumLowerActiveIncidentFaceIds link).map source

def centralVacuumLowerActiveMultiplicity
    (K : Nat) (source : EdgeLabelling)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) : Nat :=
  let spins := centralVacuumLowerActiveSpins source link
  explicitValenceMultiplicity (linkAuxiliaryCutoff K) spins.length
    (externalSpinsOfList spins)

theorem centralVacuumLowerPhysical_eq_zero_of_not_lower
    (source : EdgeLabelling) {id : Nat}
    (hphysical : id ∈ slabPhysicalFaceEdges (centralExtent 0))
    (hnotLower : id ∉ centralLowerFaceIds 0) :
    centralVacuumLowerPhysical source id = 0 := by
  unfold centralVacuumLowerPhysical assembleReflectedSlabLabelling
  rw [if_pos hphysical]
  cases hside : plaquetteHalfSide 0
      (slabPlaquetteAt (centralExtent 0) id) with
  | lower =>
      exact False.elim
        (hnotLower (mem_centralLowerFaceIds.mpr ⟨hphysical, hside⟩))
  | fixed => rfl
  | upper => rfl

/-- The full production fusion word and the active lower-face word have
exactly the same multiplicity at every cutoff. -/
theorem slabExplicitLinkMultiplicity_vacuum_eq_active
    (K : Nat) (source : EdgeLabelling)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link)
    (hsource : source ∈ centralHalfStates K 0) :
    slabExplicitLinkMultiplicity K (centralExtent 0)
        (centralVacuumLowerPhysical source) link =
      centralVacuumLowerActiveMultiplicity K source link := by
  let activeIds := centralVacuumLowerActiveIncidentFaceIds link
  let physical := centralVacuumLowerPhysical source
  let active := centralVacuumLowerActiveSpins source link
  let incident := (slabIncidentPlaqIds (centralExtent 0) link).map physical
  have hactiveMap : activeIds.map physical = active := by
    unfold active activeIds centralVacuumLowerActiveSpins
      centralVacuumLowerActiveIncidentFaceIds
      cutoffTwoActiveIncidentFaceIds
    apply List.map_congr_left
    intro id hid
    have hlower : id ∈ centralLowerFaceIds 0 :=
      of_decide_eq_true (List.mem_filter.mp hid).2
    have hparts := mem_centralLowerFaceIds.mp hlower
    unfold physical centralVacuumLowerPhysical
    exact assembleReflectedSlabLabelling_lower hparts.1 hparts.2
  have hextension : ZeroExtension active incident := by
    have hraw : ZeroExtension (activeIds.map physical) incident := by
      unfold activeIds centralVacuumLowerActiveIncidentFaceIds
        cutoffTwoActiveIncidentFaceIds incident
      apply ZeroExtension.map_of_sublist physical List.filter_sublist
        (slabIncidentPlaqIds_nodup (centralExtent 0) link)
      intro id hid hnotActive
      apply centralVacuumLowerPhysical_eq_zero_of_not_lower source
        (slabIncidentPlaqId_physical hid)
      intro hlower
      apply hnotActive
      exact List.mem_filter.mpr
        ⟨hid, by simp only [hlower, decide_true]⟩
    rw [hactiveMap] at hraw
    exact hraw
  have hactiveLength : active.length ≤ 6 := by
    unfold active centralVacuumLowerActiveSpins
      centralVacuumLowerActiveIncidentFaceIds
      cutoffTwoActiveIncidentFaceIds
    rw [List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _)
      (slabIncidentPlaqIds_length_le_six (centralExtent 0) link)
  have hincidentLength : incident.length ≤ 6 := by
    unfold incident
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six (centralExtent 0) link
  have hsourceSound := boundedEdgeLabellings_sound
    K (centralLowerFaceIds 0) source hsource
  have hactiveBounded :
      SpinsBounded (linkAuxiliaryCutoff K) active := by
    intro spin hspin
    unfold active centralVacuumLowerActiveSpins at hspin
    rcases List.mem_map.mp hspin with ⟨id, hid, rfl⟩
    have hlower : id ∈ centralLowerFaceIds 0 := by
      unfold centralVacuumLowerActiveIncidentFaceIds
        cutoffTwoActiveIncidentFaceIds at hid
      exact of_decide_eq_true (List.mem_filter.mp hid).2
    have hbound := hsourceSound.1 id hlower
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  unfold slabExplicitLinkMultiplicity
    centralVacuumLowerActiveMultiplicity
  change
    explicitValenceMultiplicity (linkAuxiliaryCutoff K) incident.length
        (externalSpinsOfList incident) =
      explicitValenceMultiplicity (linkAuxiliaryCutoff K) active.length
        (externalSpinsOfList active)
  exact (explicitValenceMultiplicity_zeroExtension
    hextension hactiveLength hincidentLength hactiveBounded).symm

/-! ## 3. Active-scope Boolean and finite-sector carrier -/

def centralVacuumLowerActiveScopesAdmissibleB
    (K : Nat) (source : EdgeLabelling) : Bool :=
  (centralLowerLinks 0).all fun link => decide
    (0 < centralVacuumLowerActiveMultiplicity K source link)

theorem centralVacuumLowerLinksAdmissibleB_eq_activeScopes
    (K : Nat) (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates K 0) :
    centralVacuumLowerLinksAdmissibleB K source =
      centralVacuumLowerActiveScopesAdmissibleB K source := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hfull
    apply List.all_eq_true.mpr
    intro link hlink
    have hpos :
        0 < slabExplicitLinkMultiplicity K (centralExtent 0)
          (centralVacuumLowerPhysical source) link :=
      of_decide_eq_true (List.all_eq_true.mp hfull link hlink)
    rw [slabExplicitLinkMultiplicity_vacuum_eq_active
      K source link hsource] at hpos
    exact decide_eq_true hpos
  · intro hactive
    apply List.all_eq_true.mpr
    intro link hlink
    have hpos : 0 < centralVacuumLowerActiveMultiplicity K source link :=
      of_decide_eq_true (List.all_eq_true.mp hactive link hlink)
    rw [← slabExplicitLinkMultiplicity_vacuum_eq_active
      K source link hsource] at hpos
    exact decide_eq_true hpos

def centralPhysicalFiniteVacuumSectorActiveScopeRootIndices
    (w : YMGap.Constructive.Q')
    (hw : (0 : YMGap.Constructive.Q') ≤ w)
    (K : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (fun source => centralVacuumLowerActiveScopesAdmissibleB K
      (centralPhysicalFiniteStateAt w hw K 0 source))

theorem centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices_eq_activeScopes
    (w : YMGap.Constructive.Q')
    (hw : (0 : YMGap.Constructive.Q') ≤ w)
    (K : Nat) :
    centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices w hw K =
      centralPhysicalFiniteVacuumSectorActiveScopeRootIndices w hw K := by
  unfold centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices
    centralPhysicalFiniteVacuumSectorActiveScopeRootIndices
  apply List.filter_congr
  intro source hsource
  have hsourceState :
      centralPhysicalFiniteStateAt w hw K 0 source ∈
        centralPhysicalFiniteVacuumSectorStates w hw K 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w hw K 0 hsource rfl
  have hsourceHalf :
      centralPhysicalFiniteStateAt w hw K 0 source ∈
        centralHalfStates K 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_halfStates
      w hw K 0 hsourceState
  exact centralVacuumLowerLinksAdmissibleB_eq_activeScopes
    K (centralPhysicalFiniteStateAt w hw K 0 source) hsourceHalf

theorem centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_activeScopes
    {w : YMGap.Constructive.Q'}
    (hw : (0 : YMGap.Constructive.Q') ≤ w)
    (hwpos : (0 : YMGap.Constructive.Q') < w)
    (K : Nat) :
    centralPhysicalFiniteVacuumSectorPositiveRootPredecessors w hw K =
      centralPhysicalFiniteVacuumSectorActiveScopeRootIndices w hw K :=
  Eq.trans
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_localConstraints
      hw hwpos K)
    (centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices_eq_activeScopes
      w hw K)

theorem centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_activeScopeCount
    {w : YMGap.Constructive.Q'}
    (hw : (0 : YMGap.Constructive.Q') ≤ w)
    (hwpos : (0 : YMGap.Constructive.Q') < w)
    (K : Nat) :
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
        w hw K).length =
      (centralPhysicalFiniteVacuumSectorActiveScopeRootIndices
        w hw K).length :=
  congrArg List.length
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_activeScopes
      hw hwpos K)

end YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier.centralVacuumLowerActiveLinkFaceIds_checked
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier.centralVacuumLowerActiveScopes_arity_le_four
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier.centralVacuumLowerPhysical_eq_zero_of_not_lower
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier.slabExplicitLinkMultiplicity_vacuum_eq_active
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier.centralVacuumLowerLinksAdmissibleB_eq_activeScopes
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier.centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices_eq_activeScopes
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier.centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_activeScopes
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier.centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_activeScopeCount
