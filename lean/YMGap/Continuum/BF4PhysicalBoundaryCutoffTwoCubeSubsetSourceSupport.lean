/-
# Source-support containment for the cutoff-two cube sector

Every doubled-spin subset source has boundary support contained in the
fundamental cube's boundary support.  The essential fact is local: on each of
the 48 production lower links, exhaustive checking of the at-most-unary fixed
scope proves that positivity for any of the 64 subset sources implies
positivity for the fundamental cube.  The generic local-checker soundness
theorem transports that finite computation to an arbitrary bounded boundary.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierBridge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
import YMGap.Continuum.FiniteLocalSupportImplicationCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetSourceSupport

set_option maxRecDepth 300000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteLocalSupportImplicationCertificate
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

/-! ## 1. Executable local implication table -/

def cutoffTwoBoundaryLinkMultiplicity
    (source : EdgeLabelling) (link : Z4Link)
    (boundary : EdgeLabelling) : Nat :=
  slabExplicitLinkMultiplicity 2 1
    (assembleReflectedSlabLabelling 0 source boundary zeroEdgeLabelling) link

/-- All 64 sources, all 48 lower links, and all bounded labellings of each
at-most-unary fixed scope are checked by reduction. -/
def cutoffTwoDoubledSourcesCubeLocalSupportCheck : Bool :=
  cutoffTwoDoubledCubeSubsetStates.all fun source =>
    (centralLowerLinks 0).all fun link =>
      boundedLocalSupportImplicationCheck 2
        (cutoffTwoCubeFixedIncidentFaceIds link)
        (cutoffTwoBoundaryLinkMultiplicity source link)
        (cutoffTwoBoundaryLinkMultiplicity centralLowerCubeState link)

theorem cutoffTwoDoubledSourcesCubeLocalSupport_checked :
    cutoffTwoDoubledSourcesCubeLocalSupportCheck = true := by
  decide

private theorem listMap_congr_on {A B : Type}
    (left right : A → B) : ∀ items : List A,
    (∀ item, item ∈ items → left item = right item) →
      items.map left = items.map right
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [List.map_cons]
      rw [hagree head List.mem_cons_self,
        listMap_congr_on left right tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem))]

private theorem slabExplicitLinkMultiplicity_congr_incident
    (K extent : Nat) (left right : EdgeLabelling) (link : Z4Link)
    (hagree : ∀ id, id ∈ slabIncidentPlaqIds extent link →
      left id = right id) :
    slabExplicitLinkMultiplicity K extent left link =
      slabExplicitLinkMultiplicity K extent right link := by
  unfold slabExplicitLinkMultiplicity
  rw [listMap_congr_on left right
    (slabIncidentPlaqIds extent link) hagree]

private theorem cutoffTwoBoundaryLinkMultiplicity_local
    (source : EdgeLabelling) (link : Z4Link)
    (hlink : link ∈ centralLowerLinks 0)
    (left right : EdgeLabelling)
    (hagree : ∀ id, id ∈ cutoffTwoCubeFixedIncidentFaceIds link →
      left id = right id) :
    cutoffTwoBoundaryLinkMultiplicity source link left =
      cutoffTwoBoundaryLinkMultiplicity source link right := by
  unfold cutoffTwoBoundaryLinkMultiplicity
  apply slabExplicitLinkMultiplicity_congr_incident
  intro id hid
  have hphysical : id ∈ slabPhysicalFaceEdges 1 :=
    slabIncidentPlaqId_physical hid
  have hnotUpper := incident_of_lower_link_ne_upper hlink hid
  cases hside : plaquetteHalfSide 0 (slabPlaquetteAt 1 id)
  · rw [assembleReflectedSlabLabelling_lower hphysical hside,
      assembleReflectedSlabLabelling_lower hphysical hside]
  · rw [assembleReflectedSlabLabelling_fixed hphysical hside,
      assembleReflectedSlabLabelling_fixed hphysical hside]
    apply hagree id
    unfold cutoffTwoCubeFixedIncidentFaceIds
    exact List.mem_filter.mpr
      ⟨hid, by
        have hfixed : id ∈ centralFixedFaceIds 0 :=
          mem_centralFixedFaceIds.mpr ⟨hphysical, hside⟩
        simpa only [decide_eq_true_eq] using hfixed⟩
  · exact False.elim (hnotUpper hside)

theorem cutoffTwoCubeLowerLinkSupport_of_doubledSubsetSupport
    (source boundary : EdgeLabelling) (link : Z4Link)
    (hsource : source ∈ cutoffTwoDoubledCubeSubsetStates)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0)
    (hlink : link ∈ centralLowerLinks 0)
    (hpositive : 0 < cutoffTwoBoundaryLinkMultiplicity source link boundary) :
    0 < cutoffTwoBoundaryLinkMultiplicity
      centralLowerCubeState link boundary := by
  apply localSupportImplication_of_check 2
    (cutoffTwoCubeFixedIncidentFaceIds link)
    (cutoffTwoBoundaryLinkMultiplicity source link)
    (cutoffTwoBoundaryLinkMultiplicity centralLowerCubeState link)
  · unfold cutoffTwoCubeFixedIncidentFaceIds
    exact (slabIncidentPlaqIds_nodup 1 link).filter _
  · exact cutoffTwoBoundaryLinkMultiplicity_local source link hlink
  · exact cutoffTwoBoundaryLinkMultiplicity_local
      centralLowerCubeState link hlink
  · exact List.all_eq_true.mp
      (List.all_eq_true.mp
        cutoffTwoDoubledSourcesCubeLocalSupport_checked source hsource)
      link hlink
  · intro id hid
    unfold centralBoundaryChannels at hboundary
    have hfixed : id ∈ centralFixedFaceIds 0 := by
      have hparts := List.mem_filter.mp hid
      exact of_decide_eq_true hparts.2
    exact (boundedEdgeLabellings_sound 2 (centralFixedFaceIds 0)
      boundary hboundary).1 id hfixed
  · exact hpositive

/-! ## 2. From positive cube links to a nonzero cube half amplitude -/

private theorem natListProduct_pos_on {A : Type}
    (value : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → 0 < value item) →
      0 < natListProduct value items
  | [], _ => by
      change 0 < 1
      exact Nat.zero_lt_succ 0
  | head :: tail, hvalue => by
      simp only [natListProduct]
      exact Nat.mul_pos
        (hvalue head List.mem_cons_self)
        (natListProduct_pos_on value tail
          (fun item hitem =>
            hvalue item (List.mem_cons_of_mem head hitem)))

private theorem eliminateLinks_pos_on (value : Nat → Q') :
    ∀ ids : List Nat,
    (∀ id, id ∈ ids → (0 : Q') < value id) →
      (0 : Q') < eliminateLinks value ids
  | [], _ => by
      change (0 : Q') < 1
      decide
  | head :: tail, hvalue =>
      Q'.mul_pos
        (hvalue head List.mem_cons_self)
        (eliminateLinks_pos_on value tail
          (fun id hid => hvalue id (List.mem_cons_of_mem head hid)))

private theorem qOfNat_pos_of_pos (value : Nat) (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  show (0 : Int) * ((Q'.ofNat value).den : Int) <
    (Q'.ofNat value).num * (1 : Int)
  rw [Int.zero_mul, Q'.ofNat_num_cast, Int.mul_one]
  exact Int.ofNat_lt.mpr hvalue

private theorem cutoffTwoCubeLowerFaceFactor_pos
  (boundary : EdgeLabelling) :
    (0 : Q') < slabFaceFactorOn cutoffTwoHalfCoupling 2
      (assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
        zeroEdgeLabelling)
      (centralLowerFaceIds 0) := by
  unfold slabFaceFactorOn
  apply eliminateLinks_pos_on
  intro id hid
  have hlower := mem_centralLowerFaceIds.mp hid
  have hspin :
      assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
          zeroEdgeLabelling id < 3 := by
    rw [assembleReflectedSlabLabelling_lower hlower.1 hlower.2]
    exact Nat.lt_of_le_of_lt (centralLowerCubeState_le_one id) (by omega)
  rw [coeffAt_heatKernelPacket hspin]
  exact coeffW_pos (by decide)
    (assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
      zeroEdgeLabelling id)

theorem centralHalfAmplitude_cutoffTwo_cube_pos_of_lowerLinks
    (boundary : EdgeLabelling)
    (hlinks : ∀ link, link ∈ centralLowerLinks 0 →
      0 < cutoffTwoBoundaryLinkMultiplicity
        centralLowerCubeState link boundary) :
    (0 : Q') < centralHalfAmplitude cutoffTwoHalfCoupling 2 0
      centralLowerCubeState boundary := by
  have hproduct : 0 < slabLinkMultiplicityProductOn 2 1
      (assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
        zeroEdgeLabelling)
      (centralLowerLinks 0) := by
    unfold slabLinkMultiplicityProductOn
    apply natListProduct_pos_on
    intro link hlink
    exact hlinks link hlink
  unfold centralHalfAmplitude centralLowerFactor
  exact Q'.mul_pos
    (cutoffTwoCubeLowerFaceFactor_pos boundary)
    (qOfNat_pos_of_pos _ hproduct)

/-- The boundary support of every one of the 64 doubled-spin subset sources
is contained in the boundary support of the fundamental cube. -/
theorem cube_halfAmplitude_ne_zero_of_doubledSubset_halfAmplitude_ne_zero
    (source boundary : EdgeLabelling)
    (hsource : source ∈ cutoffTwoDoubledCubeSubsetStates)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0)
    (hnonzero : ¬ Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source boundary) 0) :
    ¬ Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerCubeState boundary) 0 := by
  have hpositive : (0 : Q') <
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerCubeState boundary := by
    apply centralHalfAmplitude_cutoffTwo_cube_pos_of_lowerLinks
    intro link hlink
    apply cutoffTwoCubeLowerLinkSupport_of_doubledSubsetSupport
      source boundary link hsource hboundary hlink
    exact cutoffTwoLowerLinkMultiplicity_pos_of_halfAmplitude_ne_zero
      source boundary link hlink hnonzero
  intro hzero
  exact (Int.not_lt_of_ge (Q'.le_of_eqv hzero)) hpositive

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetSourceSupport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetSourceSupport.cutoffTwoDoubledSourcesCubeLocalSupport_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetSourceSupport.cutoffTwoCubeLowerLinkSupport_of_doubledSubsetSupport
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetSourceSupport.cube_halfAmplitude_ne_zero_of_doubledSubset_halfAmplitude_ne_zero
