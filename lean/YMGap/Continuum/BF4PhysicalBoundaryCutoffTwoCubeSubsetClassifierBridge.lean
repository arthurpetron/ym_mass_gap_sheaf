/-
# Bridge from the cutoff-two CSP classifier to physical half-state support

The finite CSP uses ordinary slab face coordinates below `1000` and
auxiliary deterministic-classifier coordinates `1000..1023`.  This module
constructs that combined assignment from a physical lower-half state and a
fixed-interface boundary, proves it is ternary-bounded, and then connects
positive production link support to the checked CSP constraints.

No continuum or cutoff-uniform conclusion is asserted here.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSPCertificate
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierLanguage

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 10000000

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSPCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierLanguage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteTernaryCSPUnsatCertificate
open YMGap.Continuum.FiniteTernaryCSPUnsatCertificate.TernaryUnsatCertificate
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

private theorem zeroEdgeLabelling_mem_halfStates :
    zeroEdgeLabelling ∈ centralHalfStates 2 0 := by
  apply boundedEdgeLabellings_complete
  · intro _ _
    simp [zeroEdgeLabelling]
  · intro _ _
    rfl

/-- The physical target/boundary half-slab below coordinate `1000`, the
deterministic classifier run on `1000..1023`, and zero elsewhere. -/
def cutoffTwoCubeSubsetCSPAssignment
    (state boundary : EdgeLabelling) : Nat → Nat := fun coordinate =>
  if coordinate < 1000 then
    assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling coordinate
  else if coordinate < 1024 then
    cutoffTwoCubeSubsetClassifierState state (coordinate - 1000)
  else 0

theorem cutoffTwoCubeSubsetCSPAssignment_eq_physical
    (state boundary : EdgeLabelling) {id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges 1) :
    cutoffTwoCubeSubsetCSPAssignment state boundary id =
      assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling id := by
  have hidLt := slabPhysicalFaceId_lt hid
  have hlength : (boundaryCompleteSlabPlaquettes 1).length = 72 := by
    decide
  have hidThousand : id < 1000 := by omega
  simp [cutoffTwoCubeSubsetCSPAssignment, hidThousand]

theorem cutoffTwoCubeSubsetCSPAssignment_eq_classifierState
    (state boundary : EdgeLabelling) (step : Nat) (hstep : step < 24) :
    cutoffTwoCubeSubsetCSPAssignment state boundary (1000 + step) =
      cutoffTwoCubeSubsetClassifierState state step := by
  have hnotPhysical : ¬ 1000 + step < 1000 := by omega
  have hauxiliary : 1000 + step < 1024 := by omega
  have hsubtract : 1000 + step - 1000 = step := by omega
  simp [cutoffTwoCubeSubsetCSPAssignment, hnotPhysical, hauxiliary,
    hsubtract]

theorem cutoffTwoCubeSubsetCSPAssignment_bounded
    {state boundary : EdgeLabelling}
    (hstate : state ∈ centralHalfStates 2 0)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0) :
    AssignmentBounded
      (cutoffTwoCubeSubsetCSPAssignment state boundary) := by
  let physical :=
    assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling
  have hphysicalBounded : SlabFaceLabellingBounded 2 1 physical := by
    exact assembleReflectedSlabLabelling_bounded
      hstate hboundary zeroEdgeLabelling_mem_halfStates
  intro coordinate
  unfold cutoffTwoCubeSubsetCSPAssignment
  split
  next hcoordinate =>
    by_cases hphysical : coordinate ∈ slabPhysicalFaceEdges 1
    · have hle := hphysicalBounded coordinate hphysical
      change physical coordinate < 3
      omega
    · have hzero : physical coordinate = 0 := by
        exact assembleReflectedSlabLabelling_zero_off_physical
          0 state boundary zeroEdgeLabelling hphysical
      change physical coordinate < 3
      rw [hzero]
      omega
  next hcoordinate =>
    split
    next _ =>
      exact cutoffTwoCubeSubsetClassifierState_lt_three state
        (coordinate - 1000)
    next _ => omega

/-! ## Local reconstruction of production link constraints -/

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

private theorem wordToEdgeLabelling_map_eq_on
    (assignment : Nat → Nat) : ∀ scope : List Nat,
    scope.Nodup → ∀ id, id ∈ scope →
      wordToEdgeLabelling scope (scope.map assignment) id = assignment id
  | [], _, id, hid => False.elim (List.not_mem_nil hid)
  | head :: tail, hnodup, id, hid => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hid with hhead | htail
      · subst id
        simp [wordToEdgeLabelling, setEdgeLabel]
      · have hne : id ≠ head := by
          intro heq
          apply hparts.1
          rw [← heq]
          exact htail
        simp only [List.map_cons, wordToEdgeLabelling]
        rw [show setEdgeLabel
            (wordToEdgeLabelling tail (tail.map assignment))
              head (assignment head) id =
            wordToEdgeLabelling tail (tail.map assignment) id by
              simp [setEdgeLabel, hne]]
        exact wordToEdgeLabelling_map_eq_on assignment tail
          hparts.2 id htail

private theorem decodedTarget_agrees_physical
    (state boundary : EdgeLabelling) (link : Z4Link) :
    ∀ id, id ∈ slabIncidentPlaqIds 1 link →
      wordToEdgeLabelling (slabIncidentPlaqIds 1 link)
          ((slabIncidentPlaqIds 1 link).map
            (cutoffTwoCubeSubsetCSPAssignment state boundary)) id =
        assembleReflectedSlabLabelling 0 state boundary
          zeroEdgeLabelling id := by
  intro id hid
  rw [wordToEdgeLabelling_map_eq_on
    (cutoffTwoCubeSubsetCSPAssignment state boundary)
    (slabIncidentPlaqIds 1 link)
    (slabIncidentPlaqIds_nodup 1 link) id hid]
  exact cutoffTwoCubeSubsetCSPAssignment_eq_physical
    state boundary (slabIncidentPlaqId_physical hid)

theorem cutoffTwoTargetSupportConstraint_satisfied
    (state boundary : EdgeLabelling) (link : Z4Link)
    (hpositive : 0 < slabExplicitLinkMultiplicity 2 1
      (assembleReflectedSlabLabelling 0 state boundary
        zeroEdgeLabelling) link) :
    SatisfiesConstraint (cutoffTwoCubeSubsetCSPAssignment state boundary)
      (cutoffTwoTargetSupportConstraint link) := by
  unfold SatisfiesConstraint cutoffTwoTargetSupportConstraint
  have heq := slabExplicitLinkMultiplicity_congr_incident 2 1
    (wordToEdgeLabelling (slabIncidentPlaqIds 1 link)
      ((slabIncidentPlaqIds 1 link).map
        (cutoffTwoCubeSubsetCSPAssignment state boundary)))
    (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling)
    link (decodedTarget_agrees_physical state boundary link)
  change decide (0 < slabExplicitLinkMultiplicity 2 1
    (wordToEdgeLabelling (slabIncidentPlaqIds 1 link)
      ((slabIncidentPlaqIds 1 link).map
        (cutoffTwoCubeSubsetCSPAssignment state boundary))) link) = true
  rw [heq]
  simpa only [decide_eq_true_eq] using hpositive

private theorem decodedCubeBoundary_agrees_boundary
    (state boundary : EdgeLabelling) (link : Z4Link) :
    ∀ id, id ∈ cutoffTwoCubeFixedIncidentFaceIds link →
      wordToEdgeLabelling (cutoffTwoCubeFixedIncidentFaceIds link)
          ((cutoffTwoCubeFixedIncidentFaceIds link).map
            (cutoffTwoCubeSubsetCSPAssignment state boundary)) id =
        boundary id := by
  intro id hid
  rw [wordToEdgeLabelling_map_eq_on
    (cutoffTwoCubeSubsetCSPAssignment state boundary)
    (cutoffTwoCubeFixedIncidentFaceIds link)
    (by
      unfold cutoffTwoCubeFixedIncidentFaceIds
      exact (slabIncidentPlaqIds_nodup 1 link).filter _) id hid]
  have hparts := List.mem_filter.mp hid
  have hfixed : id ∈ centralFixedFaceIds 0 := by
    exact of_decide_eq_true hparts.2
  have hgeometry := mem_centralFixedFaceIds.mp hfixed
  rw [cutoffTwoCubeSubsetCSPAssignment_eq_physical
      state boundary hgeometry.1,
    assembleReflectedSlabLabelling_fixed hgeometry.1 hgeometry.2]

private theorem decodedCubePhysical_agrees_cubePhysical
    (state boundary : EdgeLabelling) (link : Z4Link)
    (hlink : link ∈ centralLowerLinks 0) :
    ∀ id, id ∈ slabIncidentPlaqIds 1 link →
      assembleReflectedSlabLabelling 0 centralLowerCubeState
          (wordToEdgeLabelling (cutoffTwoCubeFixedIncidentFaceIds link)
            ((cutoffTwoCubeFixedIncidentFaceIds link).map
              (cutoffTwoCubeSubsetCSPAssignment state boundary)))
          zeroEdgeLabelling id =
        assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
          zeroEdgeLabelling id := by
  intro id hid
  have hphysical : id ∈ slabPhysicalFaceEdges 1 :=
    slabIncidentPlaqId_physical hid
  have hnotUpper := incident_of_lower_link_ne_upper hlink hid
  cases hside : plaquetteHalfSide 0 (slabPlaquetteAt 1 id)
  · rw [assembleReflectedSlabLabelling_lower hphysical hside,
      assembleReflectedSlabLabelling_lower hphysical hside]
  · rw [assembleReflectedSlabLabelling_fixed hphysical hside,
      assembleReflectedSlabLabelling_fixed hphysical hside]
    apply decodedCubeBoundary_agrees_boundary state boundary link id
    unfold cutoffTwoCubeFixedIncidentFaceIds
    exact List.mem_filter.mpr
      ⟨hid, by
        have hfixed : id ∈ centralFixedFaceIds 0 :=
          mem_centralFixedFaceIds.mpr ⟨hphysical, hside⟩
        simpa only [decide_eq_true_eq] using hfixed⟩
  · exact False.elim (hnotUpper hside)

theorem cutoffTwoCubeSupportConstraint_satisfied
    (state boundary : EdgeLabelling) (link : Z4Link)
    (hlink : link ∈ centralLowerLinks 0)
    (hpositive : 0 < slabExplicitLinkMultiplicity 2 1
      (assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
        zeroEdgeLabelling) link) :
    SatisfiesConstraint (cutoffTwoCubeSubsetCSPAssignment state boundary)
      (cutoffTwoCubeSupportConstraint link) := by
  unfold SatisfiesConstraint cutoffTwoCubeSupportConstraint
  have heq := slabExplicitLinkMultiplicity_congr_incident 2 1
    (assembleReflectedSlabLabelling 0 centralLowerCubeState
      (wordToEdgeLabelling (cutoffTwoCubeFixedIncidentFaceIds link)
        ((cutoffTwoCubeFixedIncidentFaceIds link).map
          (cutoffTwoCubeSubsetCSPAssignment state boundary)))
      zeroEdgeLabelling)
    (assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
      zeroEdgeLabelling)
    link (decodedCubePhysical_agrees_cubePhysical
      state boundary link hlink)
  change decide (0 < slabExplicitLinkMultiplicity 2 1
    (assembleReflectedSlabLabelling 0 centralLowerCubeState
      (wordToEdgeLabelling (cutoffTwoCubeFixedIncidentFaceIds link)
        ((cutoffTwoCubeFixedIncidentFaceIds link).map
          (cutoffTwoCubeSubsetCSPAssignment state boundary)))
      zeroEdgeLabelling) link) = true
  rw [heq]
  simpa only [decide_eq_true_eq] using hpositive

/-! ## Deterministic classifier constraints -/

private theorem cutoffTwoCubeSubsetCSPAssignment_eq_state_of_lower
    (state boundary : EdgeLabelling) {id : Nat}
    (hid : id ∈ centralLowerFaceIds 0) :
    cutoffTwoCubeSubsetCSPAssignment state boundary id = state id := by
  have hparts := mem_centralLowerFaceIds.mp hid
  rw [cutoffTwoCubeSubsetCSPAssignment_eq_physical
      state boundary hparts.1,
    assembleReflectedSlabLabelling_lower hparts.1 hparts.2]

theorem cutoffTwoCubeSubsetClassifierInitial_satisfied
    (state boundary : EdgeLabelling) :
    SatisfiesConstraint (cutoffTwoCubeSubsetCSPAssignment state boundary)
      cutoffTwoCubeSubsetClassifierInitial := by
  unfold SatisfiesConstraint cutoffTwoCubeSubsetClassifierInitial
    cutoffTwoCubeSubsetClassifierInitialAccepts
  change decide (cutoffTwoCubeSubsetCSPAssignment state boundary 1000 =
    if cutoffTwoCubeSubsetCSPAssignment state boundary 0 = 1
    then 0 else 1) = true
  rw [cutoffTwoCubeSubsetCSPAssignment_eq_state_of_lower
      state boundary (by decide : 0 ∈ centralLowerFaceIds 0),
    cutoffTwoCubeSubsetCSPAssignment_eq_classifierState
      state boundary 0 (by omega)]
  simp [cutoffTwoCubeSubsetClassifierState]

theorem cutoffTwoCubeSubsetClassifierStep_satisfied
    (state boundary : EdgeLabelling)
    (step face : Nat) (cubeCoordinate : Bool)
    (hstep : step < 23)
    (hface : cutoffTwoCubeSubsetClassifierTailFaceIds.getD step 0 = face)
    (hcube : decide (step < 5) = cubeCoordinate)
    (hlower : face ∈ centralLowerFaceIds 0) :
    SatisfiesConstraint (cutoffTwoCubeSubsetCSPAssignment state boundary)
      (cutoffTwoCubeSubsetClassifierStep cubeCoordinate
        (1000 + step) face (1001 + step)) := by
  unfold SatisfiesConstraint cutoffTwoCubeSubsetClassifierStep
    cutoffTwoCubeSubsetClassifierStepAccepts
  change decide
    (cutoffTwoCubeSubsetCSPAssignment state boundary (1001 + step) =
      cutoffTwoCubeSubsetClassifierNext cubeCoordinate
        (cutoffTwoCubeSubsetCSPAssignment state boundary (1000 + step))
        (cutoffTwoCubeSubsetCSPAssignment state boundary face)) = true
  rw [cutoffTwoCubeSubsetCSPAssignment_eq_classifierState
      state boundary step (by omega),
    cutoffTwoCubeSubsetCSPAssignment_eq_state_of_lower
      state boundary hlower]
  have hfollowing : 1001 + step = 1000 + (step + 1) := by omega
  rw [hfollowing,
    cutoffTwoCubeSubsetCSPAssignment_eq_classifierState
      state boundary (step + 1) (by omega)]
  simp only [cutoffTwoCubeSubsetClassifierState]
  simp only [hface, hcube]
  decide

theorem cutoffTwoCubeSubsetClassifierReject_satisfied
    (state boundary : EdgeLabelling)
    (houtside : ¬ CutoffTwoCubeSubsetState state) :
    SatisfiesConstraint (cutoffTwoCubeSubsetCSPAssignment state boundary)
      cutoffTwoCubeSubsetClassifierReject := by
  unfold SatisfiesConstraint
  change cutoffTwoCubeSubsetClassifierReject.accepts
    [cutoffTwoCubeSubsetCSPAssignment state boundary 1023] = true
  rw [show 1023 = 1000 + 23 by omega,
    cutoffTwoCubeSubsetCSPAssignment_eq_classifierState
      state boundary 23 (by omega)]
  unfold cutoffTwoCubeSubsetClassifierReject
  have hterminal :=
    cutoffTwoCubeSubsetClassifierTerminal_eq_two_of_not_state houtside
  unfold cutoffTwoCubeSubsetClassifierTerminal at hterminal
  simp [hterminal]

theorem cutoffTwoCubeSubsetClassifierConstraints_satisfied
    (state boundary : EdgeLabelling)
    (houtside : ¬ CutoffTwoCubeSubsetState state) :
    Satisfies cutoffTwoCubeSubsetClassifierConstraints
      (cutoffTwoCubeSubsetCSPAssignment state boundary) := by
  intro constraint hconstraint
  simp only [cutoffTwoCubeSubsetClassifierConstraints, List.mem_cons,
    List.not_mem_nil, or_false] at hconstraint
  rcases hconstraint with hconstraint | hconstraint | hconstraint |
      hconstraint | hconstraint | hconstraint | hconstraint | hconstraint |
      hconstraint | hconstraint | hconstraint | hconstraint | hconstraint |
      hconstraint | hconstraint | hconstraint | hconstraint | hconstraint |
      hconstraint | hconstraint | hconstraint | hconstraint | hconstraint |
      hconstraint | hconstraint
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierInitial_satisfied state boundary
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 0 1 true (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 1 3 true (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 2 9 true (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 3 19 true (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 4 39 true (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 5 10 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 6 12 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 7 18 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 8 21 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 9 27 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 10 28 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 11 30 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 12 36 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 13 37 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 14 45 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 15 46 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 16 48 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 17 54 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 18 55 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 19 57 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 20 63 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 21 64 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierStep_satisfied
      state boundary 22 66 false (by omega) (by decide) (by decide) (by decide)
  · subst constraint
    exact cutoffTwoCubeSubsetClassifierReject_satisfied state boundary houtside

/-! ## The checked shared-support classifier -/

theorem cutoffTwoCubeSubsetCSPConstraints_satisfied
    (state boundary : EdgeLabelling)
    (houtside : ¬ CutoffTwoCubeSubsetState state)
    (hcube : ∀ link, link ∈ centralLowerLinks 0 →
      0 < slabExplicitLinkMultiplicity 2 1
        (assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
          zeroEdgeLabelling) link)
    (htarget : ∀ link, link ∈ centralLowerLinks 0 →
      0 < slabExplicitLinkMultiplicity 2 1
        (assembleReflectedSlabLabelling 0 state boundary
          zeroEdgeLabelling) link) :
    Satisfies cutoffTwoCubeSubsetCSPConstraints
      (cutoffTwoCubeSubsetCSPAssignment state boundary) := by
  have hclassifier :=
    cutoffTwoCubeSubsetClassifierConstraints_satisfied
      state boundary houtside
  intro constraint hconstraint
  simp only [cutoffTwoCubeSubsetCSPConstraints, List.mem_append]
    at hconstraint
  rcases hconstraint with (hconstraint | hconstraint) | hconstraint
  · rcases List.mem_map.mp hconstraint with ⟨link, hlink, rfl⟩
    exact cutoffTwoCubeSupportConstraint_satisfied
      state boundary link hlink (hcube link hlink)
  · rcases List.mem_map.mp hconstraint with ⟨link, hlink, rfl⟩
    exact cutoffTwoTargetSupportConstraint_satisfied
      state boundary link (htarget link hlink)
  · exact hclassifier constraint hconstraint

/-- Kernel-checked finite classification: any bounded target half-state that
shares one fully supported boundary word with the fundamental cube belongs
to the executable cube-subset classifier language. -/
theorem cutoffTwoCubeSubsetState_of_shared_cube_link_support
    (state boundary : EdgeLabelling)
    (hstate : state ∈ centralHalfStates 2 0)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0)
    (hcube : ∀ link, link ∈ centralLowerLinks 0 →
      0 < slabExplicitLinkMultiplicity 2 1
        (assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
          zeroEdgeLabelling) link)
    (htarget : ∀ link, link ∈ centralLowerLinks 0 →
      0 < slabExplicitLinkMultiplicity 2 1
        (assembleReflectedSlabLabelling 0 state boundary
          zeroEdgeLabelling) link) :
    CutoffTwoCubeSubsetState state := by
  have hdecidable : Decidable (CutoffTwoCubeSubsetState state) := by
    unfold CutoffTwoCubeSubsetState
    infer_instance
  cases hdecidable with
  | isTrue hcandidate => exact hcandidate
  | isFalse hcandidate =>
    have hsolution : ∃ assignment : Nat → Nat,
        AssignmentBounded assignment ∧
        Satisfies cutoffTwoCubeSubsetCSPConstraints assignment :=
      ⟨cutoffTwoCubeSubsetCSPAssignment state boundary,
        cutoffTwoCubeSubsetCSPAssignment_bounded hstate hboundary,
        cutoffTwoCubeSubsetCSPConstraints_satisfied
          state boundary hcandidate hcube htarget⟩
    exact False.elim (cutoffTwoCubeSubsetCSP_unsatisfiable hsolution)

/-! ## Half-amplitude support interface -/

theorem cutoffTwoLowerLinkMultiplicity_pos_of_halfAmplitude_ne_zero
    (state boundary : EdgeLabelling) (link : Z4Link)
    (hlink : link ∈ centralLowerLinks 0)
    (hnonzero : ¬ Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 state boundary) 0) :
    0 < slabExplicitLinkMultiplicity 2 1
      (assembleReflectedSlabLabelling 0 state boundary
        zeroEdgeLabelling) link := by
  by_cases hpositive : 0 < slabExplicitLinkMultiplicity 2 1
      (assembleReflectedSlabLabelling 0 state boundary
        zeroEdgeLabelling) link
  · exact hpositive
  · have hzero : slabExplicitLinkMultiplicity 2 1
        (assembleReflectedSlabLabelling 0 state boundary
          zeroEdgeLabelling) link = 0 := by omega
    have hproduct : slabLinkMultiplicityProductOn 2 1
        (assembleReflectedSlabLabelling 0 state boundary
          zeroEdgeLabelling) (centralLowerLinks 0) = 0 := by
      unfold slabLinkMultiplicityProductOn
      exact
        YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination.natListProduct_eq_zero_of_member
          (slabExplicitLinkMultiplicity 2 1
            (assembleReflectedSlabLabelling 0 state boundary
              zeroEdgeLabelling))
          (centralLowerLinks 0) hlink hzero
    apply False.elim
    apply hnonzero
    unfold centralHalfAmplitude centralLowerFactor
    change Q'.eqv
      (slabFaceFactorOn cutoffTwoHalfCoupling 2
          (assembleReflectedSlabLabelling 0 state boundary
            zeroEdgeLabelling) (centralLowerFaceIds 0) *
        Q'.ofNat (slabLinkMultiplicityProductOn 2 1
          (assembleReflectedSlabLabelling 0 state boundary
            zeroEdgeLabelling) (centralLowerLinks 0))) 0
    rw [hproduct]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ Q'.ofNat_zero_eqv)
      (Q'.mul_zero_eqv _)

theorem cutoffTwoCubeSubsetState_of_shared_halfAmplitude_support
    (state boundary : EdgeLabelling)
    (hstate : state ∈ centralHalfStates 2 0)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0)
    (hcube : ¬ Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerCubeState boundary) 0)
    (htarget : ¬ Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 state boundary) 0) :
    CutoffTwoCubeSubsetState state := by
  apply cutoffTwoCubeSubsetState_of_shared_cube_link_support
    state boundary hstate hboundary
  · intro link hlink
    exact cutoffTwoLowerLinkMultiplicity_pos_of_halfAmplitude_ne_zero
      centralLowerCubeState boundary link hlink hcube
  · intro link hlink
    exact cutoffTwoLowerLinkMultiplicity_pos_of_halfAmplitude_ne_zero
      state boundary link hlink htarget

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierBridge

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierBridge.cutoffTwoCubeSubsetCSPAssignment_bounded
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierBridge.cutoffTwoCubeSubsetState_of_shared_cube_link_support
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierBridge.cutoffTwoCubeSubsetState_of_shared_halfAmplitude_support
