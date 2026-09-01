/-
# Arbitrary-cutoff delta law for the BF4 vacuum boundary row

The cutoff-two vacuum-row proof used a representation-theoretic argument that
does not depend on the value two: after deleting inserted vacuum spins, a
forcing link sees exactly one non-vacuum external representation, whose
invariant multiplicity is zero.  This module lifts that argument to every
cutoff.

Consequently the genuine half-amplitude from the vacuum lower state is
supported on the all-vacuum fixed-interface boundary at every finite cutoff.
This is the first half of the sparse root-spoke audit.  It does not yet
classify lower states whose amplitude against that boundary is positive, and
it asserts no routing, gap, continuum, or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
import YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport
import YMGap.Continuum.Z4FusionPathZeroInsertion

namespace YMGap.Continuum.BF4PhysicalBoundaryVacuumDeltaRow

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open scoped List
open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One non-vacuum boundary spin annihilates a forcing link -/

private theorem nil_sublist (A : Type) : ∀ items : List A, [] <+ items
  | [] => List.Sublist.slnil
  | head :: tail => List.Sublist.cons head (nil_sublist A tail)

private theorem singleton_sublist_of_mem {A : Type} (item : A) :
    ∀ {items : List A}, item ∈ items → [item] <+ items
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst head
        exact List.Sublist.cons₂ item (nil_sublist A tail)
      · exact List.Sublist.cons head
          (singleton_sublist_of_mem item htail)

private theorem vacuumForcingLinkMultiplicity_zero
    (K : Nat) (boundary : EdgeLabelling)
    (id : Nat) (hid : id ∈ centralFixedFaceIds 0)
    (hidNonzero : boundary id ≠ 0)
    (hidBound : boundary id ≤ K) :
    let witness := cutoffOneVacuumForcingWitness id hid
    slabExplicitLinkMultiplicity K 1
      (assembleReflectedSlabLabelling 0
        zeroEdgeLabelling boundary zeroEdgeLabelling)
      witness.link = 0 := by
  dsimp only
  let witness := cutoffOneVacuumForcingWitness id hid
  let physical := assembleReflectedSlabLabelling 0
    zeroEdgeLabelling boundary zeroEdgeLabelling
  let incidentIds := slabIncidentPlaqIds 1 witness.link
  let spins := incidentIds.map physical
  have hphysicalSelected : physical id = boundary id := by
    unfold physical
    have hparts := mem_centralFixedFaceIds.mp hid
    rw [assembleReflectedSlabLabelling_fixed hparts.1 hparts.2]
  have hphysicalOther :
      ∀ other, other ∈ incidentIds → other ≠ id →
        physical other = 0 := by
    intro other hother hne
    have hsupport := witness.incident_support other hother
    rcases hsupport with heq | hlower
    · exact False.elim (hne heq)
    · unfold physical
      have hparts := mem_centralLowerFaceIds.mp hlower
      rw [assembleReflectedSlabLabelling_lower hparts.1 hparts.2]
      rfl
  have hextension : ZeroExtension [boundary id] spins := by
    have hsub : [id] <+ incidentIds :=
      singleton_sublist_of_mem id witness.id_mem
    have hraw := ZeroExtension.map_of_sublist physical hsub
      (slabIncidentPlaqIds_nodup 1 witness.link)
      (fun other hother hnotSource =>
        hphysicalOther other hother (fun heq =>
          hnotSource (by subst other; simp)))
    simpa [spins, hphysicalSelected] using hraw
  have hincidentLength : spins.length ≤ 6 := by
    unfold spins incidentIds
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 witness.link
  have hsourceBounded :
      SpinsBounded (linkAuxiliaryCutoff K) [boundary id] := by
    intro spin hspin
    have heq : spin = boundary id := List.mem_singleton.mp hspin
    rw [heq]
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  have hextensionMultiplicity :=
    explicitValenceMultiplicity_zeroExtension hextension
      (by simp : [boundary id].length ≤ 6)
      hincidentLength hsourceBounded
  have hsourceZero :
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          [boundary id].length
          (externalSpinsOfList [boundary id]) = 0 := by
    change oneValentMultiplicity
      (linkAuxiliaryCutoff K) (boundary id) = 0
    rw [oneValentMultiplicity_eq_bool_zero]
    simp [boolMultiplicity, hidNonzero]
  unfold slabExplicitLinkMultiplicity
  change
    explicitValenceMultiplicity (linkAuxiliaryCutoff K) spins.length
        (externalSpinsOfList spins) = 0
  exact Eq.trans hextensionMultiplicity.symm hsourceZero

/-! ## 2. The arbitrary-cutoff vacuum boundary delta -/

/-- Any nonzero fixed-interface label kills the complete vacuum-source
half-amplitude, uniformly in the cutoff and coupling. -/
theorem centralHalfAmplitude_vacuum_eqv_zero_of_fixed_nonzero
    (w : Q') (K : Nat) (boundary : EdgeLabelling)
    (id : Nat) (hid : id ∈ centralFixedFaceIds 0)
    (hidNonzero : boundary id ≠ 0)
    (hidBound : boundary id ≤ K) :
    centralHalfAmplitude w K 0
        zeroEdgeLabelling boundary ≈ 0 := by
  let witness := cutoffOneVacuumForcingWitness id hid
  let physical := assembleReflectedSlabLabelling 0
    zeroEdgeLabelling boundary zeroEdgeLabelling
  have hlink :
      slabExplicitLinkMultiplicity K 1 physical witness.link = 0 := by
    exact vacuumForcingLinkMultiplicity_zero
      K boundary id hid hidNonzero hidBound
  have hproduct :
      slabLinkMultiplicityProductOn K 1 physical
        (centralLowerLinks 0) = 0 := by
    unfold slabLinkMultiplicityProductOn
    exact natListProduct_eq_zero_of_member
      (slabExplicitLinkMultiplicity K 1 physical)
      (centralLowerLinks 0) witness.link_mem hlink
  unfold centralHalfAmplitude centralLowerFactor
  change
    slabFaceFactorOn w K physical (centralLowerFaceIds 0) *
      Q'.ofNat
        (slabLinkMultiplicityProductOn K 1 physical
          (centralLowerLinks 0)) ≈ 0
  rw [hproduct]
  exact Q'.eqv_trans _
    (slabFaceFactorOn w K physical (centralLowerFaceIds 0) * 0) _
    (Q'.mul_eqv_congr_left _ _ _ Q'.ofNat_zero_eqv)
    (Q'.mul_zero_eqv _)

/-- Executable all-vacuum test on the complete fixed-interface support. -/
def centralFixedBoundaryAllZeroB (boundary : EdgeLabelling) : Bool :=
  (centralFixedFaceIds 0).all fun id => decide (boundary id = 0)

theorem centralFixedBoundaryAllZeroB_eq_true_implies_eq_zero
    (K : Nat) (boundary : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (hzero : centralFixedBoundaryAllZeroB boundary = true) :
    boundary = zeroEdgeLabelling := by
  have hbounded :=
    boundedEdgeLabellings_sound K (centralFixedFaceIds 0)
      boundary hboundary
  funext id
  unfold zeroEdgeLabelling
  by_cases hid : id ∈ centralFixedFaceIds 0
  · exact of_decide_eq_true
      (List.all_eq_true.mp hzero id hid)
  · exact hbounded.2 id hid

private theorem centralHalfAmplitude_vacuum_eqv_zero_of_list_all_false
    (w : Q') (K : Nat) (boundary : EdgeLabelling)
    (hbounded :
      ( ∀ id, id ∈ centralFixedFaceIds 0 → boundary id < K + 1) ∧
      ∀ id, id ∉ centralFixedFaceIds 0 → boundary id = 0) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → id ∈ centralFixedFaceIds 0) →
      ids.all (fun id => decide (boundary id = 0)) = false →
      centralHalfAmplitude w K 0 zeroEdgeLabelling boundary ≈ 0
  | [], _, hfalse => by
      change true = false at hfalse
      cases hfalse
  | head :: tail, hsubset, hfalse => by
      cases hhead : decide (boundary head = 0) with
      | false =>
          have hheadMem : head ∈ centralFixedFaceIds 0 :=
            hsubset head List.mem_cons_self
          exact centralHalfAmplitude_vacuum_eqv_zero_of_fixed_nonzero
            w K boundary head hheadMem (of_decide_eq_false hhead) (by
              have hlt := hbounded.1 head hheadMem
              omega)
      | true =>
          have htail :
              tail.all (fun id => decide (boundary id = 0)) = false := by
            change
              (decide (boundary head = 0) &&
                  tail.all (fun id => decide (boundary id = 0))) = false
              at hfalse
            rw [hhead] at hfalse
            exact hfalse
          exact centralHalfAmplitude_vacuum_eqv_zero_of_list_all_false
            w K boundary hbounded tail
            (fun id hid =>
              hsubset id (List.mem_cons_of_mem head hid))
            htail

/-- A failed executable all-vacuum test supplies a literal nonzero forcing
label, so the corresponding vacuum half-amplitude vanishes. -/
theorem centralHalfAmplitude_vacuum_eqv_zero_of_allZeroB_false
    (w : Q') (K : Nat) (boundary : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (hzero : centralFixedBoundaryAllZeroB boundary = false) :
    centralHalfAmplitude w K 0 zeroEdgeLabelling boundary ≈ 0 := by
  have hbounded :=
    boundedEdgeLabellings_sound K (centralFixedFaceIds 0)
      boundary hboundary
  exact centralHalfAmplitude_vacuum_eqv_zero_of_list_all_false
    w K boundary hbounded (centralFixedFaceIds 0)
    (fun id hid => hid) hzero

def centralVacuumBoundaryDeltaWeight
    (boundary : EdgeLabelling) : Q' :=
  match centralFixedBoundaryAllZeroB boundary with
  | true => 1
  | false => 0

/-- Exact constructive pointwise delta semantics of the vacuum boundary row,
phrased through its executable finite-support test. -/
theorem centralHalfAmplitude_vacuum_eqv_deltaWeight
    (w : Q') (K : Nat) (boundary : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K 0) :
    centralHalfAmplitude w K 0 zeroEdgeLabelling boundary ≈
      centralVacuumBoundaryDeltaWeight boundary := by
  cases hzero : centralFixedBoundaryAllZeroB boundary with
  | false =>
      unfold centralVacuumBoundaryDeltaWeight
      rw [hzero]
      exact centralHalfAmplitude_vacuum_eqv_zero_of_allZeroB_false
        w K boundary hboundary hzero
  | true =>
      unfold centralVacuumBoundaryDeltaWeight
      rw [hzero]
      have heq := centralFixedBoundaryAllZeroB_eq_true_implies_eq_zero
        K boundary hboundary hzero
      rw [heq]
      exact centralHalfAmplitude_vacuum_eqv_one w K 0

end YMGap.Continuum.BF4PhysicalBoundaryVacuumDeltaRow

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVacuumDeltaRow.centralHalfAmplitude_vacuum_eqv_zero_of_fixed_nonzero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVacuumDeltaRow.centralFixedBoundaryAllZeroB_eq_true_implies_eq_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVacuumDeltaRow.centralHalfAmplitude_vacuum_eqv_zero_of_allZeroB_false
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryVacuumDeltaRow.centralHalfAmplitude_vacuum_eqv_deltaWeight
