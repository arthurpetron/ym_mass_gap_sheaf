/-
# Production bridge for cutoff-two fixed-interface link factors

The sparse cube contraction uses literal arity-zero-through-six tables.
Their entries are audited in independent modules.  The ternary radix theorem
turns those whole-table equalities into pointwise lookup equalities, while
the zero-extension theorem below identifies the resulting active word with
the genuine production SU(2) link multiplicity on an assembled
`zero / boundary / zero` slab.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixCertificate
import YMGap.Continuum.FiniteScopedFactorTernaryRadixLookup

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFixedLinkBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableFive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryFactorGraph
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTernaryRadixLookup
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The audited table family -/

theorem cutoffTwoExpectedMultiplicityTable_eq_computed
    (arity : Nat) (harity : arity ≤ 6) :
    cutoffTwoExpectedMultiplicityTablesUpToSix.getD arity [] =
      (allSeqs 3 arity).map cutoffTwoActiveMultiplicity := by
  have hcases :
      arity = 0 ∨ arity = 1 ∨ arity = 2 ∨ arity = 3 ∨
        arity = 4 ∨ arity = 5 ∨ arity = 6 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · simpa [cutoffTwoExpectedMultiplicityTablesUpToSix] using
      cutoffTwoMultiplicityTableFive_checked.symm
  · simpa [cutoffTwoMultiplicityTableSixComputed,
      cutoffTwoMultiplicityTableSixLiteral,
      cutoffTwoExpectedMultiplicityTablesUpToSix] using
        cutoffTwoMultiplicityTableSix_eq_literal.symm

theorem cutoffTwoFixedMultiplicityQTable_eq_computed
    (arity : Nat) (harity : arity ≤ 6) :
    cutoffTwoFixedMultiplicityQTable arity =
      (allSeqs 3 arity).map
        (fun spins => Q'.ofNat (cutoffTwoActiveMultiplicity spins)) := by
  unfold cutoffTwoFixedMultiplicityQTable
  rw [cutoffTwoExpectedMultiplicityTable_eq_computed arity harity]
  simp only [List.map_map]
  apply List.map_congr_left
  intro spins _
  rfl

/-! ## 2. Zero-extension at one fixed link -/

def cutoffTwoFixedActiveSpins
    (physical : EdgeLabelling) (link : Z4Link) : List Nat :=
  (cutoffTwoFixedIncidentFaceIds link).map physical

theorem slabExplicitLinkMultiplicity_cutoffTwo_eq_fixedActive
    (physical : EdgeLabelling) (link : Z4Link)
    (hbounded : ∀ faceId,
      faceId ∈ slabIncidentPlaqIds 1 link → physical faceId ≤ 2)
    (hzero : ∀ faceId,
      faceId ∈ slabIncidentPlaqIds 1 link →
        faceId ∉ centralFixedFaceIds 0 → physical faceId = 0) :
    slabExplicitLinkMultiplicity 2 1 physical link =
      cutoffTwoActiveMultiplicity
        (cutoffTwoFixedActiveSpins physical link) := by
  let active := cutoffTwoFixedActiveSpins physical link
  let incident := (slabIncidentPlaqIds 1 link).map physical
  have hextension : ZeroExtension active incident := by
    unfold active cutoffTwoFixedActiveSpins
      cutoffTwoFixedIncidentFaceIds incident
    apply ZeroExtension.map_of_sublist physical List.filter_sublist
      (slabIncidentPlaqIds_nodup 1 link)
    intro faceId hface hnotActive
    apply hzero faceId hface
    intro hfixed
    apply hnotActive
    exact List.mem_filter.mpr ⟨hface, by simp only [hfixed, decide_true]⟩
  have hactiveLength : active.length ≤ 6 := by
    unfold active cutoffTwoFixedActiveSpins cutoffTwoFixedIncidentFaceIds
    rw [List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _)
      (slabIncidentPlaqIds_length_le_six 1 link)
  have hincidentLength : incident.length ≤ 6 := by
    unfold incident
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 link
  have hactiveBounded :
      SpinsBounded (linkAuxiliaryCutoff 2) active := by
    intro spin hspin
    unfold active cutoffTwoFixedActiveSpins at hspin
    rcases List.mem_map.mp hspin with ⟨faceId, hface, rfl⟩
    have hincident := (List.mem_filter.mp hface).1
    have hle := hbounded faceId hincident
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  unfold slabExplicitLinkMultiplicity cutoffTwoActiveMultiplicity
  change
    explicitValenceMultiplicity (linkAuxiliaryCutoff 2) incident.length
        (externalSpinsOfList incident) =
      explicitValenceMultiplicity (linkAuxiliaryCutoff 2) active.length
        (externalSpinsOfList active)
  exact (explicitValenceMultiplicity_zeroExtension
    hextension hactiveLength hincidentLength hactiveBounded).symm

private theorem assembled_zero_off_fixed
    (boundary : EdgeLabelling) (link : Z4Link) (faceId : Nat)
    (hface : faceId ∈ slabIncidentPlaqIds 1 link)
    (hnotFixed : faceId ∉ centralFixedFaceIds 0) :
    assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
        zeroEdgeLabelling faceId = 0 := by
  have hphysical : faceId ∈ slabPhysicalFaceEdges 1 :=
    slabIncidentPlaqId_physical hface
  cases hside : plaquetteHalfSide 0 (slabPlaquetteAt 1 faceId)
  · exact assembleReflectedSlabLabelling_lower hphysical hside
  · exact absurd
      (mem_centralFixedFaceIds.mpr ⟨hphysical, hside⟩) hnotFixed
  · rw [assembleReflectedSlabLabelling_upper hphysical hside]
    rfl

private theorem fixedActiveSpins_assembled_eq_boundary
    (boundary : EdgeLabelling) (link : Z4Link) :
    cutoffTwoFixedActiveSpins
        (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
          zeroEdgeLabelling) link =
      (cutoffTwoFixedIncidentFaceIds link).map boundary := by
  unfold cutoffTwoFixedActiveSpins
  apply List.map_congr_left
  intro faceId hface
  have hparts := List.mem_filter.mp hface
  have hfixed : faceId ∈ centralFixedFaceIds 0 :=
    of_decide_eq_true hparts.2
  have hfixedParts := mem_centralFixedFaceIds.mp hfixed
  exact assembleReflectedSlabLabelling_fixed
    hfixedParts.1 hfixedParts.2

/-! ## 3. Literal factor equals the genuine production factor -/

theorem cutoffTwoFixedLinkTableFactor_value_eq_active
    (link : Z4Link) (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0)) :
    (cutoffTwoFixedLinkTableFactor link).value boundary =
      Q'.ofNat (cutoffTwoActiveMultiplicity
        ((cutoffTwoFixedIncidentFaceIds link).map boundary)) := by
  have harity : (cutoffTwoFixedIncidentFaceIds link).length ≤ 6 := by
    unfold cutoffTwoFixedIncidentFaceIds
    exact Nat.le_trans (List.length_filter_le _ _)
      (slabIncidentPlaqIds_length_le_six 1 link)
  have hsound := boundedEdgeLabellings_sound 2
    (centralFixedFaceIds 0) boundary hboundary
  change scopedTableValue 3 (cutoffTwoFixedIncidentFaceIds link)
      (cutoffTwoFixedMultiplicityQTable
        (cutoffTwoFixedIncidentFaceIds link).length) boundary = _
  unfold scopedTableValue
  rw [cutoffTwoFixedMultiplicityQTable_eq_computed _ harity]
  apply scopedTableValue_map_allSeqs_three
  intro faceId hface
  have hfixed : faceId ∈ centralFixedFaceIds 0 := by
    have hparts := List.mem_filter.mp hface
    exact of_decide_eq_true hparts.2
  exact hsound.1 faceId hfixed

theorem cutoffTwoFixedLinkTableFactor_eqv_production
    (link : Z4Link) (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0)) :
    (cutoffTwoFixedLinkTableFactor link).value boundary ≈
      centralHalfLinkLocalFactor 2 0 zeroEdgeLabelling boundary link := by
  have hzeroMem := zeroEdgeLabelling_mem_centralHalfStates 2 0
  have hassembledBounded := assembleReflectedSlabLabelling_bounded
    hzeroMem hboundary hzeroMem
  have hproduction :=
    slabExplicitLinkMultiplicity_cutoffTwo_eq_fixedActive
      (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
        zeroEdgeLabelling) link
      (fun faceId hface =>
        hassembledBounded faceId (slabIncidentPlaqId_physical hface))
      (assembled_zero_off_fixed boundary link)
  rw [cutoffTwoFixedLinkTableFactor_value_eq_active link boundary hboundary]
  unfold centralHalfLinkLocalFactor
  change Q'.ofNat (cutoffTwoActiveMultiplicity
      ((cutoffTwoFixedIncidentFaceIds link).map boundary)) ≈
    Q'.ofNat
      (slabExplicitLinkMultiplicity 2 1
        (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
          zeroEdgeLabelling) link)
  rw [hproduction, fixedActiveSpins_assembled_eq_boundary]
  exact Q'.eqv_refl _

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFixedLinkBridge

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFixedLinkBridge.cutoffTwoExpectedMultiplicityTable_eq_computed
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFixedLinkBridge.slabExplicitLinkMultiplicity_cutoffTwo_eq_fixedActive
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFixedLinkBridge.cutoffTwoFixedLinkTableFactor_eqv_production
