/-
# Normalized terminal mass splits into assigned and prefix-vacuum traffic

Loop erasure may change the assigned terminal predecessor when the raw
central-face prefix already visits the vacuum.  Nevertheless its actual final
edge is still an edge of the raw prefix-plus-spoke path.  Therefore every
state in a normalized terminal fiber has exactly the following constructive
cover: either the same edge occurred inside its raw prefix, or the edge is the
assigned final spoke and the state's repaired face-zero label matches it.

This module turns that cover into an unconditional stationary-mass bound for
the actual normalized terminal fiber.  It replaces the earlier logical fork
by two explicit analytic terms: raw prefix traffic into the vacuum and raw
assigned-label fiber mass.  Neither term is bounded uniformly here, so no
cofinal congestion certificate, finite gap, physical scaling, continuum
theory, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalSourcePreservation
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceNormalizedTerminalMassDecomposition

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalMassFactorization
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawEdgeSharing
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawTerminalFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier
open YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. States whose raw prefix uses one directed edge -/

def positiveCentralFacePrefixStateUsesDirectedEdgeB
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (state source target : Nat) : Bool :=
  if hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0 then
    if hne : state ≠ 0 then
      decide ((source, target) ∈ PositiveKernelChainIn.directedEdges
        ((positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).prefixPath
          state hstate hne))
    else false
  else false

def positiveCentralFacePrefixEdgeUsingStates
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (source target : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K 0).filter
      (positiveCentralFacePrefixStateUsesDirectedEdgeB
        hw hK · source target)

theorem mem_positiveCentralFacePrefixEdgeUsingStates_iff
    {w : Q'} (hw : (0 : Q') < w) {K state source target : Nat}
    (hK : 1 ≤ K) :
    state ∈ positiveCentralFacePrefixEdgeUsingStates
        hw hK source target ↔
      ∃ (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw) K 0)
        (hne : state ≠ 0),
        (source, target) ∈ PositiveKernelChainIn.directedEdges
          ((positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).prefixPath
            state hstate hne) := by
  constructor
  · intro hmem
    have hparts := List.mem_filter.mp hmem
    unfold positiveCentralFacePrefixStateUsesDirectedEdgeB at hparts
    rw [dif_pos hparts.1] at hparts
    by_cases hne : state ≠ 0
    · rw [dif_pos hne] at hparts
      exact ⟨hparts.1, hne, of_decide_eq_true hparts.2⟩
    · rw [dif_neg hne] at hparts
      cases hparts.2
  · rintro ⟨hstate, hne, hedge⟩
    apply List.mem_filter.mpr
    refine ⟨hstate, ?_⟩
    unfold positiveCentralFacePrefixStateUsesDirectedEdgeB
    rw [dif_pos hstate, dif_pos hne]
    exact decide_eq_true hedge

/-! ## 2. Every normalized terminal state lies in one of two raw classes -/

theorem mem_normalizedTerminalFiber_implies_prefixOrAssigned
    {w : Q'} (hw : (0 : Q') < w) {K spin state : Nat}
    (hK : 1 ≤ K) (hspin : spin ≤ K)
    (hmem : state ∈
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
        (simplePositiveCentralFaceRouting hw K hK)
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin)) :
    state ∈ positiveCentralFacePrefixEdgeUsingStates hw hK
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin) 0 ∨
      state ∈ centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin) := by
  let assignment := positiveCentralFaceSpinTerminalPrefixAssignment hw K hK
  let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
  obtain ⟨hstate, hne, hterminal⟩ :=
    mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mp hmem
  have hnonzero :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_subset_edgeUsers
      (simplePositiveCentralFaceRouting hw K hK) source state hmem
  have hnormalizedUsers := (List.mem_filter.mp hnonzero).1
  have hrawUsers :=
    loopErased_routedRootEdgeUsingStates_subset_raw
      assignment.toPositiveRouting source 0 state (by
        simpa [simplePositiveCentralFaceRouting] using hnormalizedUsers)
  obtain ⟨_hstate, hedge⟩ :=
    mem_centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates_iff.mp
      hrawUsers
  rw [assignment.toPositiveRouting_rootPath hstate hne,
    assignment.rootPath_directedEdges hstate hne] at hedge
  rcases List.mem_append.mp hedge with hprefix | hspoke
  · exact Or.inl
      (mem_positiveCentralFacePrefixEdgeUsingStates_iff
        hw hK |>.mpr ⟨hstate, hne, hprefix⟩)
  · have hpairs := List.mem_singleton.mp hspoke
    have hsource : source =
        centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
          (assignment.terminalSpin state) :=
      congrArg Prod.fst hpairs
    rw [positiveCentralFaceSpinTerminalPrefixAssignment_terminalSpin] at hsource
    have hlabel : positiveCentralFaceTerminalSpin K
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw) K 0 state 0) = spin := by
      apply centralLowerSpinCubeIndex_injective_on hw
        (positiveCentralFaceTerminalSpin_le hK) hspin
      exact hsource.symm
    exact Or.inr
      (mem_positiveCentralFaceRawTerminalFiber_iff
        hw hK hspin |>.mpr ⟨hstate, hne, hlabel⟩)

/-! ## 3. The cover gives an unconditional stationary-mass decomposition -/

def positiveCentralFacePrefixEdgeUsingStationaryMass
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (source target : Nat) : Q' :=
  listQSum
    (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0)
    (positiveCentralFacePrefixEdgeUsingStates hw hK source target)

theorem normalizedTerminalFiberStationaryMass_le_prefix_add_assigned
    {w : Q'} (hw : (0 : Q') < w) {K spin : Nat}
    (hK : 1 ≤ K) (hspin : spin ≤ K) :
    let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
        (simplePositiveCentralFaceRouting hw K hK) source ≤
      positiveCentralFacePrefixEdgeUsingStationaryMass hw hK source 0 +
        centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
          (positiveCentralFaceSpinTerminalPrefixAssignment
            hw K hK).toPositiveRouting source := by
  let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
  let normalizedFiber :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
      (simplePositiveCentralFaceRouting hw K hK) source
  let prefixUsers := positiveCentralFacePrefixEdgeUsingStates hw hK source 0
  let assignedFiber :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
      (positiveCentralFaceSpinTerminalPrefixAssignment
        hw K hK).toPositiveRouting source
  let weight := centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
  have hnormalizedNodup : normalizedFiber.Nodup := by
    unfold normalizedFiber
    unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
    exact List.filter_sublist.nodup
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        w (Q'.le_of_lt hw) K 0)
  have hsum : listQSum weight normalizedFiber ≤
      listQSum weight (prefixUsers ++ assignedFiber) := by
    apply listQSum_le_of_injective
      normalizedFiber (prefixUsers ++ assignedFiber)
      weight weight (fun state => state) hnormalizedNodup
    · intro state hstate
      rcases mem_normalizedTerminalFiber_implies_prefixOrAssigned
          hw hK hspin hstate with hprefix | hassigned
      · exact List.mem_append_left assignedFiber hprefix
      · exact List.mem_append_right prefixUsers hassigned
    · intro left _ right _ heq
      exact heq
    · intro state _
      exact Q'.le_refl' (weight state)
    · intro state _
      unfold weight centralPhysicalFiniteWeight
      exact centralPhysicalRowMarginal_nonnegative
        (Q'.le_of_lt hw) K 0 _
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (listQSum_append weight prefixUsers assignedFiber))

/-- The exact resistance demand of a normalized spin-cube terminal edge is
bounded by twice the combined raw prefix-vacuum and assigned-label mass times
that edge's reciprocal conductance. -/
theorem normalizedTerminalFiberResistanceDemand_le_prefix_add_assigned
    {w : Q'} (hw : (0 : Q') < w) {K spin : Nat}
    (hK : 1 ≤ K) (hspin : spin ≤ K) :
    let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
    let hpositive :=
      centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw hspin
    let massBound :=
      positiveCentralFacePrefixEdgeUsingStationaryMass hw hK source 0 +
        centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
          (positiveCentralFaceSpinTerminalPrefixAssignment
            hw K hK).toPositiveRouting source
    let reciprocal := Q'.recipPos
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 source 0)
      hpositive
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
        (simplePositiveCentralFaceRouting hw K hK) source hpositive ≤
      massBound * reciprocal + massBound * reciprocal := by
  let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
  let hpositive :=
    centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw hspin
  let actualMass :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
      (simplePositiveCentralFaceRouting hw K hK) source
  let massBound :=
    positiveCentralFacePrefixEdgeUsingStationaryMass hw hK source 0 +
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting source
  let reciprocal := Q'.recipPos
    (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 source 0)
    hpositive
  have hmass : actualMass ≤ massBound :=
    normalizedTerminalFiberStationaryMass_le_prefix_add_assigned
      hw hK hspin
  have hmul : actualMass * reciprocal ≤ massBound * reciprocal :=
    Q'.mul_le_mul_of_nonneg_right _ _ reciprocal hmass
      (Q'.le_of_lt (Q'.recipPos_pos _ hpositive))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (terminalFiberResistanceDemand_eqv_mass_mul_reciprocal_add_self
        (simplePositiveCentralFaceRouting hw K hK) source hpositive))
    (Q'.add_le_add hmul hmul)

/-! ## Axiom audit -/

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceNormalizedTerminalMassDecomposition

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceNormalizedTerminalMassDecomposition.mem_positiveCentralFacePrefixEdgeUsingStates_iff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceNormalizedTerminalMassDecomposition.mem_normalizedTerminalFiber_implies_prefixOrAssigned
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceNormalizedTerminalMassDecomposition.normalizedTerminalFiberStationaryMass_le_prefix_add_assigned
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceNormalizedTerminalMassDecomposition.normalizedTerminalFiberResistanceDemand_le_prefix_add_assigned
