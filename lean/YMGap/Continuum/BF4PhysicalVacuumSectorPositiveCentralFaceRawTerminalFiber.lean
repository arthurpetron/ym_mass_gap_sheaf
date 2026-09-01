/-
# Exact terminal fibers of the raw positive central-face BF4 routing

The raw routing sends each non-vacuum state through the spin cube selected by
its repaired central face-zero label.  This module identifies the terminal
fiber over an admitted spin-cube spoke exactly with that label fiber.  It also
records the resulting necessary lower bound on raw edge sharing.

This is a finite classification and obstruction interface, not a uniform
fiber bound.  No cofinal congestion certificate, finite gap, physical scaling,
continuum theory, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawEdgeSharing

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawTerminalFiber

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier
open YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler
open YMGap.Continuum.FiniteBoolGraphSimplePaths

/-! ## 1. The raw terminal fiber is exactly a repaired face-zero fiber -/

theorem mem_positiveCentralFaceRawTerminalFiber_iff
    {w : Q'} (hw : (0 : Q') < w) {K spin state : Nat}
    (hK : 1 ≤ K) (hspin : spin ≤ K) :
    state ∈
        centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
          (positiveCentralFaceSpinTerminalPrefixAssignment
            hw K hK).toPositiveRouting
          (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin) ↔
      ∃ (_hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw) K 0)
        (_hne : state ≠ 0),
        positiveCentralFaceTerminalSpin K
            (centralPhysicalFiniteStateAt
              w (Q'.le_of_lt hw) K 0 state 0) = spin := by
  constructor
  · intro hmem
    obtain ⟨hstate, hne, hterminal⟩ :=
      mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mp
        hmem
    refine ⟨hstate, hne, ?_⟩
    have hselected :=
      positiveCentralFaceSpinRouting_terminalSource hw hK hstate hne
    apply centralLowerSpinCubeIndex_injective_on hw
      (positiveCentralFaceTerminalSpin_le hK) hspin
    exact hselected.symm.trans hterminal
  · rintro ⟨hstate, hne, hlabel⟩
    apply
      mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mpr
    refine ⟨hstate, hne, ?_⟩
    rw [positiveCentralFaceSpinRouting_terminalSource hw hK hstate hne,
      hlabel]

/-! ## 2. Every repaired label fiber is a terminal-edge sharing burden -/

theorem positiveCentralFaceRawTerminalFiber_length_le_edgeUsers
    {w : Q'} (hw : (0 : Q') < w) {K spin : Nat}
    (hK : 1 ≤ K) (_hspin : spin ≤ K) :
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin)).length ≤
      (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin) 0).length := by
  apply FiniteListBound.nodup_subset_length_le
  · unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
    exact List.filter_sublist.nodup
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        w (Q'.le_of_lt hw) K 0)
  · intro state hstate
    have hnonzero :=
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_subset_edgeUsers
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin)
        state hstate
    exact (List.mem_filter.mp hnonzero).1

namespace FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad

theorem terminalLabelFiber_cardinality_le_sharingBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      BF4PhysicalVacuumSectorPositiveCentralFaceRawEdgeSharing.FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad
        hw)
    (K : Nat) (hK : family.start ≤ K)
    (spin : Nat) (hspin : spin ≤ K) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
          (positiveCentralFaceSpinTerminalPrefixAssignment hw K
            (Nat.le_trans family.start_positive hK)).toPositiveRouting
          (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin)).length ≤
      family.sharingBound := by
  have hlength := positiveCentralFaceRawTerminalFiber_length_le_edgeUsers
    hw (Nat.le_trans family.start_positive hK) hspin
  exact Q'.le_trans' _ _ _
    (Q'.ofNat_le_ofNat hlength)
    (family.rawEdgeUsers_cardinality_le K hK
      (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin) 0)

end FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawTerminalFiber

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawTerminalFiber.mem_positiveCentralFaceRawTerminalFiber_iff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawTerminalFiber.positiveCentralFaceRawTerminalFiber_length_le_edgeUsers
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawTerminalFiber.FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad.terminalLabelFiber_cardinality_le_sharingBound
