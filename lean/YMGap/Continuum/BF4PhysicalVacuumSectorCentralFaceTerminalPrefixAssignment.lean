/-
# Central-face spin assignment for BF4 terminal prefixes

The spin-labelled terminal-prefix compiler is constructively inhabited at
every finite cutoff.  A state is assigned to the spin read from face zero of
its represented lower-half configuration (clamped to the cutoff outside the
finite carrier).  Constructive positive connectivity supplies a prefix to the
corresponding uniform central spin cube, and the compiler appends that cube's
certified vacuum spoke.

This is a literal distributed terminal assignment: on every sector member its
selected terminal spin is exactly its own central face-zero spin.  No
cutoff-uniform sharing or resistance-load estimate for the selected prefixes
is proved here, so no spectral, continuum, or Clay conclusion follows.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCentralFaceTerminalPrefixAssignment

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment
open YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler
open YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler.CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. Every represented sector label is admitted -/

theorem centralPhysicalFiniteStateAt_faceZero_le_cutoff
    {w : Q'} {hw : (0 : Q') < w} {K state : Nat}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state 0 ≤ K := by
  have hrepresented :
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state ∈
        centralPhysicalFiniteVacuumSectorStates
          w (Q'.le_of_lt hw) K 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w (Q'.le_of_lt hw) K 0 hstate rfl
  have hhalf := centralPhysicalFiniteVacuumSectorState_mem_halfStates
    w (Q'.le_of_lt hw) K 0 hrepresented
  have hsound := boundedEdgeLabellings_sound K
    (centralLowerFaceIds 0)
    (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state)
    hhalf
  exact Nat.le_of_lt_succ
    (hsound.1 0 (by decide : 0 ∈ centralLowerFaceIds 0))

/-! ## 2. A literal finite-cutoff assignment -/

/-- Select the central face-zero spin, clamped only so the totalized function
also returns an admitted label outside the represented carrier. -/
def centralFaceSpinTerminalPrefixAssignment
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
      w hw K :=
  fun state =>
    ⟨{
      spin := Nat.min
        (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state 0) K
      spin_le := Nat.min_le_right _ _
    }, fun hstate _hne =>
      centralPhysicalFiniteVacuumSector_positiveKernelConnected
        w (Q'.le_of_lt hw) K 0 state
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
          (Nat.min
            (centralPhysicalFiniteStateAt
              w (Q'.le_of_lt hw) K 0 state 0) K))
        hstate
        (centralLowerSpinCubeIndex_mem_vacuumSector hw
          (Nat.min_le_right _ _))⟩

/-- On an actual sector member the clamp is inactive: the selected label is
literally the state label on central face zero. -/
theorem centralFaceSpinTerminalPrefixAssignment_terminalSpin
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    (centralFaceSpinTerminalPrefixAssignment hw K).terminalSpin state =
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state 0 := by
  unfold centralFaceSpinTerminalPrefixAssignment
    CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt.terminalSpin
  change Nat.min
      (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state 0) K =
    centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state 0
  exact Nat.min_eq_left
    (centralPhysicalFiniteStateAt_faceZero_le_cutoff (hw := hw) hstate)

/-! ## 3. Exact terminal source and decoded spin -/

theorem centralFaceSpinRouting_terminalSource
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        (centralFaceSpinTerminalPrefixAssignment hw K).toPositiveRouting
        state hstate =
      centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
        (centralPhysicalFiniteStateAt
          w (Q'.le_of_lt hw) K 0 state 0) := by
  rw [toPositiveRouting_terminalSource
    (centralFaceSpinTerminalPrefixAssignment hw K) hstate hne,
    centralFaceSpinTerminalPrefixAssignment_terminalSpin hw hstate]

theorem centralFaceSpinRouting_terminalSpin
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
        (centralFaceSpinTerminalPrefixAssignment hw K).toPositiveRouting
        state hstate =
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state 0 := by
  rw [toPositiveRouting_terminalSpin
    (centralFaceSpinTerminalPrefixAssignment hw K) hstate hne,
    centralFaceSpinTerminalPrefixAssignment_terminalSpin hw hstate]

end YMGap.Continuum.BF4PhysicalVacuumSectorCentralFaceTerminalPrefixAssignment

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCentralFaceTerminalPrefixAssignment.centralPhysicalFiniteStateAt_faceZero_le_cutoff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCentralFaceTerminalPrefixAssignment.centralFaceSpinTerminalPrefixAssignment
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCentralFaceTerminalPrefixAssignment.centralFaceSpinTerminalPrefixAssignment_terminalSpin
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCentralFaceTerminalPrefixAssignment.centralFaceSpinRouting_terminalSource
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCentralFaceTerminalPrefixAssignment.centralFaceSpinRouting_terminalSpin
