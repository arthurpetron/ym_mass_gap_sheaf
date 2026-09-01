/-
# Conditional preservation of the positive central-face terminal source

The raw central-face route appends the assigned spin-cube-to-vacuum spoke to
a vertex-simple prefix.  Its loop-erased normalization preserves that
assigned terminal predecessor as soon as the prefix itself does not visit the
vacuum.  This module proves that implication and then identifies the actual
normalized terminal fiber with the repaired central face-zero fiber.

The remaining condition is kept as honest Type-level data:
`PositiveCentralFacePrefixVacuumAvoidanceAt`.  No inhabitant is constructed
here.  Without it, the already-proved raw fiber classification must not be
silently transferred to the loop-erased routing.

This is a conditional finite-routing theorem, not a cutoff-uniform avoidance
proof, congestion certificate, finite gap, physical scaling, continuum
theory, or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalMassFactorization

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalSourcePreservation

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier
open YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler
open YMGap.Continuum.FiniteBoolGraphSimplePaths

/-! ## 1. Loop erasure is the identity on a vertex-simple walk -/

private theorem walk_eraseLoops_eq_of_nodup
    {State : Type} {edge : State → State → Bool} [DecidableEq State] :
    ∀ {first last : State} (path : Walk edge first last),
      path.vertices.Nodup → (Walk.eraseLoops path).walk = path
  | _, _, Walk.single _, _ => rfl
  | first, last, Walk.cons hedge rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      have ih := walk_eraseLoops_eq_of_nodup rest hparts.2
      simp only [Walk.eraseLoops]
      by_cases hfirst : first ∈ (Walk.eraseLoops rest).walk.vertices
      · have : first ∈ rest.vertices := by
          rw [← ih]
          exact hfirst
        exact False.elim (hparts.1 this)
      · rw [dif_neg hfirst]
        exact congrArg (Walk.cons hedge) ih

private theorem supportedWalkOfPositivePath_vertices
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    ∀ (path : PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw K 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        left right),
      Walk.vertices
          (centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath
            hleft path) =
        PositiveKernelChainIn.vertices path
  | PositiveKernelChainIn.refl _ => rfl
  | PositiveKernelChainIn.step (next := next) _ hnext rest => by
      simp only [centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath,
        Walk.vertices, PositiveKernelChainIn.vertices]
      exact congrArg (List.cons left)
        (supportedWalkOfPositivePath_vertices hnext rest)

private theorem terminalSource_ofSupportedWalkOfPositivePath
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    ∀ (path : PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw K 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        left right),
      PositiveKernelChainIn.terminalSource
          (PositiveKernelChainIn.ofSupportedWalk
            (centralPhysicalFiniteSupportAdjacentB w hw K 0)
            (centralPhysicalFiniteKernel w hw K 0)
            (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
            (fun _first _next hfirst hnext hedge =>
              centralPhysicalFiniteKernel_pos_of_supportAdjacent
                hfirst hnext hedge)
            hleft
            (centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath
              hleft path)) =
        PositiveKernelChainIn.terminalSource path
  | PositiveKernelChainIn.refl _ => rfl
  | PositiveKernelChainIn.step positive hnext
      (PositiveKernelChainIn.refl _) => rfl
  | PositiveKernelChainIn.step positive hnext
      (PositiveKernelChainIn.step nextPositive hafter tail) => by
      simp only [centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath,
        PositiveKernelChainIn.ofSupportedWalk,
        PositiveKernelChainIn.terminalSource]
      exact terminalSource_ofSupportedWalkOfPositivePath hnext
        (PositiveKernelChainIn.step nextPositive hafter tail)

/-- Loop erasure preserves the terminal predecessor of any BF4 path whose
literal vertex sequence is already duplicate-free. -/
theorem loopErasedPositivePath_terminalSource_eq_of_vertices_nodup
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (path : PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      left right)
    (hnodup : (PositiveKernelChainIn.vertices path).Nodup) :
    PositiveKernelChainIn.terminalSource
        (centralPhysicalFiniteVacuumSectorLoopErasedPositivePath hleft path) =
      PositiveKernelChainIn.terminalSource path := by
  let walk :=
    centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath hleft path
  have hwalk : (Walk.vertices walk).Nodup := by
    rw [supportedWalkOfPositivePath_vertices hleft path]
    exact hnodup
  have herase : (Walk.eraseLoops walk).walk = walk :=
    walk_eraseLoops_eq_of_nodup walk hwalk
  unfold centralPhysicalFiniteVacuumSectorLoopErasedPositivePath
  rw [herase]
  exact terminalSource_ofSupportedWalkOfPositivePath hleft path

/-! ## 2. Appending the vacuum spoke preserves simplicity under avoidance -/

private theorem positiveKernelChain_vertices_trans_single
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    ∀ {first middle last : State}
      (prefixPath : PositiveKernelChainIn kernel support first middle)
      (positive : (0 : Q') < kernel middle last)
      (hlast : last ∈ support),
      PositiveKernelChainIn.vertices
          (prefixPath.trans
            (PositiveKernelChainIn.step positive hlast
              (PositiveKernelChainIn.refl last))) =
        PositiveKernelChainIn.vertices prefixPath ++ [last]
  | _, _, _, PositiveKernelChainIn.refl _, _, _ => rfl
  | first, middle, last,
      PositiveKernelChainIn.step positive hnext rest,
      terminalPositive, hlast => by
      simp only [PositiveKernelChainIn.trans, PositiveKernelChainIn.vertices,
        List.cons_append]
      exact congrArg (List.cons first)
        (positiveKernelChain_vertices_trans_single
          rest terminalPositive hlast)

private theorem positiveCentralFacePrefixPath_vertices_nodup
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    (PositiveKernelChainIn.vertices
      ((positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).prefixPath
        state hstate hne)).Nodup := by
  change
    (PositiveKernelChainIn.vertices
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        w (Q'.le_of_lt hw) K 0 state
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
          (positiveCentralFaceTerminalSpin K
            (centralPhysicalFiniteStateAt
              w (Q'.le_of_lt hw) K 0 state 0)))
        hstate
        (centralLowerSpinCubeIndex_mem_vacuumSector hw
          (positiveCentralFaceTerminalSpin_le hK)))).Nodup
  unfold centralPhysicalFiniteVacuumSectorSimplePositivePath
  rw [PositiveKernelChainIn.vertices_ofSupportedWalk]
  exact
    (centralPhysicalFiniteVacuumSectorSimpleWalk
      w (Q'.le_of_lt hw) K 0 state
      (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
        (positiveCentralFaceTerminalSpin K
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw) K 0 state 0)))
      hstate
      (centralLowerSpinCubeIndex_mem_vacuumSector hw
        (positiveCentralFaceTerminalSpin_le hK))).nodup

/-- The one missing condition for source preservation at a fixed cutoff:
every non-vacuum state's canonical prefix avoids the vacuum vertex. -/
structure PositiveCentralFacePrefixVacuumAvoidanceAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K) : Type where
  avoids : ∀ state,
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) →
    (hne : state ≠ 0) →
    0 ∉ PositiveKernelChainIn.vertices
      ((positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).prefixPath
        state hstate hne)

theorem positiveCentralFaceRawRootPath_vertices_nodup
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (avoidance : PositiveCentralFacePrefixVacuumAvoidanceAt hw K hK)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    (PositiveKernelChainIn.vertices
      ((positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).rootPath
        state hstate hne)).Nodup := by
  unfold CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt.rootPath
  unfold centralLowerSpinCubeToVacuumSpoke
  rw [positiveKernelChain_vertices_trans_single]
  apply List.nodup_append.mpr
  refine ⟨positiveCentralFacePrefixPath_vertices_nodup hw hK hstate hne,
    List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
  intro left hleft right hright heq
  have hright : right = 0 := List.mem_singleton.mp hright
  rw [heq, hright] at hleft
  exact avoidance.avoids state hstate hne hleft

/-! ## 3. Assigned terminal sources and repaired fibers survive normalization -/

theorem simplePositiveCentralFaceRouting_terminalSource_eq_assigned
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (avoidance : PositiveCentralFacePrefixVacuumAvoidanceAt hw K hK)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        (simplePositiveCentralFaceRouting hw K hK) state hstate =
      centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
        (positiveCentralFaceTerminalSpin K
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw) K 0 state 0)) := by
  let assignment := positiveCentralFaceSpinTerminalPrefixAssignment hw K hK
  have hpreserve :=
    loopErasedPositivePath_terminalSource_eq_of_vertices_nodup
      hstate (assignment.rootPath state hstate hne)
      (positiveCentralFaceRawRootPath_vertices_nodup
        hw hK avoidance hstate hne)
  have hraw :=
    CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt.rootPath_terminalSource
      assignment hstate hne
  rw [positiveCentralFaceSpinTerminalPrefixAssignment_terminalSpin] at hraw
  unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
  unfold simplePositiveCentralFaceRouting
  unfold loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
  change PositiveKernelChainIn.terminalSource
      (centralPhysicalFiniteVacuumSectorLoopErasedPositivePath hstate
        ((positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).toPositiveRouting.path
          state 0 hstate _)) = _
  rw [(positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).toPositiveRouting_rootPath
    hstate hne]
  exact hpreserve.trans hraw

theorem mem_simplePositiveCentralFaceTerminalFiber_iff
    {w : Q'} (hw : (0 : Q') < w) {K spin state : Nat}
    (hK : 1 ≤ K)
    (avoidance : PositiveCentralFacePrefixVacuumAvoidanceAt hw K hK)
    (hspin : spin ≤ K) :
    state ∈
        centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
          (simplePositiveCentralFaceRouting hw K hK)
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
      simplePositiveCentralFaceRouting_terminalSource_eq_assigned
        hw hK avoidance hstate hne
    apply centralLowerSpinCubeIndex_injective_on hw
      (positiveCentralFaceTerminalSpin_le hK) hspin
    exact hselected.symm.trans hterminal
  · rintro ⟨hstate, hne, hlabel⟩
    apply
      mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mpr
    refine ⟨hstate, hne, ?_⟩
    rw [simplePositiveCentralFaceRouting_terminalSource_eq_assigned
      hw hK avoidance hstate hne, hlabel]

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalSourcePreservation

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalSourcePreservation.loopErasedPositivePath_terminalSource_eq_of_vertices_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalSourcePreservation.positiveCentralFaceRawRootPath_vertices_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalSourcePreservation.simplePositiveCentralFaceRouting_terminalSource_eq_assigned
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalSourcePreservation.mem_simplePositiveCentralFaceTerminalFiber_iff
