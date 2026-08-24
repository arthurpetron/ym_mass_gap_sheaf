/-
# First boundary exit of a component-merger support path

A component-merger path starts at the vacuum root inside the embedded
cutoff-two vacuum component and ends at a state outside that image.  Finite
recursion over the Type-level `ChainIn` therefore locates a literal later
support edge whose source is still in the embedded old image and whose target
is outside it.

The target is then classified by the existing exact shell split: it is either
outside the whole cutoff-two positive carrier or is itself a component-merger
state.  This is the local causal interface needed for a support-stability or
bridge-mass estimate.

No larger-cutoff merger or boundary edge is produced unconditionally.  No
cofinal stability, uniform gap, thermodynamic/continuum construction, or Clay
mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSupportPath

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerBoundaryExit

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSupportPath
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteBoolGraphComponents

/-! ## 1. Generic constructive first exit from a finite sublist -/

private structure ChainListBoundaryExit
    (adjacent : Nat → Nat → Bool)
    (support old : List Nat) : Type where
  source : Nat
  target : Nat
  source_mem_old : source ∈ old
  target_not_mem_old : target ∉ old
  target_mem_support : target ∈ support
  edge : adjacent source target = true

private def chainListBoundaryExit
    (adjacent : Nat → Nat → Bool)
    (support old : List Nat) :
    {start finish : Nat} →
      ChainIn adjacent support start finish →
      start ∈ old → finish ∉ old →
      ChainListBoundaryExit adjacent support old
  | start, _, ChainIn.refl _, hstart, hfinish =>
      False.elim (hfinish hstart)
  | start, _, ChainIn.step (b := next) hedge hnext rest,
      hstart, hfinish => by
      by_cases hnextOld : next ∈ old
      · exact chainListBoundaryExit adjacent support old
          rest hnextOld hfinish
      · exact
          { source := start
            target := next
            source_mem_old := hstart
            target_not_mem_old := hnextOld
            target_mem_support := hnext
            edge := hedge }

/-! ## 2. A literal edge leaving the embedded cutoff-two vacuum image -/

structure CutoffTwoEmbeddedVacuumBoundaryExit (later : Nat) : Type where
  source : Nat
  target : Nat
  source_mem_embedded : source ∈
    centralPhysicalFiniteEmbeddedVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0
  target_not_mem_embedded : target ∉
    centralPhysicalFiniteEmbeddedVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0
  source_mem_later_sector : source ∈
    centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) later 0
  target_mem_later_sector : target ∈
    centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) later 0
  edge :
    centralPhysicalFiniteSupportAdjacentB
      cutoffTwoHalfCoupling (by decide) later 0 source target = true

def CutoffTwoOldPositiveStateMergePath.toEmbeddedVacuumBoundaryExit
    {later : Nat} (event : CutoffTwoOldPositiveStateMergePath later)
    (hcutoff : 2 ≤ later) :
    CutoffTwoEmbeddedVacuumBoundaryExit later := by
  let old := centralPhysicalFiniteEmbeddedVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) 2 later 0
  have hrootOld : 0 ∈ old := by
    unfold old centralPhysicalFiniteEmbeddedVacuumSectorIndices
    apply List.mem_map.mpr
    refine ⟨0,
      zero_mem_centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0,
      ?_⟩
    exact centralPhysicalFiniteCutoffIndexMap_zero
      cutoffTwoHalfCoupling (by decide) 2 later 0
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) later 0 event.laterIndex_mem
  have hendOutside : event.laterIndex ∉ old := by
    intro himage
    apply event.state_outside_cutoffTwo_vacuum
    exact
      (YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding.mem_centralPhysicalFiniteEmbeddedVacuumSectorIndices_iff_state_mem
        hcutoff hindexLt).mp himage
  let exit := chainListBoundaryExit
    (centralPhysicalFiniteSupportAdjacentB
      cutoffTwoHalfCoupling (by decide) later 0)
    (centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) later 0)
    old event.laterPath hrootOld hendOutside
  exact
    { source := exit.source
      target := exit.target
      source_mem_embedded := exit.source_mem_old
      target_not_mem_embedded := exit.target_not_mem_old
      source_mem_later_sector :=
        centralPhysicalFiniteEmbeddedVacuumSectorIndices_mem_later
          hcutoff exit.source_mem_old
      target_mem_later_sector := exit.target_mem_support
      edge := exit.edge }

def CutoffTwoComponentMergerWitness.toEmbeddedVacuumBoundaryExit
    {later : Nat} (witness : CutoffTwoComponentMergerWitness later)
    (hcutoff : 2 ≤ later) :
    CutoffTwoEmbeddedVacuumBoundaryExit later :=
  CutoffTwoOldPositiveStateMergePath.toEmbeddedVacuumBoundaryExit
    (YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSupportPath.CutoffTwoComponentMergerWitness.toOldPositiveStateMergePath
      witness hcutoff) hcutoff

/-! ## 3. The first target belongs to exactly one shell class -/

structure CutoffTwoBoundaryExitOutsidePositiveTarget
    (later : Nat) : Type where
  boundary : CutoffTwoEmbeddedVacuumBoundaryExit later
  target_mem : boundary.target ∈ cutoffTwoNewOutsidePositiveIndices later

structure CutoffTwoBoundaryExitComponentMergerTarget
    (later : Nat) : Type where
  boundary : CutoffTwoEmbeddedVacuumBoundaryExit later
  target_mem : boundary.target ∈ cutoffTwoNewComponentMergerIndices later

def CutoffTwoEmbeddedVacuumBoundaryExit.targetShellDecision
    {later : Nat} (boundary : CutoffTwoEmbeddedVacuumBoundaryExit later) :
    Sum (CutoffTwoBoundaryExitOutsidePositiveTarget later)
      (CutoffTwoBoundaryExitComponentMergerTarget later) := by
  have hnew : boundary.target ∈ cutoffTwoEdgeLoadNewStates later := by
    unfold cutoffTwoEdgeLoadNewStates
    exact
      (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff).mpr
        ⟨boundary.target_mem_later_sector,
          boundary.target_not_mem_embedded⟩
  cases houtside :
      cutoffTwoNewStateOutsidePositiveCarrierB later boundary.target with
  | false =>
      exact Sum.inr
        { boundary := boundary
          target_mem := by
            unfold cutoffTwoNewComponentMergerIndices
            apply List.mem_filter.mpr
            exact ⟨hnew, by simp only [houtside, Bool.not_false]⟩ }
  | true =>
      exact Sum.inl
        { boundary := boundary
          target_mem := by
            unfold cutoffTwoNewOutsidePositiveIndices
            exact List.mem_filter.mpr ⟨hnew, houtside⟩ }

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerBoundaryExit

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerBoundaryExit.CutoffTwoOldPositiveStateMergePath.toEmbeddedVacuumBoundaryExit
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerBoundaryExit.CutoffTwoComponentMergerWitness.toEmbeddedVacuumBoundaryExit
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerBoundaryExit.CutoffTwoEmbeddedVacuumBoundaryExit.targetShellDecision
