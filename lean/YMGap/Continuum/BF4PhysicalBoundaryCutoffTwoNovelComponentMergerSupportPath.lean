/-
# A component-merger witness is a newly connected old positive state

The state semantics of a component-merger index say that its represented
state was already positive at cutoff two but lay outside the cutoff-two
vacuum component.  Because the same index lies in the later rooted component,
the constructive component compiler also supplies a literal later support
chain from the vacuum root to that state.

This file packages those facts as Type-level data.  It identifies the exact
causal event behind a merger: a previously separate cutoff-two positive state
has become connected to the vacuum through the enlarged later support graph.
The path may pass through states that were not cutoff-two positive; no claim
of a single newly opened old--old edge is made.

No merger event at a cutoff larger than two is produced.  No cofinal
stability, uniform gap, thermodynamic/continuum construction, or Clay mass
gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSupportPath

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. Type-level data for an old-state component merge -/

structure CutoffTwoOldPositiveStateMergePath (later : Nat) : Type where
  laterIndex : Nat
  laterIndex_mem : laterIndex ∈
    centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) later 0
  state_cutoffTwo_positive :
    centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
        (by decide) later 0 laterIndex ∈
      centralPositiveHalfStates cutoffTwoHalfCoupling
        (by decide) 2 0
  state_outside_cutoffTwo_vacuum :
    centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
        (by decide) later 0 laterIndex ∉
      centralPhysicalFiniteVacuumSectorStates
        cutoffTwoHalfCoupling (by decide) 2 0
  laterPath :
    ChainIn
      (centralPhysicalFiniteSupportAdjacentB
        cutoffTwoHalfCoupling (by decide) later 0)
      (centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) later 0)
      0 laterIndex

/-! ## 2. Every merger witness constructs the support path -/

def CutoffTwoComponentMergerWitness.toOldPositiveStateMergePath
    {later : Nat} (witness : CutoffTwoComponentMergerWitness later)
    (hcutoff : 2 ≤ later) :
    CutoffTwoOldPositiveStateMergePath later := by
  have hsemantics := witness.state_semantics hcutoff
  have hlaterSector : witness.index ∈
      centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) later 0 := by
    exact hsemantics.1
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) later 0 hlaterSector
  have hlaterPositive := centralPhysicalFiniteStateAt_mem_positive
    cutoffTwoHalfCoupling (by decide) later 0 hindexLt
  have hlaterHalf := (mem_centralPositiveHalfStates_iff.mp hlaterPositive).1
  have htwoHalf :
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) later 0 witness.index ∈ centralHalfStates 2 0 :=
    (mem_centralHalfStates_two_iff_labelWithin_of_mem_later hlaterHalf).mpr
      hsemantics.2.2.1
  have htwoPositive :
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) later 0 witness.index ∈
        centralPositiveHalfStates cutoffTwoHalfCoupling
          (by decide) 2 0 :=
    mem_centralPositiveHalfStates_iff.mpr
      ⟨htwoHalf, hsemantics.2.2.2⟩
  have houtsideVacuum :
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) later 0 witness.index ∉
        centralPhysicalFiniteVacuumSectorStates
          cutoffTwoHalfCoupling (by decide) 2 0 := by
    intro hstate
    exact hsemantics.2.1
      ((centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff _).mp hstate)
  have hpath :
      ChainIn
        (centralPhysicalFiniteSupportAdjacentB
          cutoffTwoHalfCoupling (by decide) later 0)
        (centralPhysicalFiniteVacuumSectorIndices
          cutoffTwoHalfCoupling (by decide) later 0)
        0 witness.index := by
    exact rootComponent_connected
      (centralPhysicalFiniteSupportAdjacentB
        cutoffTwoHalfCoupling (by decide) later 0)
      (centralPhysicalFiniteSupportAdjacentB_symmetric
        cutoffTwoHalfCoupling (by decide) later 0)
      (zero_mem_centralPhysicalFiniteIndexCarrier
        cutoffTwoHalfCoupling (by decide) later 0)
      0 witness.index
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) later 0)
      hlaterSector
  exact
    { laterIndex := witness.index
      laterIndex_mem := hlaterSector
      state_cutoffTwo_positive := htwoPositive
      state_outside_cutoffTwo_vacuum := houtsideVacuum
      laterPath := hpath }

/-! ## 3. Sanity: no such merge event exists at the equal cutoff -/

theorem no_cutoffTwoOldPositiveStateMergePath_self :
    ¬ Nonempty (CutoffTwoOldPositiveStateMergePath 2) := by
  intro hexists
  rcases hexists with ⟨event⟩
  apply event.state_outside_cutoffTwo_vacuum
  exact centralPhysicalFiniteVacuumSectorState_mem_of_index
    cutoffTwoHalfCoupling (by decide) 2 0
    event.laterIndex_mem rfl

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSupportPath

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSupportPath.CutoffTwoComponentMergerWitness.toOldPositiveStateMergePath
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSupportPath.no_cutoffTwoOldPositiveStateMergePath_self
