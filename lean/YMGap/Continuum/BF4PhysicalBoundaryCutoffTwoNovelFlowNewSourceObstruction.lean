/-
# New-source obstruction in the cutoff-two novel canonical flow

The persistent old carrier has a proved cutoff-uniform row floor.  It would be
tempting to close the remaining conditional-flow denominator by claiming that
every directed occurrence can be oriented with an old source.  The literal
novel flow does not have that property.

For every genuinely new retained state and every cutoff at least two, the
ordered new-to-vacuum endpoint pair belongs to the novel endpoint list.  Its
loop-erased positive path is nontrivial, so its first directed occurrence has
that new state as source and carries strictly positive traffic.  Hence no
certificate asserting that every positive novel occurrence has an old source
can be inhabited when the new block is inhabited.

This is a diagnostic theorem about the present directed flow, not a no-go
result for all possible symmetric reorientations or alternative flows.  No
uniform row-scale estimate, payment, completed gap inhabitant,
thermodynamic/continuum construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNewSourceObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. A nontrivial positive path exposes its first directed edge -/

private theorem positivePath_exists_firstEdge_of_ne
    {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last : State}
    (path : PositiveKernelChainIn kernel support first last)
    (hne : first ≠ last) :
    ∃ next,
      (first, next) ∈
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path := by
  cases path with
  | refl state => exact False.elim (hne rfl)
  | step positive next_mem rest =>
      exact ⟨_, List.mem_cons_self⟩

private theorem positivePath_edgeLength_pos_of_ne
    {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last : State}
    (path : PositiveKernelChainIn kernel support first last)
    (hne : first ≠ last) :
    0 <
      BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
        path := by
  cases path with
  | refl state => exact False.elim (hne rfl)
  | step positive next_mem rest =>
      simp only [BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength]
      omega

private theorem q_ofNat_pos_of_nat_pos (n : Nat) (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ k => exact Q'.ofNat_succ_pos k

/-! ## 2. The vacuum root is old and every new state differs from it -/

theorem cutoffTwoVacuumRoot_mem_oldStates
    {later : Nat} (hlater : 2 ≤ later) :
    0 ∈ cutoffTwoEdgeLoadOldStates later := by
  unfold cutoffTwoEdgeLoadOldStates
  apply
    (mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff
      (w := cutoffTwoHalfCoupling) (hw := by decide)
      (half := 0) hlater).2
  unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
  apply List.mem_map.mpr
  refine ⟨0,
    zero_mem_centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0, ?_⟩
  exact centralPhysicalFiniteCutoffIndexMap_zero
    cutoffTwoHalfCoupling (by decide) 2 later 0

theorem cutoffTwoNewState_ne_vacuumRoot
    {later source : Nat}
    (hnew : source ∈ cutoffTwoEdgeLoadNewStates later) :
    source ≠ 0 := by
  intro hzero
  subst source
  have hnotEmbedded :=
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hnew).2
  apply hnotEmbedded
  unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
  apply List.mem_map.mpr
  refine ⟨0,
    zero_mem_centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0, ?_⟩
  exact centralPhysicalFiniteCutoffIndexMap_zero
    cutoffTwoHalfCoupling (by decide) 2 later 0

/-! ## 3. A genuinely positive novel occurrence has a new source -/

/-- Every new state starts one strictly positive-load occurrence in the
literal novel flow: use the ordered new-to-vacuum endpoint pair and the first
edge of its nontrivial loop-erased positive path. -/
theorem cutoffTwoNovelFlow_exists_positiveOccurrence_with_newSource
    {later source : Nat}
    (hlater : 2 ≤ later)
    (hnew : source ∈ cutoffTwoEdgeLoadNewStates later) :
    ∃ occurrence : WeightedDirectedEdgeOccurrence Nat,
      occurrence ∈ cutoffTwoNovelSimpleWeightedEdgeOccurrences later ∧
        occurrence.1.1 = source ∧
          (0 : Q') < occurrence.2 := by
  have hsourceFull : source ∈ cutoffTwoEdgeLoadFullStates later :=
    (List.mem_filter.mp hnew).1
  have hrootOld : 0 ∈ cutoffTwoEdgeLoadOldStates later :=
    cutoffTwoVacuumRoot_mem_oldStates hlater
  have hrootFull : 0 ∈ cutoffTwoEdgeLoadFullStates later :=
    (List.mem_filter.mp hrootOld).1
  have hsourceNe : source ≠ 0 :=
    cutoffTwoNewState_ne_vacuumRoot hnew
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    cutoffTwoHalfCoupling (by decide) later 0
    source 0 hsourceFull hrootFull
  obtain ⟨next, hedge⟩ := positivePath_exists_firstEdge_of_ne
    path hsourceNe
  let load :=
    (cutoffTwoEdgeLoadWeight later source *
        cutoffTwoEdgeLoadWeight later 0) *
      Q'.ofNat
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path)
  let occurrence : WeightedDirectedEdgeOccurrence Nat :=
    ((source, next), load)
  have hpairCross : (source, 0) ∈
      cutoffTwoCanonicalCrossEndpointPairs later := by
    unfold cutoffTwoCanonicalCrossEndpointPairs
    apply List.mem_append.mpr
    right
    exact (mem_cartesian_iff
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadOldStates later) (source, 0)).2
      ⟨hnew, hrootOld⟩
  have hpairNovel : (source, 0) ∈
      cutoffTwoNovelEndpointPairs later := by
    unfold cutoffTwoNovelEndpointPairs
    exact List.mem_append.mpr (Or.inr hpairCross)
  have hpathOccurrence : occurrence ∈
      cutoffTwoSimpleWeightedPathOccurrences later source 0 := by
    unfold cutoffTwoSimpleWeightedPathOccurrences
    rw [dif_pos hsourceFull, dif_pos hrootFull]
    exact List.mem_map.mpr ⟨(source, next), hedge, rfl⟩
  have hnovelOccurrence : occurrence ∈
      cutoffTwoNovelSimpleWeightedEdgeOccurrences later := by
    unfold cutoffTwoNovelSimpleWeightedEdgeOccurrences
    exact List.mem_flatMap.mpr
      ⟨(source, 0), hpairNovel, hpathOccurrence⟩
  have hsourceWeight : (0 : Q') <
      cutoffTwoEdgeLoadWeight later source :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsourceFull
  have hrootWeight : (0 : Q') <
      cutoffTwoEdgeLoadWeight later 0 :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hrootFull
  have hlengthNat : 0 <
      BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
        path :=
    positivePath_edgeLength_pos_of_ne path hsourceNe
  have hlengthQ : (0 : Q') <
      Q'.ofNat
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path) :=
    q_ofNat_pos_of_nat_pos _ hlengthNat
  have hload : (0 : Q') < load :=
    Q'.mul_pos (Q'.mul_pos hsourceWeight hrootWeight) hlengthQ
  exact ⟨occurrence, hnovelOccurrence, rfl, hload⟩

/-- Therefore the present directed novel flow cannot have every positive
occurrence sourced in the persistent old carrier whenever a new state exists.
-/
theorem no_cutoffTwoNovelFlow_allPositiveOccurrenceSourcesOld
    {later source : Nat}
    (hlater : 2 ≤ later)
    (hnew : source ∈ cutoffTwoEdgeLoadNewStates later) :
    (∀ occurrence,
      occurrence ∈ cutoffTwoNovelSimpleWeightedEdgeOccurrences later →
      (0 : Q') < occurrence.2 →
      occurrence.1.1 ∈ cutoffTwoEdgeLoadOldStates later) → False := by
  intro hallOld
  obtain ⟨occurrence, hoccurrence, hsource, hpositive⟩ :=
    cutoffTwoNovelFlow_exists_positiveOccurrence_with_newSource
      hlater hnew
  have hold := hallOld occurrence hoccurrence hpositive
  rw [hsource] at hold
  have hembedded :=
    (mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff
      (w := cutoffTwoHalfCoupling) (hw := by decide)
      (half := 0) hlater).1 hold
  exact
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hnew).2
      hembedded

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNewSourceObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNewSourceObstruction.cutoffTwoVacuumRoot_mem_oldStates
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNewSourceObstruction.cutoffTwoNewState_ne_vacuumRoot
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNewSourceObstruction.cutoffTwoNovelFlow_exists_positiveOccurrence_with_newSource
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNewSourceObstruction.no_cutoffTwoNovelFlow_allPositiveOccurrenceSourcesOld
