/-
# Multiplicity-faithful all-source production transport

The representative production pair carrier is collision-free at both
marginals, but representative selection discards the source multiplicity
whose total weight carries the explicit `41/425` success estimate.  This
module instead compiles every successful all-target source into the literal
production BF4 expanded carrier.

The source compiler is injective on the complete successful-source carrier,
so its production source marginal is duplicate-free and preserves the full
successful weight.  The target compiler is also defined and accepted for
every successful source, but its marginal deliberately retains collisions;
the existing exact target key has fibers of cardinality at most sixty-four.

This is a weighted many-to-one transport certificate on the full reflected
slab.  It is not yet the actual BF4 conditional/OS joint.  No posterior
variance, OS form bound, spectral gap, beta/lattice-spacing uniformity, or
continuum theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchCardinality
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSuccessFraction
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Every successful source compiles into the production carrier -/

private theorem globalAllSource_mem_own_block
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    source.entry ∈ cubeInwardMateCertifiedTargetFullSources
      K source.physical hK
        (cubeInwardMatePhysicalBoundedOfMem
          K source.physical source.physicalSource.2) := by
  unfold globalCubeInwardMateCertifiedTargetFullSources at hsource
  obtain ⟨physicalSource, _hphysicalSource, hblock⟩ :=
    List.mem_flatMap.mp hsource
  unfold globalCubeInwardMateCertifiedTargetFullSourceBlock at hblock
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hblock
  cases heq
  exact hentry

/-- Every successful source, not merely a selected target representative,
occurs in its complete classified source carrier. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome_mem_allSources
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome source ∈
      cubeInwardMateCertifiedOutcomeFullSources
        K source.physical hK
          (cubeInwardMatePhysicalBoundedOfMem
            K source.physical source.physicalSource.2) := by
  have hentry := globalAllSource_mem_own_block source hsource
  have hparts := (mem_cartesian_iff
    (cubeInwardMateCertifiedTargetAssignments
      K source.physical hK
        (cubeInwardMatePhysicalBoundedOfMem
          K source.physical source.physicalSource.2))
    (cubeInwardMateOffCubeFusionWitnessAssignments
      K source.physical).attach source.entry).mp hentry
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome
    cubeInwardMateCertifiedOutcomeFullSources
  apply (mem_cartesian_iff _ _ _).mpr
  refine ⟨?_, hparts.2⟩
  exact (mem_sumInlValues_iff
    (cubeInwardMateCertifiedSourceOutcomes
      K source.physical hK
        (cubeInwardMatePhysicalBoundedOfMem
          K source.physical source.physicalSource.2))).mp hparts.1

/-- Every successful source word occurs in the complete written source-code
carrier used by the equal-rank production compiler. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode_mem_allSources
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode source ∈
      cubeInwardMateCertifiedOutcomeFullSourceCodes
        K source.physical hK
          (cubeInwardMatePhysicalBoundedOfMem
            K source.physical source.physicalSource.2) := by
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode
    cubeInwardMateCertifiedOutcomeFullSourceCodes
  exact List.mem_map.mpr
    ⟨GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome source,
      GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome_mem_allSources
        source hsource,
      rfl⟩

/-- The production source assignment of every successful source is an
accepted member of its literal production fiber. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw_mem_allSources
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw source ∈
      slabFineFusionWitnesses
        (globalInwardMateAnchorSlabData K) source.physical := by
  exact globalInwardMateSourceProductionRawAt_mem
    K source.physical hK
      (cubeInwardMatePhysicalBoundedOfMem
        K source.physical source.physicalSource.2)
      (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode source)
      (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode_mem_allSources
        source hsource)

/-- Every successful source endpoint is a literal production BF4 expanded
atom. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom_mem_allSources
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalCubeInwardMateCertifiedTargetFullSources K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom source ∈
      slabExpandedFineSources (globalInwardMateAnchorSlabData K) := by
  have hphysical : source.physical ∈
      (globalInwardMateAnchorSlabData K).physicalLabellings := by
    simpa [globalInwardMateAnchorSlabData,
      SlabPhysicalData.physicalLabellings, SlabPhysicalData.faceEdges,
      SlabPhysicalData.extent, centralExtent] using source.physicalSource.2
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom
    slabExpandedFineSources
  apply List.mem_flatMap.mpr
  refine ⟨source.physical, hphysical, ?_⟩
  unfold slabExpandedFineSourceBlock
  apply List.mem_map.mpr
  exact ⟨GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw source,
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw_mem_allSources
      source hsource,
    rfl⟩

/-! ## 2. Every successful target compiles into the same carrier -/

private theorem presentedAuxiliary_mem_own_target
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
      source linked).auxiliary ∈
      orderedSlabLinkFusionWitnesses K
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
        (cubeInwardMateCompleteSourceFaceOrder linked) := by
  rw [← GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_order
    source linked]
  exact (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
    source linked).auxiliary_mem

/-- Every successful target residual code, not merely a representative code,
occurs in the exact production target-code carrier. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetResidualCode_mem_allSources
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateTargetRepresentativeResidualCode source ∈
      cubeInwardMateFixedOrderTargetResidualCodes K
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source) := by
  let auxiliaryChoice := fun
      linked : {link // link ∈ boundaryCompleteSlabLinks 1} =>
    finiteEdgeLabellingWord
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds 1 linked.1).length)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        source linked).auxiliary
  have hchoice : ∀ linked,
      auxiliaryChoice linked ∈
        cubeInwardMateFixedOrderTargetAuxiliaryCodeRow
          K (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
            linked := by
    intro linked
    have hauxiliary := presentedAuxiliary_mem_own_target source linked
    unfold cubeInwardMateFixedOrderTargetAuxiliaryCodeRow
    apply List.mem_map.mpr
    let witness : CubeInwardMateFixedOrderTargetWitness
        K (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
          linked :=
      ⟨(GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
          source linked).auxiliary,
        hauxiliary⟩
    exact ⟨witness,
      List.mem_attach
        (orderedSlabLinkFusionWitnesses K
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
          (cubeInwardMateCompleteSourceFaceOrder linked)) witness,
      rfl⟩
  have hauxiliaryWords :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented source) ∈
        cubeInwardMateFixedOrderTargetAuxiliaryCodeAssignments
          K (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source) := by
    unfold cubeInwardMateFixedOrderTargetAuxiliaryCodeAssignments
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
    exact finiteRowAssignments_choice_mem
      (cubeInwardMateFixedOrderTargetAuxiliaryCodeRow
        K (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source))
      (boundaryCompleteSlabLinks 1).attach auxiliaryChoice hchoice
  unfold globalInwardMateTargetRepresentativeResidualCode
    cubeInwardMateFixedOrderTargetResidualCodes
  apply List.mem_map.mpr
  exact ⟨presentedSlabFusionWitnessAssignmentAuxiliaryWords
      (boundaryCompleteSlabLinks 1)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented source),
    hauxiliaryWords, rfl⟩

/-- The production target assignment of every successful source is an
accepted member of its literal production fiber. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw_mem_allSources
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw source ∈
      slabFineFusionWitnesses
        (globalInwardMateAnchorSlabData K)
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source) := by
  apply globalInwardMateProductionRawAt_mem
    K (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_bounded source)
  exact GlobalCubeInwardMateCertifiedTargetFullSource.targetResidualCode_mem_allSources
    source

/-- Every successful target endpoint is a literal member of the same
production BF4 expanded carrier. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom_mem_allSources
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom source ∈
      slabExpandedFineSources (globalInwardMateAnchorSlabData K) := by
  have hphysical :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source ∈
      (globalInwardMateAnchorSlabData K).physicalLabellings := by
    simpa [globalInwardMateAnchorSlabData,
      SlabPhysicalData.physicalLabellings, SlabPhysicalData.faceEdges,
      SlabPhysicalData.extent, centralExtent] using
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_mem source)
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom
    slabExpandedFineSources
  apply List.mem_flatMap.mpr
  refine ⟨GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source,
    hphysical, ?_⟩
  unfold slabExpandedFineSourceBlock
  apply List.mem_map.mpr
  exact ⟨GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw source,
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw_mem_allSources
      source,
    rfl⟩

/-! ## 3. The all-success source marginal is collision-free -/

/-- Equality of source production atoms recovers arbitrary successful global
sources, without representative selection. -/
theorem globalInwardMateAllSourceProductionAtom_injective
    {K : Nat} {hK : 1 ≤ K}
    (left : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hleft : left ∈ globalCubeInwardMateCertifiedTargetFullSources K hK)
    (right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hright : right ∈ globalCubeInwardMateCertifiedTargetFullSources K hK)
    (heq :
      GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom left =
        GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom right) :
    left = right := by
  cases left with
  | mk leftPhysicalSource leftEntry =>
      cases right with
      | mk rightPhysicalSource rightEntry =>
          let left : GlobalCubeInwardMateCertifiedTargetFullSource K hK :=
            { physicalSource := leftPhysicalSource
              entry := leftEntry }
          let right : GlobalCubeInwardMateCertifiedTargetFullSource K hK :=
            { physicalSource := rightPhysicalSource
              entry := rightEntry }
          change left = right
          change left ∈ globalCubeInwardMateCertifiedTargetFullSources K hK at hleft
          change right ∈ globalCubeInwardMateCertifiedTargetFullSources K hK at hright
          change
            GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom
                left =
              GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom
                right at heq
          have hphysical : left.physical = right.physical := by
            have hprojection := congrArg Prod.fst heq
            simpa only [
              GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom]
              using hprojection
          have hraw :
              GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw
                  left =
                GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw
                  right := by
            have hprojection := congrArg Prod.snd heq
            simpa only [
              GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom]
              using hprojection
          have hphysicalSource :
              leftPhysicalSource = rightPhysicalSource :=
            Subtype.ext hphysical
          cases hphysicalSource
          have hcode := globalInwardMateSourceProductionRawAt_injective
            K left.physical hK
              (cubeInwardMatePhysicalBoundedOfMem
                K left.physical left.physicalSource.2)
              (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode_mem_allSources
                left hleft)
              (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode_mem_allSources
                right hright)
              hraw
          have houtcome :=
            cubeInwardMateCertifiedOutcomeFullSourceCode_injective
              K left.physical hK
                (cubeInwardMatePhysicalBoundedOfMem
                  K left.physical left.physicalSource.2)
                (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome left)
                (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome_mem_allSources
                  left hleft)
                (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome right)
                (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome_mem_allSources
                  right hright)
                hcode
          have htarget : left.entry.1 = right.entry.1 := by
            change (Sum.inl left.entry.1, left.entry.2) =
              (Sum.inl right.entry.1, right.entry.2) at houtcome
            exact Sum.inl.inj (congrArg Prod.fst houtcome)
          have hoff : left.entry.2 = right.entry.2 := by
            change (Sum.inl left.entry.1, left.entry.2) =
              (Sum.inl right.entry.1, right.entry.2) at houtcome
            exact congrArg
              (fun outcome : CubeInwardMateCertifiedOutcomeFullSource
                  K left.physical hK
                    (cubeInwardMatePhysicalBoundedOfMem
                      K left.physical left.physicalSource.2) => outcome.2)
              houtcome
          have hentry : left.entry = right.entry := Prod.ext htarget hoff
          unfold left right
          cases hentry
          rfl

/-- The production source marginal retaining every successful source. -/
def globalInwardMateAllSourceProductionSourceAtoms
    (K : Nat) (hK : 1 ≤ K) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (globalCubeInwardMateCertifiedTargetFullSources K hK).map
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom

/-- The full successful production source marginal has no collisions. -/
theorem globalInwardMateAllSourceProductionSourceAtoms_nodup
    (K : Nat) (hK : 1 ≤ K) :
    (globalInwardMateAllSourceProductionSourceAtoms K hK).Nodup := by
  unfold globalInwardMateAllSourceProductionSourceAtoms
  apply nodup_map_of_injOn
  · exact globalCubeInwardMateCertifiedTargetFullSources_nodup K hK
  · intro left hleft right hright heq
    exact globalInwardMateAllSourceProductionAtom_injective
      left hleft right hright heq

/-- Every atom of the full source marginal belongs to the literal production
BF4 expanded carrier. -/
theorem globalInwardMateAllSourceProductionSourceAtoms_mem_expanded
    (K : Nat) (hK : 1 ≤ K)
    (atom : SlabLabelling × SlabFusionWitnessAssignment)
    (hatom : atom ∈ globalInwardMateAllSourceProductionSourceAtoms K hK) :
    atom ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K) := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hatom
  exact
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom_mem_allSources
      source hsource

/-! ## 4. Exact full source mass and the many-to-one pair transport -/

/-- The all-source production marginal preserves the complete successful
source weight term by term. -/
theorem globalInwardMateAllSourceProductionSourceAtoms_weight_eqv
    (K : Nat) (hK : 1 ≤ K) :
    listQSum
        (slabExpandedFineSourceWeight (globalInwardMateAnchorSlabData K))
        (globalInwardMateAllSourceProductionSourceAtoms K hK) ≈
      listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalCubeInwardMateCertifiedTargetFullSources K hK) := by
  unfold globalInwardMateAllSourceProductionSourceAtoms
  rw [listQSum_map]
  apply listQSum_congr
  intro source
  exact
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight_eqv_weight
      source

/-- **Full successful mass survives literal production recoding.**  At every
cutoff `K >= 1`, the duplicate-free production source marginal carries at
least `41/425` of the physical partition mass. -/
theorem globalInwardMateAllSourceFraction_partition_le_productionSources
    (K : Nat) (hK : 1 ≤ K) :
    Q'.mkPos 41 425 (by decide) *
        slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      listQSum
        (slabExpandedFineSourceWeight (globalInwardMateAnchorSlabData K))
        (globalInwardMateAllSourceProductionSourceAtoms K hK) := by
  exact Q'.le_trans' _ _ _
    (globalCubeInwardMateCertifiedTargetFullSources_weight_ge_partition K hK)
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (globalInwardMateAllSourceProductionSourceAtoms_weight_eqv K hK)))

/-- The full finite many-to-one production transport, one pair for every
successful source. -/
def globalInwardMateAllSourceProductionPairs
    (K : Nat) (hK : 1 ≤ K) :
    List ((SlabLabelling × SlabFusionWitnessAssignment) ×
      (SlabLabelling × SlabFusionWitnessAssignment)) :=
  (globalCubeInwardMateCertifiedTargetFullSources K hK).map
    GlobalCubeInwardMateCertifiedTargetFullSource.productionPair

/-- The exact source marginal of the full transport. -/
theorem globalInwardMateAllSourceProductionPairs_sourceMarginal
    (K : Nat) (hK : 1 ≤ K) :
    (globalInwardMateAllSourceProductionPairs K hK).map Prod.fst =
      globalInwardMateAllSourceProductionSourceAtoms K hK := by
  unfold globalInwardMateAllSourceProductionPairs
    globalInwardMateAllSourceProductionSourceAtoms
    GlobalCubeInwardMateCertifiedTargetFullSource.productionPair
  rw [List.map_map]
  apply List.map_congr_left
  intro source _hsource
  rfl

/-- Every full-transport pair has both endpoints in one literal production
carrier and is off diagonal. -/
theorem globalInwardMateAllSourceProductionPairs_spec
    (K : Nat) (hK : 1 ≤ K)
    (pair : (SlabLabelling × SlabFusionWitnessAssignment) ×
      (SlabLabelling × SlabFusionWitnessAssignment))
    (hpair : pair ∈ globalInwardMateAllSourceProductionPairs K hK) :
    pair.1 ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K) ∧
      pair.2 ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K) ∧
      pair.1 ≠ pair.2 := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hpair
  exact ⟨
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom_mem_allSources
      source hsource,
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom_mem_allSources
      source,
    GlobalCubeInwardMateCertifiedTargetFullSource.productionPair_ne source⟩

/-- The full pair carrier itself is duplicate-free because its source
projection is injective. -/
theorem globalInwardMateAllSourceProductionPairs_nodup
    (K : Nat) (hK : 1 ≤ K) :
    (globalInwardMateAllSourceProductionPairs K hK).Nodup := by
  unfold globalInwardMateAllSourceProductionPairs
  apply nodup_map_of_injOn
  · exact globalCubeInwardMateCertifiedTargetFullSources_nodup K hK
  · intro left hleft right hright heq
    apply globalInwardMateAllSourceProductionAtom_injective
      left hleft right hright
    exact congrArg Prod.fst heq

/-- Type-level certificate for the multiplicity-faithful successful-source
transport.  Target uniqueness is intentionally absent: bounded target
congestion is the next certificate. -/
structure GlobalInwardMateAllSourceProductionTransportCertificate
    (K : Nat) (hK : 1 ≤ K) : Type where
  pairs : List ((SlabLabelling × SlabFusionWitnessAssignment) ×
    (SlabLabelling × SlabFusionWitnessAssignment))
  sources : List (SlabLabelling × SlabFusionWitnessAssignment)
  sourceMarginal : pairs.map Prod.fst = sources
  pairs_nodup : pairs.Nodup
  sources_nodup : sources.Nodup
  endpoints_mem : ∀ pair, pair ∈ pairs →
    pair.1 ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K) ∧
      pair.2 ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K)
  pairs_offDiagonal : ∀ pair, pair ∈ pairs → pair.1 ≠ pair.2
  rate : Q'
  rate_positive : (0 : Q') < rate
  sourceWeight_ge :
    rate * slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      listQSum
        (slabExpandedFineSourceWeight (globalInwardMateAnchorSlabData K))
        sources

/-- Construct the all-success production transport certificate with exact
success rate `41/425`. -/
def globalInwardMateAllSourceProductionTransportCertificate
    (K : Nat) (hK : 1 ≤ K) :
    GlobalInwardMateAllSourceProductionTransportCertificate K hK where
  pairs := globalInwardMateAllSourceProductionPairs K hK
  sources := globalInwardMateAllSourceProductionSourceAtoms K hK
  sourceMarginal :=
    globalInwardMateAllSourceProductionPairs_sourceMarginal K hK
  pairs_nodup := globalInwardMateAllSourceProductionPairs_nodup K hK
  sources_nodup :=
    globalInwardMateAllSourceProductionSourceAtoms_nodup K hK
  endpoints_mem := fun pair hpair =>
    ⟨(globalInwardMateAllSourceProductionPairs_spec K hK pair hpair).1,
      (globalInwardMateAllSourceProductionPairs_spec K hK pair hpair).2.1⟩
  pairs_offDiagonal := fun pair hpair =>
    (globalInwardMateAllSourceProductionPairs_spec K hK pair hpair).2.2
  rate := Q'.mkPos 41 425 (by decide)
  rate_positive := by decide
  sourceWeight_ge :=
    globalInwardMateAllSourceFraction_partition_le_productionSources K hK

#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome_mem_allSources
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode_mem_allSources
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom_mem_allSources
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetResidualCode_mem_allSources
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom_mem_allSources
#print axioms globalInwardMateAllSourceProductionAtom_injective
#print axioms globalInwardMateAllSourceProductionSourceAtoms_nodup
#print axioms globalInwardMateAllSourceProductionSourceAtoms_weight_eqv
#print axioms globalInwardMateAllSourceFraction_partition_le_productionSources
#print axioms globalInwardMateAllSourceProductionPairs_nodup
#print axioms GlobalInwardMateAllSourceProductionTransportCertificate
#print axioms globalInwardMateAllSourceProductionTransportCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport
