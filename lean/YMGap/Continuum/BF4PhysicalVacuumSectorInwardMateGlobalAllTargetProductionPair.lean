/-
# Literal production source-target pairs for the global all-target event

The retained inward-mate target atoms already live in the production BF4
expanded carrier.  This module places their source endpoints in that same
carrier without identifying root-first and production-order auxiliary words.

The source compiler first restores the complete classified outcome family:
every target-or-first-stretched cube outcome, crossed with every off-cube
production assignment.  This family has exactly the full production-fiber
cardinality.  A finite natural-word serialization preserves that enumeration
length, so equal written rank constructively selects a literal production
source for every listed successful outcome.  Collision-freeness of the
source-code list remains a separate obligation.

The resulting finite pair carrier is pointwise off diagonal: on each of the
six central cube faces, source and target physical labels have opposite
parity.  It is a constructed transport relation, not yet the actual BF4
conditional two-copy law.  No minorization, posterior variance, OS form
bound, spectral gap, beta/lattice-spacing uniformity, or continuum theorem
is asserted.  In particular, no source marginal identity is claimed.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionInjection

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceMultiplicitySplit
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchCardinality
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchWeight
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Restore the complete classified source carrier -/

/-- One classified cube outcome, from either branch, paired with one accepted
production assignment on every off-cube link. -/
abbrev CubeInwardMateCertifiedOutcomeFullSource
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :=
  Sum
      (CubeInwardMateOrderedTargetWitnessAssignment K physical)
      (CubeInwardMateCertifiedFirstStretchedSource
        K physical hK hbounded) ×
    { assignment : SlabFusionWitnessAssignment //
      assignment ∈
        cubeInwardMateOffCubeFusionWitnessAssignments K physical }

/-- The complete classified outcome carrier after restoring all off-cube
production coordinates. -/
def cubeInwardMateCertifiedOutcomeFullSources
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List (CubeInwardMateCertifiedOutcomeFullSource
      K physical hK hbounded) :=
  cartesian
    (cubeInwardMateCertifiedSourceOutcomes K physical hK hbounded)
    (cubeInwardMateOffCubeFusionWitnessAssignments K physical).attach

private theorem cartesian_length_local {A B : Type}
    (left : List A) (right : List B) :
    (cartesian left right).length = left.length * right.length := by
  induction left with
  | nil =>
      unfold cartesian
      simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head tail ih =>
      rw [cartesian]
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      change right.length + (cartesian tail right).length =
        (tail.length + 1) * right.length
      rw [ih, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

/-- The complete classified outcome carrier has exactly the production
intertwiner-fiber cardinality. -/
theorem cubeInwardMateCertifiedOutcomeFullSources_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedOutcomeFullSources
      K physical hK hbounded).length =
      slabExplicitLinkMultiplicityProduct K 1 physical := by
  unfold cubeInwardMateCertifiedOutcomeFullSources
  rw [cartesian_length_local,
    cubeInwardMateCertifiedSourceOutcomes_length,
    List.length_attach,
    cubeInwardMateOffCubeFusionWitnessAssignments_length]
  exact cubeInwardMateSourceBoundary_mul_offCube_eq_slabMultiplicity
    K physical

/-- Exact source classification and off-cube completion introduce no
duplicate full outcomes. -/
theorem cubeInwardMateCertifiedOutcomeFullSources_nodup
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedOutcomeFullSources
      K physical hK hbounded).Nodup := by
  unfold cubeInwardMateCertifiedOutcomeFullSources
  exact cartesian_nodup _ _
    (cubeInwardMateCertifiedSourceOutcomes_nodup
      K physical hK hbounded)
    (attach_nodup_of_nodup _
      (cubeInwardMateOffCubeFusionWitnessAssignments_nodup
        K physical))

/-! ## 2. Serialize and compile complete source outcomes -/

/-- A decidable finite word for one complete classified source outcome. -/
def cubeInwardMateCertifiedOutcomeFullSourceCode
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (source : CubeInwardMateCertifiedOutcomeFullSource
      K physical hK hbounded) : List (List Nat) :=
  (List.map (fun linked =>
      finiteEdgeLabellingWord
        (canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds 1 linked.1.link).length)
        (recoverCubeInwardMateSourceWitnessPartitionAt
          K physical hK hbounded linked
          (unsplitCubeInwardMateCertifiedSource
            K physical hK hbounded source.1 linked)))
      cubeProductionIncidences.attach) ++
    slabFusionWitnessAssignmentWords 1 source.2.1

/-- The complete written source-code family, preserving the exact enumeration
length while avoiding equality on function-valued proof packages. -/
def cubeInwardMateCertifiedOutcomeFullSourceCodes
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List (List (List Nat)) :=
  (cubeInwardMateCertifiedOutcomeFullSources
    K physical hK hbounded).map
      (cubeInwardMateCertifiedOutcomeFullSourceCode
        K physical hK hbounded)

/-- The literal production fiber and complete classified source carrier have
the same length. -/
theorem globalInwardMateProductionFiber_length_eq_sourceOutcomes
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (slabFineFusionWitnesses
        (globalInwardMateAnchorSlabData K) physical).length =
      (cubeInwardMateCertifiedOutcomeFullSourceCodes
        K physical hK hbounded).length := by
  calc
    (slabFineFusionWitnesses
        (globalInwardMateAnchorSlabData K) physical).length =
        slabExplicitLinkMultiplicityProduct K 1 physical := by
      simpa [globalInwardMateAnchorSlabData,
        SlabPhysicalData.extent, centralExtent] using
        (slabFineFusionWitnesses_length
          (globalInwardMateAnchorSlabData K) physical)
    _ = (cubeInwardMateCertifiedOutcomeFullSourceCodes
        K physical hK hbounded).length := by
      unfold cubeInwardMateCertifiedOutcomeFullSourceCodes
      rw [List.length_map,
        cubeInwardMateCertifiedOutcomeFullSources_length]

/-- Recode one complete classified source outcome to the production-order
assignment at the same written rank. -/
def globalInwardMateSourceProductionRawAt
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (sourceCode : List (List Nat)) : SlabFusionWitnessAssignment :=
  equalRankReindex []
    (slabFineFusionWitnesses (globalInwardMateAnchorSlabData K) physical)
    (cubeInwardMateCertifiedOutcomeFullSourceCodes
      K physical hK hbounded) sourceCode

/-- Equal-rank source compilation lands in the literal production fiber. -/
theorem globalInwardMateSourceProductionRawAt_mem
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (sourceCode : List (List Nat))
    (hsource : sourceCode ∈ cubeInwardMateCertifiedOutcomeFullSourceCodes
      K physical hK hbounded) :
    globalInwardMateSourceProductionRawAt
        K physical hK hbounded sourceCode ∈
      slabFineFusionWitnesses
        (globalInwardMateAnchorSlabData K) physical := by
  exact equalRankReindex_mem []
    (slabFineFusionWitnesses (globalInwardMateAnchorSlabData K) physical)
    (cubeInwardMateCertifiedOutcomeFullSourceCodes
      K physical hK hbounded)
    (globalInwardMateProductionFiber_length_eq_sourceOutcomes
      K physical hK hbounded)
    sourceCode hsource

/-! ## 3. Restrict the complete compiler to retained all-target sources -/

private theorem globalTargetFullSource_mem_own_block
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

/-- View an all-target source as the left branch of the complete classified
source carrier, retaining its off-cube production coordinates. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    CubeInwardMateCertifiedOutcomeFullSource
      K source.physical hK
        (cubeInwardMatePhysicalBoundedOfMem
          K source.physical source.physicalSource.2) :=
  (Sum.inl source.entry.1, source.entry.2)

/-- Every retained representative is genuinely a member of the complete
classified source carrier at its own physical field. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateTargetRepresentatives K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome source ∈
      cubeInwardMateCertifiedOutcomeFullSources
        K source.physical hK
          (cubeInwardMatePhysicalBoundedOfMem
            K source.physical source.physicalSource.2) := by
  have hglobal := globalInwardMateTargetRepresentatives_mem_source
    source hsource
  have hentry := globalTargetFullSource_mem_own_block source hglobal
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

/-- The finite decidable source word attached to one all-target entry. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List (List Nat) :=
  cubeInwardMateCertifiedOutcomeFullSourceCode
    K source.physical hK
      (cubeInwardMatePhysicalBoundedOfMem
        K source.physical source.physicalSource.2)
      (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome source)

/-- The source word of every retained representative occurs in the complete
written source-code family. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateTargetRepresentatives K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode source ∈
      cubeInwardMateCertifiedOutcomeFullSourceCodes
        K source.physical hK
          (cubeInwardMatePhysicalBoundedOfMem
            K source.physical source.physicalSource.2) := by
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode
    cubeInwardMateCertifiedOutcomeFullSourceCodes
  exact List.mem_map.mpr
    ⟨GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome source,
      GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome_mem
        source hsource,
      rfl⟩

/-- The production-order source assignment attached to one retained
all-target representative. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    SlabFusionWitnessAssignment :=
  globalInwardMateSourceProductionRawAt
    K source.physical hK
      (cubeInwardMatePhysicalBoundedOfMem
        K source.physical source.physicalSource.2)
      (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode source)

/-- The recoded source assignment is a literal production fiber member. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateTargetRepresentatives K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw source ∈
      slabFineFusionWitnesses
        (globalInwardMateAnchorSlabData K) source.physical := by
  exact globalInwardMateSourceProductionRawAt_mem
    K source.physical hK
      (cubeInwardMatePhysicalBoundedOfMem
        K source.physical source.physicalSource.2)
      (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode source)
      (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode_mem
        source hsource)

/-- The source endpoint as an atom of the same production BF4 expanded
carrier as the retained target. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    SlabLabelling × SlabFusionWitnessAssignment :=
  (source.physical,
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw source)

/-- Every recoded source endpoint is a literal production BF4 expanded
atom. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateTargetRepresentatives K hK) :
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
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw_mem
      source hsource,
    rfl⟩

/-! ## 4. A literal off-diagonal same-carrier pair relation -/

/-- The recoded production source and target endpoints carried by one
retained representative. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.productionPair
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (SlabLabelling × SlabFusionWitnessAssignment) ×
      (SlabLabelling × SlabFusionWitnessAssignment) :=
  (GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom source,
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom source)

/-- Both endpoints of every retained pair lie in the same literal production
BF4 expanded carrier. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.productionPair_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateTargetRepresentatives K hK) :
    (GlobalCubeInwardMateCertifiedTargetFullSource.productionPair source).1 ∈
        slabExpandedFineSources (globalInwardMateAnchorSlabData K) ∧
      (GlobalCubeInwardMateCertifiedTargetFullSource.productionPair source).2 ∈
        slabExpandedFineSources (globalInwardMateAnchorSlabData K) := by
  exact ⟨GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom_mem
      source hsource,
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom_mem
      source hsource⟩

/-- On every central cube face, the pair endpoints have opposite physical
parity. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.productionPair_parity_ne
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    {faceId : Nat} (hface : faceId ∈ centralLowerCubeFaceIds) :
    (GlobalCubeInwardMateCertifiedTargetFullSource.productionPair source).2.1
        faceId % 2 ≠
      (GlobalCubeInwardMateCertifiedTargetFullSource.productionPair source).1.1
        faceId % 2 := by
  exact GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_parity_ne
    source hface

/-- In particular, every constructed production pair is off diagonal. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.productionPair_ne
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (GlobalCubeInwardMateCertifiedTargetFullSource.productionPair source).1 ≠
      (GlobalCubeInwardMateCertifiedTargetFullSource.productionPair source).2 := by
  intro heq
  have hphysical := congrArg (fun atom => atom.1 0 % 2) heq
  exact
    (GlobalCubeInwardMateCertifiedTargetFullSource.productionPair_parity_ne
      source (by decide : 0 ∈ centralLowerCubeFaceIds)) hphysical.symm

/-- The finite production pair carrier selected by the distinct retained
target representatives. -/
def globalInwardMateProductionPairs
    (K : Nat) (hK : 1 ≤ K) :
    List
      ((SlabLabelling × SlabFusionWitnessAssignment) ×
        (SlabLabelling × SlabFusionWitnessAssignment)) :=
  (globalInwardMateTargetRepresentatives K hK).map
    GlobalCubeInwardMateCertifiedTargetFullSource.productionPair

/-- The target marginal of the pair carrier is exactly the previously proved
collision-free retained production subcarrier. -/
theorem globalInwardMateProductionPairs_targetMarginal
    (K : Nat) (hK : 1 ≤ K) :
    (globalInwardMateProductionPairs K hK).map Prod.snd =
      globalInwardMateProductionTargetAtoms K hK := by
  unfold globalInwardMateProductionPairs
    globalInwardMateProductionTargetAtoms
    GlobalCubeInwardMateCertifiedTargetFullSource.productionPair
  rw [List.map_map]
  apply List.map_congr_left
  intro source _hsource
  rfl

private theorem nodup_of_map_nodup_local
    {A B : Type} (map : A → B) : ∀ {items : List A},
    (items.map map).Nodup → items.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_of_map_nodup_local map hparts.2⟩
      intro hmem
      exact hparts.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩)

/-- The pair carrier has no duplicate edges because its target marginal is
already collision-free. -/
theorem globalInwardMateProductionPairs_nodup
    (K : Nat) (hK : 1 ≤ K) :
    (globalInwardMateProductionPairs K hK).Nodup := by
  apply nodup_of_map_nodup_local Prod.snd
  rw [globalInwardMateProductionPairs_targetMarginal]
  exact globalInwardMateProductionTargetAtoms_nodup K hK

/-- Every listed edge has both endpoints in the production carrier and is
strictly off diagonal. -/
theorem globalInwardMateProductionPairs_spec
    (K : Nat) (hK : 1 ≤ K)
    (pair :
      (SlabLabelling × SlabFusionWitnessAssignment) ×
        (SlabLabelling × SlabFusionWitnessAssignment))
    (hpair : pair ∈ globalInwardMateProductionPairs K hK) :
    pair.1 ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K) ∧
      pair.2 ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K) ∧
      pair.1 ≠ pair.2 := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hpair
  exact
    ⟨GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom_mem
        source hsource,
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom_mem
        source hsource,
      GlobalCubeInwardMateCertifiedTargetFullSource.productionPair_ne source⟩

#print axioms cubeInwardMateCertifiedOutcomeFullSources_length
#print axioms cubeInwardMateCertifiedOutcomeFullSources_nodup
#print axioms cubeInwardMateCertifiedOutcomeFullSourceCode
#print axioms cubeInwardMateCertifiedOutcomeFullSourceCodes
#print axioms globalInwardMateProductionFiber_length_eq_sourceOutcomes
#print axioms globalInwardMateSourceProductionRawAt
#print axioms globalInwardMateSourceProductionRawAt_mem
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome_mem
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw_mem
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom_mem
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.productionPair
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.productionPair_mem
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.productionPair_parity_ne
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.productionPair_ne
#print axioms globalInwardMateProductionPairs
#print axioms globalInwardMateProductionPairs_targetMarginal
#print axioms globalInwardMateProductionPairs_nodup
#print axioms globalInwardMateProductionPairs_spec

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair
