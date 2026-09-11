/-
# Exact global production source marginal of the inward-mate pair carrier

The fixed-physical source compiler is injective.  Adding the physical field
as the first coordinate therefore separates every remaining global block.
This module proves that the source endpoints of the retained production-pair
carrier form a duplicate-free literal BF4 subcarrier and preserve the exact
source weight term by term.

Together with the existing target-marginal theorem, the pair carrier now has
two explicit same-object production marginals.  It is still a constructed
transport relation, not the actual BF4 conditional/OS joint.  No posterior
variance, OS form bound, spectral gap, beta/lattice-spacing uniformity, or
continuum theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceInjection

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Global injectivity of the production source atom -/

/-- Equality of source production atoms recovers the retained global
representative. -/
theorem globalInwardMateSourceProductionAtom_injective
    {K : Nat} {hK : 1 ≤ K}
    (left : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hleft : left ∈ globalInwardMateTargetRepresentatives K hK)
    (right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hright : right ∈ globalInwardMateTargetRepresentatives K hK)
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
          change left ∈ globalInwardMateTargetRepresentatives K hK at hleft
          change right ∈ globalInwardMateTargetRepresentatives K hK at hright
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
              (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode_mem
                left hleft)
              (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcomeCode_mem
                right hright)
              hraw
          have houtcome :=
            cubeInwardMateCertifiedOutcomeFullSourceCode_injective
              K left.physical hK
                (cubeInwardMatePhysicalBoundedOfMem
                  K left.physical left.physicalSource.2)
                (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome left)
                (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome_mem
                  left hleft)
                (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome right)
                (GlobalCubeInwardMateCertifiedTargetFullSource.sourceOutcome_mem
                  right hright)
                hcode
          have htarget : left.entry.1 = right.entry.1 := by
            change
              (Sum.inl left.entry.1, left.entry.2) =
                (Sum.inl right.entry.1, right.entry.2) at houtcome
            have hbranch := congrArg Prod.fst houtcome
            exact Sum.inl.inj hbranch
          have hoff : left.entry.2 = right.entry.2 := by
            change
              (Sum.inl left.entry.1, left.entry.2) =
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

/-! ## 2. The duplicate-free literal source marginal -/

/-- The list of production source endpoints selected by all distinct retained
targets. -/
def globalInwardMateProductionSourceAtoms
    (K : Nat) (hK : 1 ≤ K) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (globalInwardMateTargetRepresentatives K hK).map
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom

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

/-- The source marginal has no collisions. -/
theorem globalInwardMateProductionSourceAtoms_nodup
    (K : Nat) (hK : 1 ≤ K) :
    (globalInwardMateProductionSourceAtoms K hK).Nodup := by
  unfold globalInwardMateProductionSourceAtoms
  apply nodup_map_of_injOn
  · apply nodup_of_map_nodup_local
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom
    exact globalInwardMateProductionTargetAtoms_nodup K hK
  · intro left hleft right hright heq
    exact globalInwardMateSourceProductionAtom_injective
      left hleft right hright heq

/-- Every source-marginal atom is a literal member of the production BF4
expanded carrier. -/
theorem globalInwardMateProductionSourceAtoms_mem_expanded
    (K : Nat) (hK : 1 ≤ K)
    (atom : SlabLabelling × SlabFusionWitnessAssignment)
    (hatom : atom ∈ globalInwardMateProductionSourceAtoms K hK) :
    atom ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K) := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hatom
  exact GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom_mem
    source hsource

/-! ## 3. Exact source weights and pair marginal -/

/-- Production BF4 weight of the recoded source endpoint. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  slabExpandedFineSourceWeight (globalInwardMateAnchorSlabData K)
    (GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom source)

/-- The source recoding preserves the original all-target source weight
exactly. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight_eqv_weight
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
        source ≈
      GlobalCubeInwardMateCertifiedTargetFullSource.weight source := by
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor
      anchorCoupling K 1 source.physical) _ ?_ ?_
  · unfold GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
      slabExpandedFineSourceWeight
      GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom
    simpa [globalInwardMateAnchorSlabData,
      SlabPhysicalData.extent, centralExtent] using
      (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
        (globalInwardMateAnchorSlabData K) source.physical
        (GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw
          source))
  · unfold GlobalCubeInwardMateCertifiedTargetFullSource.weight
      cubeInwardMateCertifiedTargetFullSourceWeight
      GlobalCubeInwardMateCertifiedTargetFullSource.physical
    exact Q'.eqv_refl _

/-- Total production source-marginal weight is exactly the selected original
all-target source weight. -/
theorem globalInwardMateProductionSourceAtoms_weight_eqv
    (K : Nat) (hK : 1 ≤ K) :
    listQSum
        (slabExpandedFineSourceWeight (globalInwardMateAnchorSlabData K))
        (globalInwardMateProductionSourceAtoms K hK) ≈
      listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalInwardMateTargetRepresentatives K hK) := by
  unfold globalInwardMateProductionSourceAtoms
  rw [listQSum_map]
  apply listQSum_congr
  intro source
  exact
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight_eqv_weight
      source

/-- The source marginal of the production-pair carrier is exactly the
duplicate-free production source-atom list. -/
theorem globalInwardMateProductionPairs_sourceMarginal
    (K : Nat) (hK : 1 ≤ K) :
    (globalInwardMateProductionPairs K hK).map Prod.fst =
      globalInwardMateProductionSourceAtoms K hK := by
  unfold globalInwardMateProductionPairs
    globalInwardMateProductionSourceAtoms
    GlobalCubeInwardMateCertifiedTargetFullSource.productionPair
  rw [List.map_map]
  apply List.map_congr_left
  intro source _hsource
  rfl

/-- Both marginals of the constructed pair carrier are duplicate-free literal
production BF4 subcarriers. -/
structure GlobalInwardMateProductionPairMarginalCertificate
    (K : Nat) (hK : 1 ≤ K) : Type where
  pairs : List
    ((SlabLabelling × SlabFusionWitnessAssignment) ×
      (SlabLabelling × SlabFusionWitnessAssignment))
  sources : List (SlabLabelling × SlabFusionWitnessAssignment)
  targets : List (SlabLabelling × SlabFusionWitnessAssignment)
  sourceMarginal : pairs.map Prod.fst = sources
  targetMarginal : pairs.map Prod.snd = targets
  sources_nodup : sources.Nodup
  targets_nodup : targets.Nodup
  sources_mem : ∀ atom, atom ∈ sources →
    atom ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K)
  targets_mem : ∀ atom, atom ∈ targets →
    atom ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K)
  pairs_offDiagonal : ∀ pair, pair ∈ pairs → pair.1 ≠ pair.2

/-- Package the two exact same-carrier marginals without asserting an actual
conditional probability law. -/
def globalInwardMateProductionPairMarginalCertificate
    (K : Nat) (hK : 1 ≤ K) :
    GlobalInwardMateProductionPairMarginalCertificate K hK where
  pairs := globalInwardMateProductionPairs K hK
  sources := globalInwardMateProductionSourceAtoms K hK
  targets := globalInwardMateProductionTargetAtoms K hK
  sourceMarginal := globalInwardMateProductionPairs_sourceMarginal K hK
  targetMarginal := globalInwardMateProductionPairs_targetMarginal K hK
  sources_nodup := globalInwardMateProductionSourceAtoms_nodup K hK
  targets_nodup := globalInwardMateProductionTargetAtoms_nodup K hK
  sources_mem := globalInwardMateProductionSourceAtoms_mem_expanded K hK
  targets_mem := globalInwardMateProductionTargetAtoms_mem_expanded K hK
  pairs_offDiagonal := fun pair hpair =>
    (globalInwardMateProductionPairs_spec K hK pair hpair).2.2

#print axioms globalInwardMateSourceProductionAtom_injective
#print axioms globalInwardMateProductionSourceAtoms
#print axioms globalInwardMateProductionSourceAtoms_nodup
#print axioms globalInwardMateProductionSourceAtoms_mem_expanded
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight_eqv_weight
#print axioms globalInwardMateProductionSourceAtoms_weight_eqv
#print axioms globalInwardMateProductionPairs_sourceMarginal
#print axioms GlobalInwardMateProductionPairMarginalCertificate
#print axioms globalInwardMateProductionPairMarginalCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal
