/-
# Collision-free global all-target production subcarrier

The equal-rank compiler places every fixed-order all-target code in the
literal production BF4 fiber.  To use its total weight as a genuine
submeasure, distinct retained representatives must not collide after that
recoding.

The key observation is purely finite and constructive.  Positional lookup in
a duplicate-free list is injective below its length, even when the element
type itself has no decidable equality.  Hence equal production assignments
have equal written ranks.  Reading those ranks back in the residual-code list
recovers equal codes, and the existing SU(2) target-block code theorem
recovers the representative.  Distinct physical targets are already
separated by the physical coordinate of the expanded atom.

The result is a duplicate-free literal subcarrier of
`slabExpandedFineSources` with the previously proved positive cutoff-uniform
weight fraction at coupling `1/400`.  No conditional two-copy law, posterior
variance, OS form bound, spectral gap, beta/lattice-spacing uniformity, or
continuum theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionInjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Positional lookup is injective without element decidable equality -/

private theorem listAtRank_injective_local
    {A : Type} (fallback : A) :
    ∀ {items : List A}, items.Nodup →
      ∀ {left right : Nat},
        left < items.length → right < items.length →
        listAtRank fallback items left = listAtRank fallback items right →
        left = right
  | [], _, left, _, hleft, _, _ =>
      False.elim (Nat.not_lt_zero left hleft)
  | head :: tail, hnodup, left, right, hleft, hright, heq => by
      have hparts := List.nodup_cons.mp hnodup
      cases left with
      | zero =>
          cases right with
          | zero => rfl
          | succ rightTail =>
              have hrightTail : rightTail < tail.length :=
                Nat.lt_of_succ_lt_succ hright
              have hmem := listAtRank_mem_of_lt
                fallback tail rightTail hrightTail
              change head = listAtRank fallback tail rightTail at heq
              rw [← heq] at hmem
              exact False.elim (hparts.1 hmem)
      | succ leftTail =>
          cases right with
          | zero =>
              have hleftTail : leftTail < tail.length :=
                Nat.lt_of_succ_lt_succ hleft
              have hmem := listAtRank_mem_of_lt
                fallback tail leftTail hleftTail
              change listAtRank fallback tail leftTail = head at heq
              rw [heq] at hmem
              exact False.elim (hparts.1 hmem)
          | succ rightTail =>
              have hleftTail : leftTail < tail.length :=
                Nat.lt_of_succ_lt_succ hleft
              have hrightTail : rightTail < tail.length :=
                Nat.lt_of_succ_lt_succ hright
              change listAtRank fallback tail leftTail =
                listAtRank fallback tail rightTail at heq
              exact congrArg Nat.succ
                (listAtRank_injective_local fallback hparts.2
                  hleftTail hrightTail heq)

/-! ## 2. Equal-rank production recoding is collision-free -/

/-- Two listed target codes that compile to the same production assignment
were already the same code.  No decidable equality on function-valued
production assignments is required. -/
theorem globalInwardMateProductionRawAt_injective
    (K : Nat) (target : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded K 1 target)
    {left right : List (List Nat) × List (List Nat)}
    (hleft : left ∈ cubeInwardMateFixedOrderTargetResidualCodes K target)
    (hright : right ∈ cubeInwardMateFixedOrderTargetResidualCodes K target)
    (heq : globalInwardMateProductionRawAt K target left =
      globalInwardMateProductionRawAt K target right) :
    left = right := by
  have hlength :=
    globalInwardMateProductionFiber_length_eq_targetCodes K target hbounded
  have hleftRank :
      listRank left (cubeInwardMateFixedOrderTargetResidualCodes K target) <
        (slabFineFusionWitnesses
          (globalInwardMateAnchorSlabData K) target).length := by
    rw [hlength]
    exact listRank_lt_length_of_mem left hleft
  have hrightRank :
      listRank right (cubeInwardMateFixedOrderTargetResidualCodes K target) <
        (slabFineFusionWitnesses
          (globalInwardMateAnchorSlabData K) target).length := by
    rw [hlength]
    exact listRank_lt_length_of_mem right hright
  have hranks :
      listRank left (cubeInwardMateFixedOrderTargetResidualCodes K target) =
        listRank right
          (cubeInwardMateFixedOrderTargetResidualCodes K target) := by
    apply listAtRank_injective_local []
      (slabFineFusionWitnesses_nodup
        (globalInwardMateAnchorSlabData K) target)
      hleftRank hrightRank
    simpa only [globalInwardMateProductionRawAt, equalRankReindex] using heq
  calc
    left = listAtRank left
        (cubeInwardMateFixedOrderTargetResidualCodes K target)
        (listRank left
          (cubeInwardMateFixedOrderTargetResidualCodes K target)) :=
      (listAtRank_listRank_eq_of_mem left left hleft).symm
    _ = listAtRank left
        (cubeInwardMateFixedOrderTargetResidualCodes K target)
        (listRank right
          (cubeInwardMateFixedOrderTargetResidualCodes K target)) := by
      rw [hranks]
    _ = right := listAtRank_listRank_eq_of_mem left right hright

/-- Within one fixed physical target block, equality of the recoded
production assignments recovers the retained representative. -/
theorem globalInwardMateTargetPhysicalBlock_targetProductionRaw_injective
    {K : Nat} {hK : 1 ≤ K} {target : EdgeLabelling}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (left : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hleft : left ∈
      globalInwardMateTargetPhysicalBlockRepresentatives K hK target)
    (right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hright : right ∈
      globalInwardMateTargetPhysicalBlockRepresentatives K hK target)
    (heq :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw right) :
    left = right := by
  have hleftPhysical :=
    globalInwardMateTargetPhysicalBlockRepresentative_targetPhysical_eq
      htarget left hleft
  have hrightPhysical :=
    globalInwardMateTargetPhysicalBlockRepresentative_targetPhysical_eq
      htarget right hright
  have hleftCode :=
    globalInwardMateTargetPhysicalBlock_residualCode_mem_targetCodes
      htarget left hleft
  have hrightCode :=
    globalInwardMateTargetPhysicalBlock_residualCode_mem_targetCodes
      htarget right hright
  have hrawAt :
      globalInwardMateProductionRawAt K target
          (globalInwardMateTargetRepresentativeResidualCode left) =
        globalInwardMateProductionRawAt K target
          (globalInwardMateTargetRepresentativeResidualCode right) := by
    unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw at heq
    rw [hleftPhysical, hrightPhysical] at heq
    exact heq
  have hcode := globalInwardMateProductionRawAt_injective
    K target
    (fun faceId hface => Nat.le_of_lt_succ
      ((boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
        target htarget).1 faceId hface))
    hleftCode hrightCode hrawAt
  exact globalInwardMateTargetPhysicalBlock_residualCode_injective
    htarget left hleft right hright hcode

/-! ## 3. Global physical coordinates separate the remaining blocks -/

private theorem representative_mem_physical_block_local
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateTargetRepresentatives K hK) :
    source ∈ globalInwardMateTargetPhysicalBlockRepresentatives K hK
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source) := by
  unfold globalInwardMateTargetPhysicalBlockRepresentatives
  apply List.mem_filter.mpr
  exact ⟨hsource, by simp⟩

/-- The full production atom, including its physical coordinate, is
injective on the selected global target representatives. -/
theorem globalInwardMateTargetProductionAtom_injective
    {K : Nat} {hK : 1 ≤ K}
    (left : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hleft : left ∈ globalInwardMateTargetRepresentatives K hK)
    (right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hright : right ∈ globalInwardMateTargetRepresentatives K hK)
    (heq :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom right) :
    left = right := by
  have hphysical :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right := by
    have hprojection := congrArg Prod.fst heq
    simpa only [GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom]
      using hprojection
  have hraw :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw right := by
    have hprojection := congrArg Prod.snd heq
    simpa only [GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom]
      using hprojection
  let target := GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left
  have htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) :=
    GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_mem left
  have hleftBlock : left ∈
      globalInwardMateTargetPhysicalBlockRepresentatives K hK target :=
    representative_mem_physical_block_local left hleft
  have hrightBlock : right ∈
      globalInwardMateTargetPhysicalBlockRepresentatives K hK target := by
    unfold globalInwardMateTargetPhysicalBlockRepresentatives
    apply List.mem_filter.mpr
    refine ⟨hright, ?_⟩
    simp only [decide_eq_true_eq]
    exact congrArg
      (finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)) hphysical.symm
  exact globalInwardMateTargetPhysicalBlock_targetProductionRaw_injective
    htarget left hleftBlock right hrightBlock hraw

/-! ## 4. The literal duplicate-free production target subcarrier -/

/-- The exact list of recoded production atoms, one per distinct retained
target representative. -/
def globalInwardMateProductionTargetAtoms
    (K : Nat) (hK : 1 ≤ K) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (globalInwardMateTargetRepresentatives K hK).map
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom

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

/-- The production target atom list has no collisions. -/
theorem globalInwardMateProductionTargetAtoms_nodup
    (K : Nat) (hK : 1 ≤ K) :
    (globalInwardMateProductionTargetAtoms K hK).Nodup := by
  unfold globalInwardMateProductionTargetAtoms
  apply nodup_map_of_injOn
  · unfold globalInwardMateTargetRepresentatives
    apply nodup_of_map_nodup_local globalInwardMateTargetKey
    exact keyRepresentatives_keys_nodup globalInwardMateTargetKey
      (globalCubeInwardMateCertifiedTargetFullSources K hK)
  · intro left hleft right hright heq
    exact globalInwardMateTargetProductionAtom_injective
      left hleft right hright heq

/-- Every atom in the recoded list is a literal production BF4 expanded
source. -/
theorem globalInwardMateProductionTargetAtoms_mem_expanded
    (K : Nat) (hK : 1 ≤ K)
    (atom : SlabLabelling × SlabFusionWitnessAssignment)
    (hatom : atom ∈ globalInwardMateProductionTargetAtoms K hK) :
    atom ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K) := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hatom
  exact GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom_mem
    source hsource

/-- Summing the literal expanded BF4 weight over the collision-free recoded
list is the production-target weight sum. -/
theorem globalInwardMateProductionTargetAtoms_weight_eqv
    (K : Nat) (hK : 1 ≤ K) :
    listQSum
        (slabExpandedFineSourceWeight (globalInwardMateAnchorSlabData K))
        (globalInwardMateProductionTargetAtoms K hK) ≈
      listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
        (globalInwardMateTargetRepresentatives K hK) := by
  unfold globalInwardMateProductionTargetAtoms
  rw [listQSum_map]
  exact globalInwardMateProductionTargets_weight_eqv K hK

/-- **Literal retained production submeasure.**  The duplicate-free list of
actual BF4 expanded atoms carries at least the explicit positive fraction of
the extent-one physical partition. -/
theorem globalInwardMateRetainedTargetFraction_partition_le_productionAtoms
    (K : Nat) (hK : 1 ≤ K) :
    globalInwardMateRetainedTargetFraction *
        slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      listQSum
        (slabExpandedFineSourceWeight (globalInwardMateAnchorSlabData K))
        (globalInwardMateProductionTargetAtoms K hK) := by
  exact Q'.le_trans' _ _ _
    (globalInwardMateRetainedTargetFraction_partition_le_targets K hK)
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (globalInwardMateProductionTargetAtoms_weight_eqv K hK)))

/-- Type-level certificate for the literal collision-free retained target
subcarrier and its positive mass fraction. -/
structure GlobalInwardMateProductionTargetSubcarrierCertificate
    (K : Nat) (hK : 1 ≤ K) : Type where
  targets : List (SlabLabelling × SlabFusionWitnessAssignment)
  targets_nodup : targets.Nodup
  targets_mem : ∀ atom, atom ∈ targets →
    atom ∈ slabExpandedFineSources (globalInwardMateAnchorSlabData K)
  rate : Q'
  rate_positive : (0 : Q') < rate
  targetWeight_ge :
    rate * slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      listQSum
        (slabExpandedFineSourceWeight (globalInwardMateAnchorSlabData K))
        targets

/-- Construct the collision-free literal production target certificate at
every representation cutoff `K >= 1`. -/
def globalInwardMateProductionTargetSubcarrierCertificate
    (K : Nat) (hK : 1 ≤ K) :
    GlobalInwardMateProductionTargetSubcarrierCertificate K hK where
  targets := globalInwardMateProductionTargetAtoms K hK
  targets_nodup := globalInwardMateProductionTargetAtoms_nodup K hK
  targets_mem := globalInwardMateProductionTargetAtoms_mem_expanded K hK
  rate := globalInwardMateRetainedTargetFraction
  rate_positive := globalInwardMateRetainedTargetFraction_positive
  targetWeight_ge :=
    globalInwardMateRetainedTargetFraction_partition_le_productionAtoms K hK

#print axioms globalInwardMateProductionRawAt_injective
#print axioms globalInwardMateTargetPhysicalBlock_targetProductionRaw_injective
#print axioms globalInwardMateTargetProductionAtom_injective
#print axioms globalInwardMateProductionTargetAtoms
#print axioms globalInwardMateProductionTargetAtoms_nodup
#print axioms globalInwardMateProductionTargetAtoms_mem_expanded
#print axioms globalInwardMateProductionTargetAtoms_weight_eqv
#print axioms globalInwardMateRetainedTargetFraction_partition_le_productionAtoms
#print axioms GlobalInwardMateProductionTargetSubcarrierCertificate
#print axioms globalInwardMateProductionTargetSubcarrierCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionInjection
