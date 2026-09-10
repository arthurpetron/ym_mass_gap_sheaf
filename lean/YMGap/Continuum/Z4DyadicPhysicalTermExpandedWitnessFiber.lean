/-
# Reopen a corrected-slab physical term into accepted fusion witnesses

The cross-scale row is indexed by physical labellings, while the established
canonical component peel acts on accepted expanded sources carrying a global
fine-intertwiner assignment.  The auxiliary assignments were previously
summed into `SlabPhysicalData.physicalTerm`; this file reopens exactly that
finite fiber.

For every physical labelling in the production carrier we construct a
duplicate-free list of attached expanded entries above it.  Its weight is
exactly the original physical term.  The Cartesian product of two such
fibers is therefore an accepted two-replica state carrier with weight exactly
the product of the two physical terms.  The construction is valid at the
coupling stored in `D`; no beta-uniform estimate is made.

Constructive contract: existing accepted-assignment lists, attachment, and
finite rational Fubini only; no classical choice, proof hole, trusted
external computation, computability escape, heartbeat increase, or new
axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
import YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier

namespace YMGap.Continuum.Z4DyadicPhysicalTermExpandedWitnessFiber

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One physical-label fiber -/

/-- Every accepted global fusion assignment above one fixed physical
labelling, attached to its membership in the full expanded source carrier. -/
def slabPhysicalExpandedEntryBlock
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (hphysical : physical ∈ D.physicalLabellings) :
    List (SlabExpandedFineSourceEntry D) :=
  (slabFineFusionWitnesses D physical).attach.map fun assignment =>
    ⟨(physical, assignment.1),
      (mem_slabExpandedFineSources_iff).mpr
        ⟨hphysical, assignment.2⟩⟩

/-- Every entry in the block has literally the requested physical
labelling. -/
theorem slabPhysicalExpandedEntryBlock_physical_eq
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (hphysical : physical ∈ D.physicalLabellings)
    (entry : SlabExpandedFineSourceEntry D)
    (hentry : entry ∈
      slabPhysicalExpandedEntryBlock D physical hphysical) :
    entry.1.1 = physical := by
  unfold slabPhysicalExpandedEntryBlock at hentry
  obtain ⟨assignment, _, heq⟩ := List.mem_map.mp hentry
  rw [← heq]

/-- The fixed-physical assignment block has no duplicate expanded entry. -/
theorem slabPhysicalExpandedEntryBlock_nodup
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (hphysical : physical ∈ D.physicalLabellings) :
    (slabPhysicalExpandedEntryBlock D physical hphysical).Nodup := by
  unfold slabPhysicalExpandedEntryBlock
  apply nodup_map_of_injOn
  · exact attach_nodup_of_nodup _
      (slabFineFusionWitnesses_nodup D physical)
  · intro left _ right _ heq
    apply Subtype.ext
    exact congrArg (fun entry : SlabExpandedFineSourceEntry D =>
      entry.1.2) heq

/-- Reopening the accepted assignment fiber exactly recovers the physical
term already used by the cross-scale row. -/
theorem slabPhysicalExpandedEntryBlock_weight_total
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (hphysical : physical ∈ D.physicalLabellings) :
    listQSum (slabExpandedFineEntryWeight D)
        (slabPhysicalExpandedEntryBlock D physical hphysical) ≈
      D.physicalTerm physical := by
  unfold slabPhysicalExpandedEntryBlock
  rw [listQSum_map]
  change
    listQSum
        (fun assignment :
          {assignment // assignment ∈ slabFineFusionWitnesses D physical} =>
          retainedFineIntertwinerPhysicalFiberWeight
            D physical assignment.1)
        (slabFineFusionWitnesses D physical).attach ≈
      D.physicalTerm physical
  rw [listQSum_attach]
  exact retainedFineIntertwinerPhysicalFiberWeight_total D physical

/-! ## 2. A two-replica accepted-state fiber -/

/-- Literal accepted two-replica states above a fixed pair of physical
labellings. -/
def slabPhysicalPairExpandedStateCarrier
    (D : SlabPhysicalData)
    (first : SlabLabelling) (hfirst : first ∈ D.physicalLabellings)
    (second : SlabLabelling) (hsecond : second ∈ D.physicalLabellings) :
    List (SlabAcceptedTwoReplicaState D) :=
  cartesian
    (slabPhysicalExpandedEntryBlock D first hfirst)
    (slabPhysicalExpandedEntryBlock D second hsecond)

/-- The fixed-physical pair carrier is duplicate-free. -/
theorem slabPhysicalPairExpandedStateCarrier_nodup
    (D : SlabPhysicalData)
    (first : SlabLabelling) (hfirst : first ∈ D.physicalLabellings)
    (second : SlabLabelling) (hsecond : second ∈ D.physicalLabellings) :
    (slabPhysicalPairExpandedStateCarrier
      D first hfirst second hsecond).Nodup := by
  unfold slabPhysicalPairExpandedStateCarrier
  exact cartesian_nodup _ _
    (slabPhysicalExpandedEntryBlock_nodup D first hfirst)
    (slabPhysicalExpandedEntryBlock_nodup D second hsecond)

/-- Every fixed-physical pair is an element of the complete accepted
terminal carrier. -/
theorem slabPhysicalPairExpandedStateCarrier_mem_terminal
    (D : SlabPhysicalData)
    (first : SlabLabelling) (hfirst : first ∈ D.physicalLabellings)
    (second : SlabLabelling) (hsecond : second ∈ D.physicalLabellings)
    (state : SlabAcceptedTwoReplicaState D)
    (_hstate : state ∈ slabPhysicalPairExpandedStateCarrier
      D first hfirst second hsecond) :
    state ∈ slabAcceptedTwoReplicaStates D := by
  exact slabAcceptedTwoReplicaState_mem D state

/-- The two-replica expanded fiber has exactly the product of the original
physical terms. -/
theorem slabPhysicalPairExpandedStateCarrier_weight_total
    (D : SlabPhysicalData)
    (first : SlabLabelling) (hfirst : first ∈ D.physicalLabellings)
    (second : SlabLabelling) (hsecond : second ∈ D.physicalLabellings) :
    listQSum
        (slabAcceptedTwoReplicaStateWeight D)
        (slabPhysicalPairExpandedStateCarrier
          D first hfirst second hsecond) ≈
      D.physicalTerm first * D.physicalTerm second := by
  let firstBlock := slabPhysicalExpandedEntryBlock D first hfirst
  let secondBlock := slabPhysicalExpandedEntryBlock D second hsecond
  have hcart := listQSum_cartesian_product
    (slabExpandedFineEntryWeight D)
    (slabExpandedFineEntryWeight D)
    firstBlock secondBlock
  have hfirstWeight :=
    slabPhysicalExpandedEntryBlock_weight_total D first hfirst
  have hsecondWeight :=
    slabPhysicalExpandedEntryBlock_weight_total D second hsecond
  refine Q'.eqv_trans _
    (listQSum (slabExpandedFineEntryWeight D) firstBlock *
      listQSum (slabExpandedFineEntryWeight D) secondBlock) _ ?_ ?_
  · simpa only [firstBlock, secondBlock,
      slabPhysicalPairExpandedStateCarrier,
      slabAcceptedTwoReplicaStateWeight] using hcart
  · exact Q'.eqv_trans _
      (D.physicalTerm first *
        listQSum (slabExpandedFineEntryWeight D) secondBlock) _
      (Q'.mul_eqv_congr_right _ _ _ hfirstWeight)
      (Q'.mul_eqv_congr_left _ _ _ hsecondWeight)

#print axioms slabPhysicalExpandedEntryBlock
#print axioms slabPhysicalExpandedEntryBlock_physical_eq
#print axioms slabPhysicalExpandedEntryBlock_nodup
#print axioms slabPhysicalExpandedEntryBlock_weight_total
#print axioms slabPhysicalPairExpandedStateCarrier
#print axioms slabPhysicalPairExpandedStateCarrier_nodup
#print axioms slabPhysicalPairExpandedStateCarrier_mem_terminal
#print axioms slabPhysicalPairExpandedStateCarrier_weight_total

end YMGap.Continuum.Z4DyadicPhysicalTermExpandedWitnessFiber
