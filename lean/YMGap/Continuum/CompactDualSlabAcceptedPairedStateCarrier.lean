/-
# Complete carrier for accepted paired terminal states

Canonical observable peeling lands in a pair of literal expanded slab
sources.  This module enumerates that terminal space as the Cartesian square
of the already attached expanded-source carrier.  Its total weight is exactly
the square of the corrected-slab physical partition.

The same finite carrier supplies a uniform trace-mass ceiling.  Each replica
has physical mass at most `faceCount * cutoff`, so every paired canonical
trace has mass at most twice that number.  These are the two finite axes
needed to partition the global connected residue by terminal and paid mass.

Constructive contract: literal finite lists, bounded Cartesian labellings,
and natural-number telescoping only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
import YMGap.Continuum.CompactDualSlabObservableRemovalPartition

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal finite terminal carrier -/

/-- Every accepted two-replica terminal, enumerated without duplicates. -/
def slabAcceptedTwoReplicaStates (D : SlabPhysicalData) :
    List (SlabAcceptedTwoReplicaState D) :=
  cartesian (slabExpandedFineSourceEntries D)
    (slabExpandedFineSourceEntries D)

theorem slabAcceptedTwoReplicaStates_nodup (D : SlabPhysicalData) :
    (slabAcceptedTwoReplicaStates D).Nodup := by
  exact cartesian_nodup _ _
    (slabExpandedFineSourceEntries_nodup D)
    (slabExpandedFineSourceEntries_nodup D)

theorem slabAcceptedTwoReplicaState_mem
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) :
    state ∈ slabAcceptedTwoReplicaStates D := by
  apply (mem_cartesian_iff _ _ state).mpr
  constructor
  · exact List.mem_attach _ state.1
  · exact List.mem_attach _ state.2

/-- The terminal carrier has exactly the two-replica partition weight. -/
theorem slabAcceptedTwoReplicaStates_weight_total
    (cutoff half : Nat) :
    listQSum (slabAcceptedTwoReplicaStateWeight cutoff half)
        (slabAcceptedTwoReplicaStates
          (anchorSlabPhysicalData cutoff half)) ≈
      (anchorSlabPhysicalData cutoff half).physicalPartition *
        (anchorSlabPhysicalData cutoff half).physicalPartition := by
  let D := anchorSlabPhysicalData cutoff half
  have hcart := listQSum_cartesian_product
    (slabExpandedFineEntryWeight D)
    (slabExpandedFineEntryWeight D)
    (slabExpandedFineSourceEntries D)
    (slabExpandedFineSourceEntries D)
  have hpartition := slabExpandedFineSourceEntries_weight_total D
  refine Q'.eqv_trans _
    (listQSum (slabExpandedFineEntryWeight D)
        (slabExpandedFineSourceEntries D) *
      listQSum (slabExpandedFineEntryWeight D)
        (slabExpandedFineSourceEntries D)) _ ?_ ?_
  · simpa only [D, slabAcceptedTwoReplicaStates,
      slabAcceptedTwoReplicaStateWeight] using hcart
  · exact Q'.eqv_trans _
      ((anchorSlabPhysicalData cutoff half).physicalPartition *
        listQSum (slabExpandedFineEntryWeight D)
          (slabExpandedFineSourceEntries D)) _
      (Q'.mul_eqv_congr_right _ _ _ hpartition)
      (Q'.mul_eqv_congr_left _ _ _ hpartition)

/-! ## 2. A common paid-mass ceiling -/

private theorem listNatWeight_le_length_mul
    {A : Type} (weight : A → Nat) (bound : Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → weight item ≤ bound) →
      listNatWeight weight items ≤ items.length * bound
  | [], _ => by simp [listNatWeight]
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := listNatWeight_le_length_mul weight bound tail
        (fun item hitem =>
          hbound item (List.mem_cons_of_mem head hitem))
      simp only [listNatWeight, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- One accepted expanded source carries at most one cutoff unit per slab
face. -/
theorem slabExpandedFineEntry_physicalMass_le
    (D : SlabPhysicalData) (entry : SlabExpandedFineSourceEntry D) :
    slabPhysicalLabellingMass D.extent entry.1.1 ≤
      slabObservableRemovalMaxSize D := by
  unfold slabPhysicalLabellingMass slabObservableRemovalMaxSize
    SlabPhysicalData.faceEdges
  apply listNatWeight_le_length_mul entry.1.1 D.cutoff
  intro faceId hface
  have hphysical := (mem_slabExpandedFineSources_iff.mp entry.2).1
  exact Nat.le_of_lt_succ
    ((boundedEdgeLabellings_sound D.cutoff
      (slabPhysicalFaceEdges D.extent) entry.1.1 hphysical).1
        faceId hface)

/-- Both replicas together carry at most twice the one-copy mass ceiling. -/
theorem slabAcceptedTwoReplicaStateMass_le
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) :
    slabAcceptedTwoReplicaStateMass state ≤
      2 * slabObservableRemovalMaxSize D := by
  have hleft := slabExpandedFineEntry_physicalMass_le D state.1
  have hright := slabExpandedFineEntry_physicalMass_le D state.2
  unfold slabAcceptedTwoReplicaStateMass
  omega

/-- Canonical peeling cannot pay more trace mass than its initial paired
physical mass. -/
theorem slabAcceptedPairCanonicalPeeling_traceMass_le
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    slabAcceptedPairedPeelTraceMass
        (slabAcceptedPairCanonicalPeeling
          D faces hphysical state).2 ≤
      2 * slabObservableRemovalMaxSize D := by
  have htelescope := slabAcceptedPairCanonicalPeeling_mass_telescope
    D faces hphysical state
  have hmass := slabAcceptedTwoReplicaStateMass_le D state
  omega

#print axioms slabAcceptedTwoReplicaStates
#print axioms slabAcceptedTwoReplicaStates_nodup
#print axioms slabAcceptedTwoReplicaState_mem
#print axioms slabAcceptedTwoReplicaStates_weight_total
#print axioms slabExpandedFineEntry_physicalMass_le
#print axioms slabAcceptedTwoReplicaStateMass_le
#print axioms slabAcceptedPairCanonicalPeeling_traceMass_le

end YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
