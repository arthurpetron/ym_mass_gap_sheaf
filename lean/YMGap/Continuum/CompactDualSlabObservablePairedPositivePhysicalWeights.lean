/-
# Strict positivity of the literal paired physical weights

At zero coupling, non-vacuum heat-kernel coefficients may vanish.  The
finite connected posterior can therefore only be strictly coercive under an
explicit positive-coupling hypothesis.  This module propagates that honest
hypothesis through the corrected-slab face product and the two unit-counted
fine-intertwiner fibers.

Every attached source already carries the physical cutoff bound.  Hence each
coefficient selected by the finite heat-kernel packet is the strictly positive
`coeffW` value rather than the packet's zero extension.  Finite products then
give strictly positive one-replica and paired Gibbs weights, including every
source in the connected strand carrier.

Constructive contract: structural list induction and exact `Q'` positivity
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
`noncomputable` declaration, or enlarged heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
import YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment

namespace YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Strict positivity of the bounded heat-kernel face product -/

private theorem eliminateLinks_pos_on
    (value : Nat -> Q') :
    forall ids : List Nat,
      (forall id, id ∈ ids -> (0 : Q') < value id) ->
        (0 : Q') < eliminateLinks value ids
  | [], _ => by
      change (0 : Q') < 1
      decide
  | head :: tail, hvalue =>
      Q'.mul_pos
        (hvalue head List.mem_cons_self)
        (eliminateLinks_pos_on value tail
          (fun id hid => hvalue id (List.mem_cons_of_mem head hid)))

/-- A corrected-slab face product is strictly positive at positive coupling
whenever every physical face label lies inside the packet cutoff. -/
theorem slabParametricKPhysicalFaceFactor_pos_of_bounded
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (physical : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded
      D.cutoff D.extent physical) :
    (0 : Q') < slabParametricKPhysicalFaceFactor
      D.coupling D.cutoff D.extent physical := by
  unfold slabParametricKPhysicalFaceFactor
  apply eliminateLinks_pos_on
  intro faceId hface
  have hspin : physical faceId < D.cutoff + 1 :=
    Nat.lt_succ_of_le (hbounded faceId hface)
  rw [coeffAt_heatKernelPacket hspin]
  exact coeffW_pos hcoupling _

/-! ## 2. Attached one-replica and paired weights -/

/-- Every attached expanded source has positive physical weight at positive
coupling. -/
theorem slabExpandedFineEntryWeight_pos_of_coupling_pos
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (entry : SlabExpandedFineSourceEntry D) :
    (0 : Q') < slabExpandedFineEntryWeight D entry := by
  unfold slabExpandedFineEntryWeight slabExpandedFineSourceWeight
    retainedFineIntertwinerPhysicalFiberWeight
    retainedFineIntertwinerRawWeight
  exact Q'.mul_pos
    (slabParametricKPhysicalFaceFactor_pos_of_bounded
      D hcoupling entry.1.1
        (YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment.SlabExpandedFineSourceEntry.physical_bounded
          entry))
    (by decide)

/-- Restricting the first replica to the positive-face carrier preserves its
strict Gibbs positivity. -/
theorem slabObservablePositiveEntryWeight_pos_of_coupling_pos
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    {faceId : Nat} (entry : SlabObservablePositiveSourceEntry D faceId) :
    (0 : Q') < slabObservablePositiveEntryWeight D entry := by
  unfold slabObservablePositiveEntryWeight
  exact slabExpandedFineEntryWeight_pos_of_coupling_pos D hcoupling
    ⟨entry.1, entry.source_mem_expanded⟩

/-- Both factors of every literal two-replica source are strictly positive at
positive coupling. -/
theorem slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    {rootFaceId : Nat} (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    (0 : Q') < slabObservableTwoReplicaPairWeight D pair := by
  unfold slabObservableTwoReplicaPairWeight
  exact Q'.mul_pos
    (slabObservablePositiveEntryWeight_pos_of_coupling_pos
      D hcoupling pair.1)
    (slabExpandedFineEntryWeight_pos_of_coupling_pos
      D hcoupling pair.2)

/-- In particular, every source row of the support-connected strand kernel
has a strictly positive Gibbs prefactor at positive coupling. -/
theorem slabObservablePairedConnectedStrandSourceWeight_pos_of_coupling_pos
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    (0 : Q') < slabObservableTwoReplicaPairWeight D source.1 :=
  slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
    D hcoupling source.1

end YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights.slabParametricKPhysicalFaceFactor_pos_of_bounded
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights.slabExpandedFineEntryWeight_pos_of_coupling_pos
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights.slabObservablePositiveEntryWeight_pos_of_coupling_pos
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights.slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights.slabObservablePairedConnectedStrandSourceWeight_pos_of_coupling_pos
