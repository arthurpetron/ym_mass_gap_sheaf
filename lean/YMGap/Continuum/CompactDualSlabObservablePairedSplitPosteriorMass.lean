/-
# Split posterior mass: glue disjoint disconnected and connected transports

The posterior transport is now best expressed as two physical-sector
branches rather than one dependent sum:

* the support-disconnected branch is the existing normalized involutive
  support switch;
* the support-connected branch is the canonically thinned successful strand
  switch.

Both branches preserve complete Gibbs weight, have column capacity, and land
in disjoint target sectors.  Exact finite Fubini therefore bounds the first
source mass by the disconnected target mass and the second transported mass
by the connected target mass.  Adding the bounds and using the exact target
partition gives one shared physical budget without constructing a global
paired-face decoder.

The connected thinned transported mass may still be zero.  Positivity and a
quantitative aggregate fraction are deliberately left as the next theorem.

Constructive contract: finite filtered carriers, exact dependent-kernel
Fubini, and `Q'` algebra only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning

namespace YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance splitPosteriorPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

/-! ## 1. Exact target-sector partition -/

def slabObservablePairedSupportConnectedFourCellTargetPairs
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  (slabObservableFourCellTargetPairs D rootFaceId targetFaceId).filter
    fun pair => slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId pair

def slabObservablePairedSupportDisconnectedFourCellTargetPairs
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  (slabObservableFourCellTargetPairs D rootFaceId targetFaceId).filter
    fun pair => !(slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId pair)

theorem slabObservableFourCellTargetPairs_pairedSupport_partition
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs D rootFaceId targetFaceId) ≈
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportConnectedFourCellTargetPairs
            D rootFaceId targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportDisconnectedFourCellTargetPairs
            D rootFaceId targetFaceId) := by
  exact listQSum_filter_partition
    (slabObservableTwoReplicaPairWeight D)
    (fun pair : SlabObservableTwoReplicaPair D rootFaceId =>
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId pair)
    (slabObservableFourCellTargetPairs D rootFaceId targetFaceId)

/-! ## 2. The normalized disconnected branch spends only disconnected columns -/

/-- The normalized disconnected kernel respects the literal physical capacity
of every target column.  This is the pointwise form of the column argument
used by the aggregate disconnected-sector budget below. -/
theorem slabObservablePairedSupportSeparatedWeightedColumn_le_disconnectedTarget
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (receiver : SlabObservableTwoReplicaPair D rootFaceId) :
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1 *
          dependentKernelPushforwardWeight
            (SlabObservablePairedSupportRecouplingChoice
              D rootFaceId targetFaceId)
            (slabObservablePairedSupportRecouplingChoices
              D rootFaceId targetFaceId)
            (slabObservablePairedSupportRecouplingWeight
              D rootFaceId targetFaceId htarget)
            (slabObservablePairedSupportRecoupledTargetPair
              D rootFaceId targetFaceId htarget)
            source receiver)
        (slabObservablePairedSupportSeparatedSources
          D rootFaceId targetFaceId) ≤
      slabObservableTwoReplicaPairWeight D receiver := by
  exact weightedColumn_le_of_columnCapacity
    (slabObservablePairedSupportSeparatedSources
      D rootFaceId targetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (slabObservableTwoReplicaPairWeight D)
    (SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId)
    (slabObservablePairedSupportRecouplingChoices
      D rootFaceId targetFaceId)
    (slabObservablePairedSupportRecouplingWeight
      D rootFaceId targetFaceId htarget)
    (slabObservablePairedSupportRecoupledTargetPair
      D rootFaceId targetFaceId htarget)
    receiver
    (slabObservableTwoReplicaPairWeight_nonnegative
      D rootFaceId receiver)
    (fun source _ choice heq => by
      rw [heq]
      exact slabObservablePairedSupportRecoupledTargetPair_weight_preserved
        D rootFaceId targetFaceId htarget source choice)
    (slabObservablePairedSupportDependentColumnCapacity
      D rootFaceId targetFaceId htarget receiver)

theorem slabObservablePairedSupportSeparated_weight_le_disconnectedTarget
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportSeparatedFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportDisconnectedFourCellTargetPairs
          D rootFaceId targetFaceId) := by
  have htransport :=
    sourceWeight_total_le_of_dependentKernelCapacity
      (sources := slabObservablePairedSupportSeparatedSources
        D rootFaceId targetFaceId)
      (sourceWeight := fun source =>
        slabObservableTwoReplicaPairWeight D source.1)
      (targets := slabObservablePairedSupportDisconnectedFourCellTargetPairs
        D rootFaceId targetFaceId)
      (targetWeight := slabObservableTwoReplicaPairWeight D)
      (Choice := SlabObservablePairedSupportRecouplingChoice
        D rootFaceId targetFaceId)
      (choices := slabObservablePairedSupportRecouplingChoices
        D rootFaceId targetFaceId)
      (localWeight := slabObservablePairedSupportRecouplingWeight
        D rootFaceId targetFaceId htarget)
      (realize := slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget)
      ((slabObservableFourCellTargetPairs_nodup
        D rootFaceId targetFaceId).filter _)
      (fun source _ choice _ => by
        apply List.mem_filter.mpr
        exact ⟨slabObservablePairedSupportRecoupledTargetPair_mem
            D rootFaceId targetFaceId htarget source choice,
          by rw [slabObservablePairedSupportRecoupledTargetPair_disconnected]
             rfl⟩)
      (fun source _ =>
        slabObservablePairedSupportRecouplingWeight_row_normalized
          D rootFaceId targetFaceId htarget source)
      (fun target _ =>
        weightedColumn_le_of_columnCapacity
          (slabObservablePairedSupportSeparatedSources
            D rootFaceId targetFaceId)
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          (slabObservableTwoReplicaPairWeight D)
          (SlabObservablePairedSupportRecouplingChoice
            D rootFaceId targetFaceId)
          (slabObservablePairedSupportRecouplingChoices
            D rootFaceId targetFaceId)
          (slabObservablePairedSupportRecouplingWeight
            D rootFaceId targetFaceId htarget)
          (slabObservablePairedSupportRecoupledTargetPair
            D rootFaceId targetFaceId htarget)
          target
          (slabObservableTwoReplicaPairWeight_nonnegative
            D rootFaceId target)
          (fun source _ choice heq => by
            rw [heq]
            exact slabObservablePairedSupportRecoupledTargetPair_weight_preserved
              D rootFaceId targetFaceId htarget source choice)
          (slabObservablePairedSupportDependentColumnCapacity
            D rootFaceId targetFaceId htarget target))
  simpa only [slabObservablePairedSupportSeparatedSources,
    listQSum_attach] using htransport

/-! ## 3. The thinned connected branch spends only connected columns -/

def slabObservablePairedConnectedStrandThinnedRowMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) : Q' :=
  listQSum
    (slabObservablePairedConnectedStrandThinnedWeight
      D rootFaceId targetFaceId htarget source)
    (slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId source)

def slabObservablePairedConnectedStrandThinnedTransportedMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) : Q' :=
  listQSum
    (fun source => slabObservableTwoReplicaPairWeight D source.1 *
      slabObservablePairedConnectedStrandThinnedRowMass
        D rootFaceId targetFaceId htarget source)
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)

theorem slabObservablePairedConnectedStrandThinnedTransportedMass_le_connectedTarget
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabObservablePairedConnectedStrandThinnedTransportedMass
        D rootFaceId targetFaceId htarget ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellTargetPairs
          D rootFaceId targetFaceId) := by
  exact sourceWeightedRowMass_total_le_of_dependentKernelCapacity
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (slabObservablePairedConnectedStrandThinnedRowMass
      D rootFaceId targetFaceId htarget)
    (slabObservablePairedSupportConnectedFourCellTargetPairs
      D rootFaceId targetFaceId)
    (slabObservableTwoReplicaPairWeight D)
    (SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandThinnedWeight
      D rootFaceId targetFaceId htarget)
    (slabObservablePairedConnectedStrandRealize
      D rootFaceId targetFaceId htarget)
    ((slabObservableFourCellTargetPairs_nodup
      D rootFaceId targetFaceId).filter _)
    (fun source _ choice _ => by
      apply List.mem_filter.mpr
      exact ⟨slabObservablePairedConnectedStrandRealize_mem
          D rootFaceId targetFaceId htarget source choice,
        slabObservablePairedConnectedStrandRealize_connected
          D rootFaceId targetFaceId htarget source choice⟩)
    (fun _ _ => Q'.eqv_refl _)
    (fun target _ =>
      slabObservablePairedConnectedStrandThinnedWeightedColumn_le
        D rootFaceId targetFaceId htarget target)

/-! ## 4. One shared target budget, obtained by sector gluing -/

/-- **Decoder-free split posterior budget.**  The complete disconnected
source mass plus the actually retained connected mass fits in the opposite
four-cell target mass. -/
theorem slabObservablePairedSplitTransportedMass_le_target
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportSeparatedFourCellSourcePairs
          D rootFaceId targetFaceId) +
      slabObservablePairedConnectedStrandThinnedTransportedMass
        D rootFaceId targetFaceId htarget ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId) := by
  have hbranches := Q'.add_le_add
    (slabObservablePairedSupportSeparated_weight_le_disconnectedTarget
      D rootFaceId targetFaceId htarget)
    (slabObservablePairedConnectedStrandThinnedTransportedMass_le_connectedTarget
      D rootFaceId targetFaceId htarget)
  have htargets :
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportDisconnectedFourCellTargetPairs
            D rootFaceId targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportConnectedFourCellTargetPairs
            D rootFaceId targetFaceId) ≈
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId) :=
    Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv _ _)
      (Q'.eqv_symm
        (slabObservableFourCellTargetPairs_pairedSupport_partition
          D rootFaceId targetFaceId))
  exact Q'.le_trans' _ _ _ hbranches (Q'.le_of_eqv htargets)

end YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass.slabObservableFourCellTargetPairs_pairedSupport_partition
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass.slabObservablePairedSupportSeparatedWeightedColumn_le_disconnectedTarget
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass.slabObservablePairedSupportSeparated_weight_le_disconnectedTarget
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass.slabObservablePairedConnectedStrandThinnedTransportedMass_le_connectedTarget
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass.slabObservablePairedSplitTransportedMass_le_target
