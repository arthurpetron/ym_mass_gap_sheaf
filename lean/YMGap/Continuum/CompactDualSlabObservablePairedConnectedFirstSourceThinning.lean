/-
# First-source column capacity for the connected strand posterior

Restrict the successful SU(2) strand-recoupling row to the physical
union-support connected source sector.  Its direct paired-face realization
can be many-to-one, so this module applies canonical first-source thinning:
for each final physical target, only successful channels from the first
listed connected source reaching that target are retained.

Every original successful row is a nonnegative subrow of a normalized SU(2)
recoupling row.  The generic thinning theorem therefore gives unweighted
column capacity.  Exact Gibbs-weight preservation upgrades it to the physical
weighted column bound.  Target-sector invariance also proves that every
realized output remains support-connected.

Zero-weight successful channels are discarded before first-source search, so
every listed retained candidate is strictly positive.  The retained connected
row mass is explicit but is not proved positive here because the filtered list
may still be empty.  Thus this closes the decoder-free connected
column-capacity node and the zero-channel selector defect, not the aggregate
posterior floor.

Constructive contract: finite attached lists, explicit SU(2) row weights,
canonical first-source search, and exact `Q'` inequalities only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration.  Elaboration uses a finite one-million-heartbeat bound for the
dependent successful-choice carrier.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation
import YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport
import YMGap.Continuum.FiniteDependentKernelFirstSourceThinning

namespace YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance connectedThinningPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

/-! ## 1. The exact connected source carrier -/

abbrev SlabObservablePairedConnectedStrandSource
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :=
  {pair // pair ∈ slabObservablePairedSupportConnectedFourCellSourcePairs
    D rootFaceId targetFaceId}

def slabObservablePairedConnectedStrandSources
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :=
  (slabObservablePairedSupportConnectedFourCellSourcePairs
    D rootFaceId targetFaceId).attach

theorem slabObservablePairedConnectedStrandSources_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId).Nodup := by
  unfold slabObservablePairedConnectedStrandSources
  exact attach_nodup_of_nodup _
    ((slabObservableFourCellSourcePairs_nodup
      D rootFaceId targetFaceId).filter _)

def SlabObservablePairedConnectedStrandSource.toRecouplingSource
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId :=
  ⟨source.1, (List.mem_filter.mp source.2).1⟩

theorem SlabObservablePairedConnectedStrandSource.connected
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId source.1 = true :=
  (List.mem_filter.mp source.2).2

/-! ## 2. The successful strand row on that carrier -/

abbrev SlabObservablePairedConnectedStrandChoice
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :=
  SlabObservablePairedStrandSuccessfulChoice
    D rootFaceId targetFaceId source.toRecouplingSource

def slabObservablePairedConnectedStrandChoices
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    List (SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source) :=
  (slabObservablePairedStrandSuccessfulChoices
    D rootFaceId targetFaceId source.toRecouplingSource).filter
      fun choice => decide ((0 : Q') <
        slabObservablePairedStrandSuccessfulWeight
          D rootFaceId targetFaceId source.toRecouplingSource choice)

def slabObservablePairedConnectedStrandWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source) : Q' :=
  slabObservablePairedStrandSuccessfulWeight
    D rootFaceId targetFaceId source.toRecouplingSource choice

def slabObservablePairedConnectedStrandRealize
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source) :
    SlabObservableTwoReplicaPair D rootFaceId :=
  slabObservablePairedStrandRecoupledTargetPair
    D rootFaceId targetFaceId htarget source.toRecouplingSource choice

theorem slabObservablePairedStrandDisconnectionMass_le_one
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :
    slabObservablePairedStrandDisconnectionMass
      D rootFaceId targetFaceId source ≤ 1 := by
  unfold slabObservablePairedStrandDisconnectionMass
    slabObservablePairedStrandSuccessfulRecouplingChoices
  exact Q'.le_trans' _ _ _
    (listQSum_filter_le_of_nonnegative
      (slabObservablePairedStrandRecouplingWeight
        D rootFaceId targetFaceId source)
      (slabObservablePairedStrandRecouplingSuccessB
        D rootFaceId targetFaceId source)
      (slabObservablePairedStrandRecouplingWeight_nonnegative
        D rootFaceId targetFaceId source)
      (slabObservablePairedStrandRecouplingChoices
        D rootFaceId targetFaceId source))
    (Q'.le_of_eqv
      (slabObservablePairedStrandRecouplingWeight_row_normalized
        D rootFaceId targetFaceId source))

theorem slabObservablePairedConnectedStrandWeight_nonnegative
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source) :
    (0 : Q') ≤ slabObservablePairedConnectedStrandWeight
      D rootFaceId targetFaceId source choice :=
  slabObservablePairedStrandSuccessfulWeight_nonnegative
    D rootFaceId targetFaceId source.toRecouplingSource choice

/-- Every listed connected channel has strictly positive SU(2) row weight;
zero entries are discarded before first-source selection. -/
theorem slabObservablePairedConnectedStrandWeight_pos_of_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source)
    (hchoice : choice ∈ slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId source) :
    (0 : Q') < slabObservablePairedConnectedStrandWeight
      D rootFaceId targetFaceId source choice := by
  exact of_decide_eq_true (List.mem_filter.mp hchoice).2

theorem slabObservablePairedConnectedStrandWeight_row_le_one
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    listQSum
        (slabObservablePairedConnectedStrandWeight
          D rootFaceId targetFaceId source)
        (slabObservablePairedConnectedStrandChoices
          D rootFaceId targetFaceId source) ≤ 1 := by
  have hfilter :
      listQSum
          (slabObservablePairedConnectedStrandWeight
            D rootFaceId targetFaceId source)
          (slabObservablePairedConnectedStrandChoices
            D rootFaceId targetFaceId source) ≤
        listQSum
          (slabObservablePairedConnectedStrandWeight
            D rootFaceId targetFaceId source)
          (slabObservablePairedStrandSuccessfulChoices
            D rootFaceId targetFaceId source.toRecouplingSource) := by
    unfold slabObservablePairedConnectedStrandChoices
    exact listQSum_filter_le_of_nonnegative _ _
      (slabObservablePairedConnectedStrandWeight_nonnegative
        D rootFaceId targetFaceId source) _
  exact Q'.le_trans' _ _ _ hfilter
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (slabObservablePairedStrandSuccessfulWeight_row_mass
          D rootFaceId targetFaceId source.toRecouplingSource))
      (slabObservablePairedStrandDisconnectionMass_le_one
        D rootFaceId targetFaceId source.toRecouplingSource))

/-! ## 3. Canonical thinning and unweighted column capacity -/

def slabObservablePairedConnectedStrandThinnedWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) →
      SlabObservablePairedConnectedStrandChoice
        D rootFaceId targetFaceId source → Q' :=
  firstSourceThinnedWeight
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)
    (SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandWeight
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandRealize
      D rootFaceId targetFaceId htarget)

theorem slabObservablePairedConnectedStrandThinnedWeight_nonnegative
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source) :
    (0 : Q') ≤ slabObservablePairedConnectedStrandThinnedWeight
      D rootFaceId targetFaceId htarget source choice := by
  apply firstSourceThinnedWeight_nonnegative
  exact slabObservablePairedConnectedStrandWeight_nonnegative
    D rootFaceId targetFaceId source choice

theorem slabObservablePairedConnectedStrandThinnedColumn_le_one
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    listQSum
        (fun source => dependentKernelPushforwardWeight
          (SlabObservablePairedConnectedStrandChoice
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandChoices
            D rootFaceId targetFaceId)
          (slabObservablePairedConnectedStrandThinnedWeight
            D rootFaceId targetFaceId htarget)
          (slabObservablePairedConnectedStrandRealize
            D rootFaceId targetFaceId htarget)
          source target)
        (slabObservablePairedConnectedStrandSources
          D rootFaceId targetFaceId) ≤ 1 := by
  apply firstSourceThinnedColumn_le_one
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandSources_nodup
      D rootFaceId targetFaceId)
    (SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandWeight
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandRealize
      D rootFaceId targetFaceId htarget)
  · intro source _ choice
    exact slabObservablePairedConnectedStrandWeight_nonnegative
      D rootFaceId targetFaceId source choice
  · intro source _
    exact slabObservablePairedConnectedStrandWeight_row_le_one
      D rootFaceId targetFaceId source

/-! ## 4. Coverage, sector separation, and weighted capacity -/

theorem slabObservablePairedConnectedStrandRealize_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source) :
    slabObservablePairedConnectedStrandRealize
        D rootFaceId targetFaceId htarget source choice ∈
      slabObservableFourCellTargetPairs
        D rootFaceId targetFaceId :=
  slabObservablePairedStrandRecoupledTargetPair_mem
    D rootFaceId targetFaceId htarget source.toRecouplingSource choice

theorem slabObservablePairedConnectedStrandRealize_connected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId
        (slabObservablePairedConnectedStrandRealize
          D rootFaceId targetFaceId htarget source choice) = true :=
  slabObservablePairedStrandRecoupledTargetPair_connected
    D rootFaceId targetFaceId htarget source.toRecouplingSource choice
    source.connected

/-- **Physical connected-column capacity without a decoder.** -/
theorem slabObservablePairedConnectedStrandThinnedWeightedColumn_le
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1 *
          dependentKernelPushforwardWeight
            (SlabObservablePairedConnectedStrandChoice
              D rootFaceId targetFaceId)
            (slabObservablePairedConnectedStrandChoices
              D rootFaceId targetFaceId)
            (slabObservablePairedConnectedStrandThinnedWeight
              D rootFaceId targetFaceId htarget)
            (slabObservablePairedConnectedStrandRealize
              D rootFaceId targetFaceId htarget)
            source target)
        (slabObservablePairedConnectedStrandSources
          D rootFaceId targetFaceId) ≤
      slabObservableTwoReplicaPairWeight D target := by
  apply weightedColumn_le_of_columnCapacity
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (slabObservableTwoReplicaPairWeight D)
    (SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandThinnedWeight
      D rootFaceId targetFaceId htarget)
    (slabObservablePairedConnectedStrandRealize
      D rootFaceId targetFaceId htarget)
    target
  · exact slabObservableTwoReplicaPairWeight_nonnegative
      D rootFaceId target
  · intro source _ choice heq
    subst target
    exact Q'.eqv_symm
      (slabObservablePairedStrandRecoupledTargetPair_weight_preserved
        D rootFaceId targetFaceId htarget
        source.toRecouplingSource choice)
  · exact slabObservablePairedConnectedStrandThinnedColumn_le_one
      D rootFaceId targetFaceId htarget target

end YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning.slabObservablePairedConnectedStrandSources_nodup
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning.slabObservablePairedStrandDisconnectionMass_le_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning.slabObservablePairedConnectedStrandWeight_pos_of_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning.slabObservablePairedConnectedStrandThinnedColumn_le_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning.slabObservablePairedConnectedStrandRealize_connected
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning.slabObservablePairedConnectedStrandThinnedWeightedColumn_le
