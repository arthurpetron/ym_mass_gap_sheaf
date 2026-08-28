/-
# A successful locally positive slab target constructs the positive channel

The connected-channel frontier has two logically independent inputs.  First,
a whole-slab recoupling target must disconnect the marked root and target
strands.  Second, every local SU(2) matrix coordinate selected by that target
must have positive weight.  This module records exactly those two inputs on
the raw, unfiltered target carrier.

The finite product theorem turns local positivity into positive global row
weight.  The successful target then belongs to the existing positive-filtered
connected row, constructing the positive-channel witness consumed by the
retained-fraction and physical Osterwalder--Schrader contraction theorems.

This is a genuine factorization of the open construction: geometry supplies
`success`, representation theory supplies `coordinatewise_positive`, and no
aggregate posterior positivity is assumed.

Constructive contract: dependent finite products, Boolean membership, and
exact `Q'` positivity only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.  The
dependent target carrier is elaborated with a bounded one-million-heartbeat
allowance.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
import YMGap.Continuum.FiniteBistochasticQKernelProductPositivity

set_option maxHeartbeats 1000000

namespace YMGap.Continuum.CompactDualSlabObservablePairedLocalPositiveChannel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The raw target and its local positivity map -/

abbrev SlabObservablePairedConnectedRawRecouplingChoice
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :=
  SlabObservablePairedStrandRecouplingChoice
    D rootFaceId targetFaceId source.toRecouplingSource

abbrev SlabObservablePairedConnectedRecouplingPackages
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :=
  slabPhysicalPairRecouplingPackages D.extent
    source.1.1.1.1 source.1.2.1.1

def slabObservablePairedConnectedProductionSource
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    FiniteBistochasticSourceAssignment
      (SlabObservablePairedConnectedRecouplingPackages
        D rootFaceId targetFaceId source) :=
  slabPhysicalPairRecouplingProductionSource
    D.cutoff D.extent source.1.1.1.1 source.1.2.1.1
    source.1.1.1.2 source.1.2.1.2
    source.1.1.assignment_mem
    (slabExpandedFineSourceEntryAssignment_mem source.1.2)

/-- Keep the expanded dependent-product proposition opaque at certificate
boundaries.  This prevents record projection generation from normalizing the
entire valence-sensitive slab package list. -/
def SlabObservablePairedConnectedChoiceLocallyPositive
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedConnectedRawRecouplingChoice
      D rootFaceId targetFaceId source) : Prop :=
  FiniteBistochasticCoordinatewisePositive
    (slabObservablePairedConnectedProductionSource
      D rootFaceId targetFaceId source)
    choice

/-- One raw complete target column above a fixed connected source, with its
geometric success and local SU(2) positivity as separate proof fields. -/
inductive SlabObservablePairedConnectedLocalPositiveTarget
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) : Type where
  | mk
      (choice : SlabObservablePairedConnectedRawRecouplingChoice
        D rootFaceId targetFaceId source)
      (choice_mem : choice ∈ slabObservablePairedStrandRecouplingChoices
        D rootFaceId targetFaceId source.toRecouplingSource)
      (success : slabObservablePairedStrandRecouplingSuccessB
        D rootFaceId targetFaceId source.toRecouplingSource choice = true)
      (locally_positive :
        SlabObservablePairedConnectedChoiceLocallyPositive
          D rootFaceId targetFaceId source choice)

/-- One connected source equipped with one successful locally positive raw
target column. -/
inductive SlabObservablePairedConnectedLocalPositiveChannel
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Type where
  | mk
      (source : SlabObservablePairedConnectedStrandSource
        D rootFaceId targetFaceId)
      (target : SlabObservablePairedConnectedLocalPositiveTarget
        D rootFaceId targetFaceId source)

/-! ## 2. Local positivity constructs the existing filtered witness -/

def SlabObservablePairedConnectedLocalPositiveChannel.weight
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (certificate : SlabObservablePairedConnectedLocalPositiveChannel
      D rootFaceId targetFaceId) : Q' := by
  cases certificate with
  | mk source target =>
    cases target with
    | mk choice _ _ _ =>
      exact slabObservablePairedStrandRecouplingWeight
        D rootFaceId targetFaceId source.toRecouplingSource choice

theorem SlabObservablePairedConnectedLocalPositiveChannel.weight_pos
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (certificate : SlabObservablePairedConnectedLocalPositiveChannel
      D rootFaceId targetFaceId) :
    (0 : Q') < certificate.weight := by
  cases certificate with
  | mk source target =>
    cases target with
    | mk choice _ _ locally_positive =>
      unfold SlabObservablePairedConnectedLocalPositiveChannel.weight
        slabObservablePairedStrandRecouplingWeight
        slabPhysicalPairRecouplingKernel
      exact finiteBistochasticProductWeight_pos_of_coordinatewise
        (slabObservablePairedConnectedProductionSource
          D rootFaceId targetFaceId source)
        choice locally_positive

/-- A successful raw column with positive local entries is exactly the
positive connected channel required by the retained-mass theorem. -/
def SlabObservablePairedConnectedLocalPositiveChannel.toPositiveChannelWitness
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (certificate : SlabObservablePairedConnectedLocalPositiveChannel
      D rootFaceId targetFaceId) :
    SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId := by
  cases certificate with
  | mk source target =>
    cases target with
    | mk choice choice_mem success locally_positive =>
      let successful : SlabObservablePairedStrandSuccessfulChoice
          D rootFaceId targetFaceId source.toRecouplingSource :=
        ⟨choice, List.mem_filter.mpr ⟨choice_mem, success⟩⟩
      exact
        { source := source
          choice := successful
          choice_mem := by
            unfold slabObservablePairedConnectedStrandChoices
            apply List.mem_filter.mpr
            refine ⟨List.mem_attach _ successful, ?_⟩
            exact decide_eq_true (by
              simpa only [slabObservablePairedConnectedStrandWeight,
                slabObservablePairedStrandSuccessfulWeight, successful,
                SlabObservablePairedConnectedLocalPositiveChannel.weight]
                using
                  (SlabObservablePairedConnectedLocalPositiveChannel.weight_pos
                    (.mk source (.mk choice choice_mem success
                      locally_positive)))) }

/-! ## 3. Immediate physical consequences -/

/-- The local certificate feeds the already-verified retained-fraction
contraction, producing an explicit finite strict factor. -/
def slabObservablePairedSplitRetainedContraction_of_localPositiveChannel
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (certificate : SlabObservablePairedConnectedLocalPositiveChannel
      D rootFaceId targetFaceId) :
    SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId :=
  slabObservablePairedSplitRetainedContraction
    D hcoupling rootFaceId targetFaceId htarget
      certificate.toPositiveChannelWitness

end YMGap.Continuum.CompactDualSlabObservablePairedLocalPositiveChannel

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedLocalPositiveChannel.SlabObservablePairedConnectedLocalPositiveChannel.weight_pos
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedLocalPositiveChannel.SlabObservablePairedConnectedLocalPositiveChannel.toPositiveChannelWitness
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedLocalPositiveChannel.slabObservablePairedSplitRetainedContraction_of_localPositiveChannel
