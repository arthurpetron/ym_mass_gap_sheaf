/-
# The SU(2) recoupling row filtered by strand disconnection

Fix one literal source pair in the observable four-cell.  Keep its two
physical spin fields unchanged and run the complete whole-slab SU(2)
recoupling matrix on its two accepted auxiliary assignments.  Every target
column is realized as a new accepted pair over the same physical fields.

The successful columns are exactly those for which the realized paired
strand graph disconnects the target face from the root.  Their total row
weight is therefore an explicit rational probability made from squared SU(2)
recoupling coefficients.  The paired-face/support refinement proves that
this probability is exactly one whenever the original physical union support
is disconnected.  On support-connected sources the same formula is the
literal posterior fraction whose positivity must be proved by bounded-spin
recoupling mathematics.

No positivity on the connected sector, face-swap realization, shared column
capacity, uniform rate, operator gap, or continuum claim is made here.

Constructive contract: finite exact bistochastic matrices and accepted
carriers only; no `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
import YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
import YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization

namespace YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The complete four-cell source and its physical-only matrix -/

abbrev SlabObservablePairedStrandRecouplingSource
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :=
  {pair // pair ∈ slabObservableFourCellSourcePairs
    D rootFaceId targetFaceId}

def slabObservablePairedStrandRecouplingSources
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :=
  (slabObservableFourCellSourcePairs D rootFaceId targetFaceId).attach

abbrev SlabObservablePairedStrandRecouplingChoice
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :=
  SlabPhysicalPairRecouplingTargetAssignment D.extent
    source.1.1.1.1 source.1.2.1.1

def slabObservablePairedStrandRecouplingChoices
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :
    List (SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) :=
  (slabPhysicalPairRecouplingKernel D.extent
    source.1.1.1.1 source.1.2.1.1).targets

def slabObservablePairedStrandRecouplingWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) : Q' :=
  (slabPhysicalPairRecouplingKernel D.extent
      source.1.1.1.1 source.1.2.1.1).weight
    (slabPhysicalPairRecouplingProductionSource
      D.cutoff D.extent source.1.1.1.1 source.1.2.1.1
      source.1.1.1.2 source.1.2.1.2
      source.1.1.assignment_mem
      (slabExpandedFineSourceEntryAssignment_mem source.1.2))
    choice

theorem slabObservablePairedStrandRecouplingWeight_nonnegative
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) :
    (0 : Q') <= slabObservablePairedStrandRecouplingWeight
      D rootFaceId targetFaceId source choice :=
  (slabPhysicalPairRecouplingKernel D.extent
    source.1.1.1.1 source.1.2.1.1).weight_nonnegative _ _

theorem slabObservablePairedStrandRecouplingWeight_row_normalized
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :
    listQSum
        (slabObservablePairedStrandRecouplingWeight
          D rootFaceId targetFaceId source)
        (slabObservablePairedStrandRecouplingChoices
          D rootFaceId targetFaceId source) ≈ 1 :=
  slabPhysicalPairRecouplingProductionSource_row_normalized
    D.cutoff D.extent source.1.1.1.1 source.1.2.1.1
    source.1.1.1.2 source.1.2.1.2
    source.1.1.assignment_mem
    (slabExpandedFineSourceEntryAssignment_mem source.1.2)

/-! ## 2. Realize every column over the unchanged physical pair -/

def SlabObservablePairedStrandRecouplingSource.anchor
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :
    SlabPhysicalPairCanonicalAnchor D.cutoff D.extent
      source.1.1.1.1 source.1.2.1.1 where
  leftAssignment := source.1.1.1.2
  rightAssignment := source.1.2.1.2
  left_mem := source.1.1.assignment_mem
  right_mem := slabExpandedFineSourceEntryAssignment_mem source.1.2
  leftBounded :=
    YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment.SlabObservablePositiveSourceEntry.physical_bounded
      source.1.1
  rightBounded :=
    YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment.SlabExpandedFineSourceEntry.physical_bounded
      source.1.2

def slabObservablePairedStrandRecoupledAssignments
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) :=
  source.anchor.realize choice

def slabObservablePairedStrandRecoupledPair
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) :
    SlabObservableTwoReplicaPair D rootFaceId :=
  (slabObservablePositiveSourceEntryOfCarrier
      D rootFaceId source.1.1.1.1 source.1.1.physical_mem
      (slabObservablePairedStrandRecoupledAssignments
        D rootFaceId targetFaceId source choice).leftAssignment
      (source.anchor.realize_left_mem choice)
      source.1.1.source_positive,
    slabExpandedFineSourceEntryOfCarrier
      D source.1.2.1.1
      (mem_slabExpandedFineSources_iff.mp source.1.2.2).1
      (slabObservablePairedStrandRecoupledAssignments
        D rootFaceId targetFaceId source choice).rightAssignment
      (source.anchor.realize_right_mem choice))

@[simp] theorem slabObservablePairedStrandRecoupledPair_leftPhysical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) :
    (slabObservablePairedStrandRecoupledPair
      D rootFaceId targetFaceId source choice).1.1.1 =
        source.1.1.1.1 := rfl

@[simp] theorem slabObservablePairedStrandRecoupledPair_rightPhysical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) :
    (slabObservablePairedStrandRecoupledPair
      D rootFaceId targetFaceId source choice).2.1.1 =
        source.1.2.1.1 := rfl

theorem slabObservablePairedStrandRecoupledPair_mem_source
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) :
    slabObservablePairedStrandRecoupledPair
        D rootFaceId targetFaceId source choice ∈
      slabObservableFourCellSourcePairs
        D rootFaceId targetFaceId := by
  have hcells := (mem_cartesian_iff
    (slabObservableRootTargetEntries D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetComplementEntries
      D rootFaceId targetFaceId) source.1).mp source.2
  have hleft := List.mem_filter.mp hcells.1
  have hright := List.mem_filter.mp hcells.2
  apply (mem_cartesian_iff
    (slabObservableRootTargetEntries D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetComplementEntries
      D rootFaceId targetFaceId)
    (slabObservablePairedStrandRecoupledPair
      D rootFaceId targetFaceId source choice)).mpr
  constructor
  · apply List.mem_filter.mpr
    exact ⟨List.mem_attach _ _, hleft.2⟩
  · apply List.mem_filter.mpr
    exact ⟨List.mem_attach _ _, hright.2⟩

/-! ## 3. The exact posterior disconnection probability -/

def slabObservablePairedStrandRecouplingSuccessB
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) : Bool :=
  !(slabObservableTwoReplicaPairPairedFaceConnectedB
    D rootFaceId targetFaceId
      (slabObservablePairedStrandRecoupledPair
        D rootFaceId targetFaceId source choice))

def slabObservablePairedStrandSuccessfulRecouplingChoices
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :
    List (SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) :=
  (slabObservablePairedStrandRecouplingChoices
    D rootFaceId targetFaceId source).filter
      (slabObservablePairedStrandRecouplingSuccessB
        D rootFaceId targetFaceId source)

/-- Exact SU(2) row probability that recoupling separates the paired strand
component while leaving the physical spin fields fixed. -/
def slabObservablePairedStrandDisconnectionMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) : Q' :=
  listQSum
    (slabObservablePairedStrandRecouplingWeight
      D rootFaceId targetFaceId source)
    (slabObservablePairedStrandSuccessfulRecouplingChoices
      D rootFaceId targetFaceId source)

theorem slabObservablePairedStrandDisconnectionMass_nonnegative
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :
    (0 : Q') <= slabObservablePairedStrandDisconnectionMass
      D rootFaceId targetFaceId source := by
  unfold slabObservablePairedStrandDisconnectionMass
  induction slabObservablePairedStrandSuccessfulRecouplingChoices
      D rootFaceId targetFaceId source with
  | nil => exact Q'.le_refl' 0
  | cons head tail ih =>
      exact Q'.zero_le_add _ _
        (slabObservablePairedStrandRecouplingWeight_nonnegative
          D rootFaceId targetFaceId source head) ih

private theorem filter_eq_self_of_true_on_mem
    {A : Type} (test : A -> Bool) :
    forall items : List A,
      (forall item, item ∈ items -> test item = true) ->
      items.filter test = items
  | [], _ => rfl
  | head :: tail, hall => by
      rw [List.filter_cons, hall head List.mem_cons_self]
      exact congrArg (List.cons head)
        (filter_eq_self_of_true_on_mem test tail
          (fun item hitem => hall item (List.mem_cons_of_mem head hitem)))

/-- Support disconnection forces every realized SU(2) recoupling column to
be strand-disconnected. -/
theorem slabObservablePairedStrandRecouplingSuccessB_of_supportDisconnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (hdisconnected :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId source.1 = false)
    (choice : SlabObservablePairedStrandRecouplingChoice
      D rootFaceId targetFaceId source) :
    slabObservablePairedStrandRecouplingSuccessB
      D rootFaceId targetFaceId source choice = true := by
  have hrealizedSupport :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId
          (slabObservablePairedStrandRecoupledPair
            D rootFaceId targetFaceId source choice) = false := by
    simpa only [slabObservableTwoReplicaPairPairedSupportConnectedB,
      slabObservableTwoReplicaPairPairedSupportSwapMask,
      slabObservablePairedStrandRecoupledPair_leftPhysical,
      slabObservablePairedStrandRecoupledPair_rightPhysical] using
        hdisconnected
  have hface :=
    slabObservableTwoReplicaPairPairedFaceDisconnected_of_supportDisconnected
      D rootFaceId targetFaceId htarget
      (slabObservablePairedStrandRecoupledPair
        D rootFaceId targetFaceId source choice)
      (slabObservablePairedStrandRecoupledPair_mem_source
        D rootFaceId targetFaceId source choice)
      hrealizedSupport
  unfold slabObservablePairedStrandRecouplingSuccessB
  rw [hface]
  rfl

/-- On the old support-disconnected sector, the new posterior row has exact
mass one rather than merely a lower bound. -/
theorem slabObservablePairedStrandDisconnectionMass_eqv_one_of_supportDisconnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (hdisconnected :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId source.1 = false) :
    slabObservablePairedStrandDisconnectionMass
      D rootFaceId targetFaceId source ≈ 1 := by
  have hchoices :
      slabObservablePairedStrandSuccessfulRecouplingChoices
          D rootFaceId targetFaceId source =
        slabObservablePairedStrandRecouplingChoices
          D rootFaceId targetFaceId source := by
    unfold slabObservablePairedStrandSuccessfulRecouplingChoices
    apply filter_eq_self_of_true_on_mem
    intro choice _
    exact slabObservablePairedStrandRecouplingSuccessB_of_supportDisconnected
      D rootFaceId targetFaceId htarget source hdisconnected choice
  unfold slabObservablePairedStrandDisconnectionMass
  rw [hchoices]
  exact slabObservablePairedStrandRecouplingWeight_row_normalized
    D rootFaceId targetFaceId source

end YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow.slabObservablePairedStrandRecouplingWeight_row_normalized
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow.slabObservablePairedStrandRecoupledPair_mem_source
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow.slabObservablePairedStrandDisconnectionMass_nonnegative
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow.slabObservablePairedStrandRecouplingSuccessB_of_supportDisconnected
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow.slabObservablePairedStrandDisconnectionMass_eqv_one_of_supportDisconnected
