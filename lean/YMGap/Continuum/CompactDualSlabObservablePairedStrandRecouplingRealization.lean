/-
# Realize successful strand-disconnecting recouplings in the target cell

The preceding row keeps precisely those whole-slab SU(2) recoupling columns
whose realized paired strand graph separates the target face from the root.
For each such column, the target-rooted paired-face component is therefore a
legal cross-replica switch mask: it fixes the root, swaps the target, and is
closed across every literal strand edge in both realized assignments.

This module applies the existing accepted paired-face switch to that realized
pair.  The output is a literal member of the opposite `10 x 01` four-cell,
and the complete two-replica Gibbs weight is preserved exactly.  Thus the
posterior row now has a concrete physical realization rather than merely a
success predicate.

No global preimage/column-capacity theorem or positive connected-sector
fraction is proved here.

Constructive contract: explicit accepted assignments and finite dependent
subtypes only; no `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair

namespace YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_attach_local
    {A : Type} (weight : A -> Q') : forall items : List A,
    listQSum (fun item : {item // item ∈ items} => weight item.1)
        items.attach ≈ listQSum weight items
  | items => Q'.eqv_of_eq (listQSum_attach weight items)

private theorem bool_eq_false_of_not_eq_true_local
    (value : Bool) (hvalue : (!value) = true) : value = false := by
  cases value <;> simp_all

/-! ## 1. Successful dependent choices -/

abbrev SlabObservablePairedStrandSuccessfulChoice
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :=
  {choice // choice ∈
    slabObservablePairedStrandSuccessfulRecouplingChoices
      D rootFaceId targetFaceId source}

def slabObservablePairedStrandSuccessfulChoices
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :
    List (SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :=
  (slabObservablePairedStrandSuccessfulRecouplingChoices
    D rootFaceId targetFaceId source).attach

def slabObservablePairedStrandSuccessfulWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) : Q' :=
  slabObservablePairedStrandRecouplingWeight
    D rootFaceId targetFaceId source choice.1

theorem slabObservablePairedStrandSuccessfulWeight_nonnegative
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    (0 : Q') <= slabObservablePairedStrandSuccessfulWeight
      D rootFaceId targetFaceId source choice :=
  slabObservablePairedStrandRecouplingWeight_nonnegative
    D rootFaceId targetFaceId source choice.1

theorem slabObservablePairedStrandSuccessfulWeight_row_mass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId) :
    listQSum
        (slabObservablePairedStrandSuccessfulWeight
          D rootFaceId targetFaceId source)
        (slabObservablePairedStrandSuccessfulChoices
          D rootFaceId targetFaceId source) ≈
      slabObservablePairedStrandDisconnectionMass
        D rootFaceId targetFaceId source := by
  unfold slabObservablePairedStrandSuccessfulChoices
    slabObservablePairedStrandSuccessfulWeight
    slabObservablePairedStrandDisconnectionMass
  exact listQSum_attach_local
    (slabObservablePairedStrandRecouplingWeight
      D rootFaceId targetFaceId source)
    (slabObservablePairedStrandSuccessfulRecouplingChoices
      D rootFaceId targetFaceId source)

theorem SlabObservablePairedStrandSuccessfulChoice.disconnected
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId}
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    slabObservableTwoReplicaPairPairedFaceConnectedB
        D rootFaceId targetFaceId
        (slabObservablePairedStrandRecoupledPair
          D rootFaceId targetFaceId source choice.1) = false := by
  have hsuccess := (List.mem_filter.mp choice.2).2
  unfold slabObservablePairedStrandRecouplingSuccessB at hsuccess
  exact bool_eq_false_of_not_eq_true_local _ hsuccess

/-! ## 2. Accepted component-switched outputs -/

def slabObservablePairedStrandSwitchedLeftEntry
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    SlabObservablePositiveSourceEntry D rootFaceId :=
  let pair := slabObservablePairedStrandRecoupledPair
    D rootFaceId targetFaceId source choice.1
  let hpair := slabObservablePairedStrandRecoupledPair_mem_source
    D rootFaceId targetFaceId source choice.1
  slabObservablePositiveSourceEntryOfCarrier
    D rootFaceId
    (slabObservablePairedFaceSwapLeftPhysical D targetFaceId pair)
    (slabObservablePairedFaceSwapLeftPhysical_mem D targetFaceId pair)
    (slabObservablePairSwitchedLeftAssignment
      D rootFaceId targetFaceId htarget pair hpair)
    (slabObservablePairSwitchedLeftAssignment_mem
      D rootFaceId targetFaceId htarget pair hpair)
    (slabObservablePairedFaceSwapLeftPhysical_root_positive
      D rootFaceId targetFaceId pair choice.disconnected)

def slabObservablePairedStrandSwitchedRightEntry
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    SlabExpandedFineSourceEntry D :=
  let pair := slabObservablePairedStrandRecoupledPair
    D rootFaceId targetFaceId source choice.1
  let hpair := slabObservablePairedStrandRecoupledPair_mem_source
    D rootFaceId targetFaceId source choice.1
  slabExpandedFineSourceEntryOfCarrier
    D (slabObservablePairedFaceSwapRightPhysical D targetFaceId pair)
    (slabObservablePairedFaceSwapRightPhysical_mem D targetFaceId pair)
    (slabObservablePairSwitchedRightAssignment
      D rootFaceId targetFaceId htarget pair hpair)
    (slabObservablePairSwitchedRightAssignment_mem
      D rootFaceId targetFaceId htarget pair hpair)

def slabObservablePairedStrandRecoupledTargetPair
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    SlabObservableTwoReplicaPair D rootFaceId :=
  (slabObservablePairedStrandSwitchedLeftEntry
      D rootFaceId targetFaceId htarget source choice,
    slabObservablePairedStrandSwitchedRightEntry
      D rootFaceId targetFaceId htarget source choice)

theorem slabObservablePairedStrandSwitchedLeftEntry_physical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    (slabObservablePairedStrandSwitchedLeftEntry
      D rootFaceId targetFaceId htarget source choice).1.1 =
      slabObservablePairedFaceSwapLeftPhysical D targetFaceId
        (slabObservablePairedStrandRecoupledPair
          D rootFaceId targetFaceId source choice.1) := by
  unfold slabObservablePairedStrandSwitchedLeftEntry
  apply slabObservablePositiveSourceEntryOfCarrier_physical

theorem slabObservablePairedStrandSwitchedRightEntry_physical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    (slabObservablePairedStrandSwitchedRightEntry
      D rootFaceId targetFaceId htarget source choice).1.1 =
      slabObservablePairedFaceSwapRightPhysical D targetFaceId
        (slabObservablePairedStrandRecoupledPair
          D rootFaceId targetFaceId source choice.1) := by
  unfold slabObservablePairedStrandSwitchedRightEntry
  apply slabExpandedFineSourceEntryOfCarrier_physical

/-! ## 3. Coverage and exact Gibbs-weight preservation -/

theorem slabObservablePairedStrandRecoupledTargetPair_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    slabObservablePairedStrandRecoupledTargetPair
        D rootFaceId targetFaceId htarget source choice ∈
      slabObservableFourCellTargetPairs D rootFaceId targetFaceId := by
  let pair := slabObservablePairedStrandRecoupledPair
    D rootFaceId targetFaceId source choice.1
  let hpair := slabObservablePairedStrandRecoupledPair_mem_source
    D rootFaceId targetFaceId source choice.1
  unfold slabObservablePairedStrandRecoupledTargetPair
  apply faceSwapEntries_mem_fourCellTarget
    D rootFaceId targetFaceId pair hpair
  · exact slabObservablePairedStrandSwitchedLeftEntry_physical
      D rootFaceId targetFaceId htarget source choice
  · exact slabObservablePairedStrandSwitchedRightEntry_physical
      D rootFaceId targetFaceId htarget source choice
  · exact slabObservableTwoReplicaPairPairedFaceSwapMask_root_of_disconnected
      D rootFaceId targetFaceId pair choice.disconnected
  · exact slabObservableTwoReplicaPairPairedFaceSwapMask_target
      D rootFaceId targetFaceId htarget pair hpair

theorem slabObservablePairedStrandRecoupledTargetPair_weight_preserved
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    slabObservableTwoReplicaPairWeight D
        (slabObservablePairedStrandRecoupledTargetPair
          D rootFaceId targetFaceId htarget source choice) ≈
      slabObservableTwoReplicaPairWeight D source.1 := by
  let pair := slabObservablePairedStrandRecoupledPair
    D rootFaceId targetFaceId source choice.1
  unfold slabObservableTwoReplicaPairWeight
    slabObservablePositiveEntryWeight slabExpandedFineEntryWeight
    slabExpandedFineSourceWeight
    slabObservablePairedStrandRecoupledTargetPair
  rw [slabObservablePairedStrandSwitchedLeftEntry_physical,
    slabObservablePairedStrandSwitchedRightEntry_physical]
  have hswap := retainedFineIntertwinerPhysicalFiberWeight_pair_faceSwap
    D (slabObservableTwoReplicaPairPairedFaceSwapMask
      D pair targetFaceId)
    pair.1.1.1 pair.2.1.1 source.1.1.1.2 source.1.2.1.2
    (slabObservablePairedStrandSwitchedLeftEntry
      D rootFaceId targetFaceId htarget source choice).1.2
    (slabObservablePairedStrandSwitchedRightEntry
      D rootFaceId targetFaceId htarget source choice).1.2
  exact Q'.eqv_trans _ _ _ hswap (Q'.eqv_refl _)

end YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization.SlabObservablePairedStrandSuccessfulChoice.disconnected
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization.slabObservablePairedStrandSuccessfulWeight_row_mass
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization.slabObservablePairedStrandRecoupledTargetPair_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization.slabObservablePairedStrandRecoupledTargetPair_weight_preserved
