/-
# Fractional SU(2) recoupling switch on the physical four-cell carrier

The deterministic disconnected switch asks one output to remember every
source decomposition.  The complete SU(2) recoupling matrix suggests the
correct finite replacement: distribute each separated source over its
source-dependent right-tree carrier, realize those channels as physical
target pairs, and require only that every target column receive mass at most
one.

This module makes that statement exact.  The local and whole-slab row laws
are already proved; facewise transposition preserves the full two-replica
Gibbs weight at every coupling.  The remaining bridge splits into a physical
right-tree realization and its load-bearing global column-capacity bound.
Conditional on both, finite dependent Fubini proves separated-cell domination
and contracts the anchor four-cell defect to the exact paired-union connected
residue.

No realization certificate is inhabited here.  In particular, no decoder,
column-capacity estimate, beta-uniform gap, or continuum theorem is claimed.

Constructive contract: exact finite carriers and `Q'`, no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteDependentKernelCapacity
import YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct

namespace YMGap.Continuum.SU2SlabRecouplingFractionalSwitch

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabObservableConnectedDecay
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal separated source and its dependent recoupling row -/

/-- Attach membership to every separated source pair. -/
abbrev SlabObservableSeparatedRecouplingSource
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :=
  {pair // pair ∈ slabObservablePairedFaceSeparatedFourCellSourcePairs
    D rootFaceId targetFaceId}

def slabObservableSeparatedRecouplingSources
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId) :=
  (slabObservablePairedFaceSeparatedFourCellSourcePairs
    D rootFaceId targetFaceId).attach

theorem SlabObservableSeparatedRecouplingSource.pair_mem_fourCell
    {D : SlabPhysicalData} {rootFaceId : Nat}
    {targetFaceId : Nat}
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId) :
    source.1 ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId :=
  (List.mem_filter.mp source.2).1

/-- The complete whole-slab right-tree target carrier available from one
separated physical source. -/
abbrev SlabObservableSeparatedRecouplingChoice
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId) :=
  SlabObservablePairCrossedBistochasticTargetAssignment
    D rootFaceId targetFaceId htarget source.1
      source.pair_mem_fourCell

def slabObservableSeparatedRecouplingChoices
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId) :
    List (SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source) :=
  (slabObservablePairCrossedBistochasticKernel
    D rootFaceId targetFaceId htarget source.1
      source.pair_mem_fourCell).targets

def slabObservableSeparatedRecouplingWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source) : Q' :=
  (slabObservablePairCrossedBistochasticKernel
    D rootFaceId targetFaceId htarget source.1
      source.pair_mem_fourCell).weight
    (slabObservablePairCrossedBistochasticProductionSource
      D rootFaceId targetFaceId htarget source.1
        source.pair_mem_fourCell)
    choice

theorem slabObservableSeparatedRecouplingWeight_nonnegative
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source) :
    (0 : Q') ≤ slabObservableSeparatedRecouplingWeight
      D rootFaceId targetFaceId htarget source choice :=
  (slabObservablePairCrossedBistochasticKernel
    D rootFaceId targetFaceId htarget source.1
      source.pair_mem_fourCell).weight_nonnegative _ _

theorem slabObservableSeparatedRecouplingWeight_row_normalized
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId) :
    listQSum
        (slabObservableSeparatedRecouplingWeight
          D rootFaceId targetFaceId htarget source)
        (slabObservableSeparatedRecouplingChoices
          D rootFaceId targetFaceId htarget source) ≈ 1 :=
  slabObservablePairCrossedBistochasticProductionSource_row_normalized
    D rootFaceId targetFaceId htarget source.1
      source.pair_mem_fourCell

/-! ## 2. Constructive equality on the common physical target type -/

private def slabObservableTwoReplicaPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  fun left right =>
    if hleft :
        slabExpandedFineTargetKey D left.1.1.1 left.1.1.2 =
          slabExpandedFineTargetKey D right.1.1.1 right.1.1.2 then
      if hright :
          slabExpandedFineTargetKey D left.2.1.1 left.2.1.2 =
            slabExpandedFineTargetKey D right.2.1.1 right.2.1.2 then
        isTrue (Prod.ext
          (Subtype.ext (slabExpandedFineTargetKey_eq_source_eq D
            left.1.source_mem_expanded right.1.source_mem_expanded hleft))
          (Subtype.ext (slabExpandedFineTargetKey_eq_source_eq D
            left.2.2 right.2.2 hright)))
      else
        isFalse (fun heq => hright (by rw [heq]))
    else
      isFalse (fun heq => hleft (by rw [heq]))

local instance (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

/-! ## 3. The exact remaining realization-and-capacity certificate -/

theorem SlabObservableSeparatedRecouplingSource.pairedFace_disconnected
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId) :
    slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId source.1 = false := by
  have hseparated := (List.mem_filter.mp source.2).2
  cases hconnected : slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId source.1 with
  | false => rfl
  | true =>
      simp only [hconnected, Bool.not_true, Bool.false_eq_true] at hseparated

/-- **OPEN same-carrier SU(2) realization.**  Realize every dependent
right-tree recoupling choice as an actual accepted physical target pair.  The
physical projection must be the canonical paired-component face
transposition.  The row law and Gibbs-weight preservation are derived; target
membership remains explicit because it includes accepted witness data. -/
structure SlabObservableRecouplingTargetRealization
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) : Type where
  realize : (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId) →
    SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source →
    SlabObservableTwoReplicaPair D rootFaceId
  realize_left_physical : ∀ source choice,
    (realize source choice).1.1.1 =
      twoReplicaFaceSwapLeft
        (slabObservableTwoReplicaPairPairedFaceSwapMask
          D source.1 targetFaceId)
        source.1.1.1.1 source.1.2.1.1
  realize_right_physical : ∀ source choice,
    (realize source choice).2.1.1 =
      twoReplicaFaceSwapRight
        (slabObservableTwoReplicaPairPairedFaceSwapMask
          D source.1 targetFaceId)
        source.1.1.1.1 source.1.2.1.1
  realize_mem_target : ∀ source choice,
    realize source choice ∈
      slabObservableFourCellTargetPairs D rootFaceId targetFaceId

/-- The source-dependent whole-slab recoupling row after a concrete
realization on the common physical target carrier. -/
def slabObservableRecouplingPushedWeight
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (realization : SlabObservableRecouplingTargetRealization
      D rootFaceId targetFaceId htarget)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId)
    (target : SlabObservableTwoReplicaPair D rootFaceId) : Q' :=
  dependentKernelPushforwardWeight
    (SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget)
    (slabObservableSeparatedRecouplingChoices
      D rootFaceId targetFaceId htarget)
    (slabObservableSeparatedRecouplingWeight
      D rootFaceId targetFaceId htarget)
    realization.realize source target

/-- Total unweighted recoupling load entering one realized physical target. -/
def slabObservableRecouplingColumnMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (realization : SlabObservableRecouplingTargetRealization
      D rootFaceId targetFaceId htarget)
    (target : SlabObservableTwoReplicaPair D rootFaceId) : Q' :=
  listQSum
    (fun source => slabObservableRecouplingPushedWeight
      realization source target)
    (slabObservableSeparatedRecouplingSources
      D rootFaceId targetFaceId)

/-- **OPEN no-overload theorem for a concrete realization.**  This is the
single global collision estimate left after the right-tree channels have been
interpreted on the physical target carrier. -/
structure SlabObservableRecouplingColumnCapacity
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (realization : SlabObservableRecouplingTargetRealization
      D rootFaceId targetFaceId htarget) : Type where
  column_capacity : ∀ target,
    target ∈ slabObservableFourCellTargetPairs
        D rootFaceId targetFaceId →
      slabObservableRecouplingColumnMass realization target ≤ 1

/-- Full physical two-replica Gibbs weight is automatic: the realization
only transposes the two face labels, and every retained intertwiner carries
one counting unit.  The equality is valid at the datum's explicit coupling. -/
theorem SlabObservableRecouplingTargetRealization.weight_preserved
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (certificate : SlabObservableRecouplingTargetRealization
      D rootFaceId targetFaceId htarget)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source) :
    slabObservableTwoReplicaPairWeight D source.1 ≈
      slabObservableTwoReplicaPairWeight D
        (certificate.realize source choice) := by
  unfold slabObservableTwoReplicaPairWeight
    slabObservablePositiveEntryWeight slabExpandedFineEntryWeight
    slabExpandedFineSourceWeight
  rw [certificate.realize_left_physical source choice,
    certificate.realize_right_physical source choice]
  exact Q'.eqv_symm
    (retainedFineIntertwinerPhysicalFiberWeight_pair_faceSwap
      D (slabObservableTwoReplicaPairPairedFaceSwapMask
        D source.1 targetFaceId)
      source.1.1.1.1 source.1.2.1.1
      source.1.1.1.2 source.1.2.1.2
      (certificate.realize source choice).1.1.2
      (certificate.realize source choice).2.1.2)

/-! ## 4. Column capacity contracts the paired-face separated cell -/

/-- The complete SU(2) row laws and one physical column-capacity certificate
replace the old deterministic decoder/injectivity requirement. -/
theorem slabObservablePairedFaceSeparatedFourCellSourcePairs_weight_le
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half))
    (realization : SlabObservableRecouplingTargetRealization
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId htarget)
    (capacity : SlabObservableRecouplingColumnCapacity realization) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedFaceSeparatedFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId) := by
  let D := anchorSlabPhysicalData cutoff half
  have htransport :=
    sourceWeight_total_le_of_dependentKernelCapacity
      (sources := slabObservableSeparatedRecouplingSources
        D rootFaceId targetFaceId)
      (sourceWeight := fun source =>
        slabObservableTwoReplicaPairWeight D source.1)
      (targets := slabObservableFourCellTargetPairs
        D rootFaceId targetFaceId)
      (targetWeight := slabObservableTwoReplicaPairWeight D)
      (Choice := SlabObservableSeparatedRecouplingChoice
        D rootFaceId targetFaceId htarget)
      (choices := slabObservableSeparatedRecouplingChoices
        D rootFaceId targetFaceId htarget)
      (localWeight := slabObservableSeparatedRecouplingWeight
        D rootFaceId targetFaceId htarget)
      (realize := realization.realize)
      (slabObservableFourCellTargetPairs_nodup
        D rootFaceId targetFaceId)
      (fun source _ choice _ =>
        realization.realize_mem_target source choice)
      (fun source _ =>
        slabObservableSeparatedRecouplingWeight_row_normalized
          D rootFaceId targetFaceId htarget source)
      (fun target htargetMem =>
        weightedColumn_le_of_columnCapacity
          (slabObservableSeparatedRecouplingSources
            D rootFaceId targetFaceId)
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          (slabObservableTwoReplicaPairWeight D)
          (SlabObservableSeparatedRecouplingChoice
            D rootFaceId targetFaceId htarget)
          (slabObservableSeparatedRecouplingChoices
            D rootFaceId targetFaceId htarget)
          (slabObservableSeparatedRecouplingWeight
            D rootFaceId targetFaceId htarget)
          realization.realize target
          (slabObservableTwoReplicaPairWeight_anchor_nonnegative
            cutoff half rootFaceId target)
          (fun source _ choice heq => by
            rw [heq]
            exact realization.weight_preserved source choice)
          (capacity.column_capacity target htargetMem))
  simpa only [slabObservableSeparatedRecouplingSources,
    listQSum_attach] using htransport

/-- Once the fractional recoupling realization has column capacity, the
complete source determinant cell is bounded by the opposite cell plus exactly
the paired-union connected residue. -/
theorem slabObservableFourCellSourcePairs_weight_le_target_add_pairedConnected
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half))
    (realization : SlabObservableRecouplingTargetRealization
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId htarget)
    (capacity : SlabObservableRecouplingColumnCapacity realization) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellTargetPairs
            D rootFaceId targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedFaceConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) := by
  let D := anchorSlabPhysicalData cutoff half
  have hpartition :=
    slabObservableFourCellSourcePairs_pairedFace_partition
      D rootFaceId targetFaceId
  have hseparated :=
    slabObservablePairedFaceSeparatedFourCellSourcePairs_weight_le
      cutoff half rootFaceId targetFaceId htarget realization capacity
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hpartition)
    (Q'.add_le_add hseparated (Q'.le_refl' _))

/-- **Exact finite recoupling contraction.**  The Boolean two-face defect is
bounded by the literal paired-union connected residue.  No numerical rate is
inserted: bounding this exact residue is the next analytic frontier. -/
theorem slabObservableFourCell_defect_le_pairedConnected_of_recoupling
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half))
    (realization : SlabObservableRecouplingTargetRealization
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId htarget)
    (capacity : SlabObservableRecouplingColumnCapacity realization) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetEntries
            D rootFaceId targetFaceId) *
        listQSum (slabExpandedFineEntryWeight D)
          (slabObservableRootComplementTargetComplementEntries
            D rootFaceId targetFaceId) ≤
      listQSum (slabObservablePositiveEntryWeight D)
            (slabObservableRootTargetComplementEntries
              D rootFaceId targetFaceId) *
          listQSum (slabExpandedFineEntryWeight D)
            (slabObservableRootComplementTargetEntries
              D rootFaceId targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedFaceConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) := by
  let D := anchorSlabPhysicalData cutoff half
  have hsource := slabObservableFourCellSourcePairs_weight_product
    D rootFaceId targetFaceId
  have htargetPair := slabObservableFourCellTargetPairs_weight_product
    D rootFaceId targetFaceId
  have hfour :=
    slabObservableFourCellSourcePairs_weight_le_target_add_pairedConnected
      cutoff half rootFaceId targetFaceId htarget realization capacity
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _ hfour
      (Q'.add_le_add (Q'.le_of_eqv htargetPair) (Q'.le_refl' _)))

end YMGap.Continuum.SU2SlabRecouplingFractionalSwitch

#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.slabObservableSeparatedRecouplingSources
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.SlabObservableSeparatedRecouplingSource.pair_mem_fourCell
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.slabObservableSeparatedRecouplingChoices
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.slabObservableSeparatedRecouplingWeight
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.slabObservableSeparatedRecouplingWeight_nonnegative
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.slabObservableSeparatedRecouplingWeight_row_normalized
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.SlabObservableSeparatedRecouplingSource.pairedFace_disconnected
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.SlabObservableRecouplingTargetRealization
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.SlabObservableRecouplingColumnCapacity
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.SlabObservableRecouplingTargetRealization.weight_preserved
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.slabObservablePairedFaceSeparatedFourCellSourcePairs_weight_le
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.slabObservableFourCellSourcePairs_weight_le_target_add_pairedConnected
#print axioms YMGap.Continuum.SU2SlabRecouplingFractionalSwitch.slabObservableFourCell_defect_le_pairedConnected_of_recoupling
