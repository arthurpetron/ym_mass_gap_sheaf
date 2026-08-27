/-
# Weighted contraction from paired-support column capacity

The physical paired-support recoupling kernel is already row normalized and
has global unweighted column capacity one.  Its realized target pair differs
from the source pair only by a facewise transposition of the two physical
replicas, so the complete Gibbs weight is preserved exactly.  Finite
dependent-kernel transport therefore sends the whole support-disconnected
source sector into the opposite four-cell with no increase of mass.

Partitioning the complete source four-cell leaves one literal
support-connected residue.  This module records the resulting exact defect
inequality.  No numerical estimate on that residue, beta-to-spacing relation,
thermodynamic limit, or continuum claim is made here.

Constructive contract: exact finite carriers and `Q'`; no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservableConnectedDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact Gibbs-weight preservation -/

/-- Realizing an abstract recoupling column preserves the complete
two-replica Gibbs weight.  Only the two physical fields enter the weight;
the retained auxiliary assignments each carry one counting unit. -/
theorem slabObservablePairedSupportRecoupledTargetPair_weight_preserved
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    slabObservableTwoReplicaPairWeight D source.1 ≈
      slabObservableTwoReplicaPairWeight D
        (slabObservablePairedSupportRecoupledTargetPair
          D rootFaceId targetFaceId htarget source choice) := by
  unfold slabObservableTwoReplicaPairWeight
    slabObservablePositiveEntryWeight slabExpandedFineEntryWeight
    slabExpandedFineSourceWeight
  unfold slabObservablePairedSupportRecoupledTargetPair
  rw [slabObservablePairedSupportRecoupledLeftEntry_physical
      D rootFaceId targetFaceId htarget source choice,
    slabObservablePairedSupportRecoupledRightEntry_physical
      D rootFaceId targetFaceId htarget source choice]
  exact Q'.eqv_symm
    (retainedFineIntertwinerPhysicalFiberWeight_pair_faceSwap
      D (slabObservableTwoReplicaPairPairedSupportSwapMask
        D source.1 targetFaceId)
      source.1.1.1.1 source.1.2.1.1
      source.1.1.1.2 source.1.2.1.2
      (slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget source choice).1.1.2
      (slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget source choice).2.1.2)

/-! ## 2. The support-disconnected sector contracts -/

/-- The complete support-disconnected source sector is transported into the
opposite four-cell with no increase of physical weight. -/
theorem slabObservablePairedSupportSeparatedFourCellSourcePairs_weight_le
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half)) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportSeparatedFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId) := by
  let D := anchorSlabPhysicalData cutoff half
  letI := slabObservableTwoReplicaPairDecidableEq D rootFaceId
  have htransport :=
    sourceWeight_total_le_of_dependentKernelCapacity
      (sources := slabObservablePairedSupportSeparatedSources
        D rootFaceId targetFaceId)
      (sourceWeight := fun source =>
        slabObservableTwoReplicaPairWeight D source.1)
      (targets := slabObservableFourCellTargetPairs
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
      (slabObservableFourCellTargetPairs_nodup
        D rootFaceId targetFaceId)
      (fun source _ choice _ =>
        slabObservablePairedSupportRecoupledTargetPair_mem
          D rootFaceId targetFaceId htarget source choice)
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
          (slabObservableTwoReplicaPairWeight_anchor_nonnegative
            cutoff half rootFaceId target)
          (fun source _ choice heq => by
            rw [heq]
            exact slabObservablePairedSupportRecoupledTargetPair_weight_preserved
              D rootFaceId targetFaceId htarget source choice)
          (slabObservablePairedSupportDependentColumnCapacity
            D rootFaceId targetFaceId htarget target))
  simpa only [slabObservablePairedSupportSeparatedSources,
    listQSum_attach] using htransport

/-! ## 3. The exact support-connected residue -/

/-- The literal obstruction left inside the source four-cell: root and target
belong to one connected component of the union of the two physical replica
supports. -/
def slabObservablePairedSupportConnectedFourCellSourcePairs
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  (slabObservableFourCellSourcePairs D rootFaceId targetFaceId).filter
    fun pair => slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId pair

/-- The source four-cell is the exact disjoint weighted sum of its
support-disconnected contractible sector and support-connected residue. -/
theorem slabObservableFourCellSourcePairs_pairedSupport_partition
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs D rootFaceId targetFaceId) ≈
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportSeparatedFourCellSourcePairs
            D rootFaceId targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) := by
  have hpartition := listQSum_filter_partition
    (slabObservableTwoReplicaPairWeight D)
    (fun pair : SlabObservableTwoReplicaPair D rootFaceId =>
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId pair)
    (slabObservableFourCellSourcePairs D rootFaceId targetFaceId)
  exact Q'.eqv_trans _ _ _ hpartition (Q'.add_comm_eqv _ _)

/-- After the exact fractional recoupling, the complete source determinant
cell is bounded by the opposite cell plus only the support-connected
physical residue. -/
theorem slabObservableFourCellSourcePairs_weight_le_target_add_pairedSupportConnected
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half)) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellTargetPairs
            D rootFaceId targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) := by
  let D := anchorSlabPhysicalData cutoff half
  have hpartition :=
    slabObservableFourCellSourcePairs_pairedSupport_partition
      D rootFaceId targetFaceId
  have hseparated :=
    slabObservablePairedSupportSeparatedFourCellSourcePairs_weight_le
      cutoff half rootFaceId targetFaceId htarget
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hpartition)
    (Q'.add_le_add hseparated (Q'.le_refl' _))

/-! ## 4. Exact finite four-cell defect contraction -/

/-- **Unconditional exact finite recoupling contraction.**  The Boolean
two-face defect is bounded by the literal paired-support connected residue.
The next analytic frontier is to estimate this residue by a strict
cutoff-uniform fraction of the relevant normalizing mass. -/
theorem slabObservableFourCell_defect_le_pairedSupportConnected
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half)) :
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
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) := by
  let D := anchorSlabPhysicalData cutoff half
  have hsource := slabObservableFourCellSourcePairs_weight_product
    D rootFaceId targetFaceId
  have htargetPair := slabObservableFourCellTargetPairs_weight_product
    D rootFaceId targetFaceId
  have hfour :=
    slabObservableFourCellSourcePairs_weight_le_target_add_pairedSupportConnected
      cutoff half rootFaceId targetFaceId htarget
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _ hfour
      (Q'.add_le_add (Q'.le_of_eqv htargetPair) (Q'.le_refl' _)))

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction.slabObservablePairedSupportRecoupledTargetPair_weight_preserved
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction.slabObservablePairedSupportSeparatedFourCellSourcePairs_weight_le
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction.slabObservableFourCellSourcePairs_pairedSupport_partition
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction.slabObservableFourCellSourcePairs_weight_le_target_add_pairedSupportConnected
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction.slabObservableFourCell_defect_le_pairedSupportConnected
