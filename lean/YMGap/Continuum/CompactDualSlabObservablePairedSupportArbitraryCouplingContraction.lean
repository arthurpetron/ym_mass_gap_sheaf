/-
# Exact paired-support recoupling at arbitrary nonnegative coupling

The physical paired-support recoupling switch, its stochastic rows, and its
column-capacity theorem are already stated for an arbitrary corrected slab.
Only the final mass contraction was specialized to the production anchor,
because it used an anchor-named nonnegativity lemma.

Expanded SU(2) source weights are nonnegative at every nonnegative rational
coupling.  Replacing that last lemma therefore makes the exact disconnected
switch contraction and four-cell defect reduction available for every
`SlabPhysicalData`.  The only remaining term is the literal connected
two-replica support carrier.

This is a signed-covariance reduction, not a decay estimate on that connected
carrier.  It supplies the arbitrary-coupling target that the high-spin /
finite-core analysis must next estimate.

Constructive contract: the existing explicit SU(2) recoupling kernel, finite
dependent pushforward, and rational nonnegativity only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
import YMGap.Continuum.CompactDualSlabObservableHighSpinFiniteCoreRemainder
import YMGap.Continuum.CompactDualSlabObservableBooleanCovariance

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

private theorem divPos_le_divPos_of_le_local
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hle : left <= right) :
    Q'.divPos left denominator hdenominator <=
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hle
    (Q'.le_of_lt (Q'.recipPos_pos denominator hdenominator))

/-! ## 1. Arbitrary-coupling nonnegativity -/

theorem slabExpandedFineEntryWeight_nonnegative
    (D : SlabPhysicalData) (entry : SlabExpandedFineSourceEntry D) :
    (0 : Q') <= slabExpandedFineEntryWeight D entry := by
  unfold slabExpandedFineEntryWeight
  exact slabObservableExpandedFineSourceWeight_nonnegative D entry.1

theorem slabObservablePositiveEntryWeight_nonnegative
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (entry : SlabObservablePositiveSourceEntry D rootFaceId) :
    (0 : Q') <= slabObservablePositiveEntryWeight D entry := by
  unfold slabObservablePositiveEntryWeight
  exact slabObservableExpandedFineSourceWeight_nonnegative D entry.1

theorem slabObservableTwoReplicaPairWeight_nonnegative
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    (0 : Q') <= slabObservableTwoReplicaPairWeight D pair := by
  unfold slabObservableTwoReplicaPairWeight
  exact Q'.mul_nonneg _ _
    (slabObservablePositiveEntryWeight_nonnegative
      D rootFaceId pair.1)
    (slabExpandedFineEntryWeight_nonnegative D pair.2)

/-! ## 2. The disconnected switch for every corrected slab -/

/-- The complete support-disconnected source sector contracts into the
opposite four-cell at every nonnegative coupling. -/
theorem slabObservablePairedSupportSeparatedFourCellSourcePairs_weight_le
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportSeparatedFourCellSourcePairs
          D rootFaceId targetFaceId) <=
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId) := by
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
          (slabObservableTwoReplicaPairWeight_nonnegative
            D rootFaceId target)
          (fun source _ choice heq => by
            rw [heq]
            exact
              slabObservablePairedSupportRecoupledTargetPair_weight_preserved
                D rootFaceId targetFaceId htarget source choice)
          (slabObservablePairedSupportDependentColumnCapacity
            D rootFaceId targetFaceId htarget target))
  simpa only [slabObservablePairedSupportSeparatedSources,
    listQSum_attach] using htransport

/-! ## 3. Exact arbitrary-coupling connected residue -/

/-- The exact source-cell partition and arbitrary-coupling switch leave only
the literal paired-support connected carrier. -/
theorem slabObservableFourCellSourcePairs_weight_le_target_add_pairedSupportConnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) <=
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellTargetPairs
            D rootFaceId targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) := by
  have hpartition :=
    slabObservableFourCellSourcePairs_pairedSupport_partition
      D rootFaceId targetFaceId
  have hseparated :=
    slabObservablePairedSupportSeparatedFourCellSourcePairs_weight_le
      D rootFaceId targetFaceId htarget
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hpartition)
    (Q'.add_le_add hseparated (Q'.le_refl' _))

/-- **Arbitrary-coupling SU(2) four-cell reduction.**  The Boolean covariance
numerator is no larger than the exact connected paired-support residue.  No
uniform estimate on that residue is included in this theorem. -/
theorem slabObservableFourCell_defect_le_pairedSupportConnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetEntries
            D rootFaceId targetFaceId) *
        listQSum (slabExpandedFineEntryWeight D)
          (slabObservableRootComplementTargetComplementEntries
            D rootFaceId targetFaceId) <=
      listQSum (slabObservablePositiveEntryWeight D)
            (slabObservableRootTargetComplementEntries
              D rootFaceId targetFaceId) *
          listQSum (slabExpandedFineEntryWeight D)
            (slabObservableRootComplementTargetEntries
              D rootFaceId targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) := by
  have hsource := slabObservableFourCellSourcePairs_weight_product
    D rootFaceId targetFaceId
  have htargetPair := slabObservableFourCellTargetPairs_weight_product
    D rootFaceId targetFaceId
  have hfour :=
    slabObservableFourCellSourcePairs_weight_le_target_add_pairedSupportConnected
      D rootFaceId targetFaceId htarget
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _ hfour
      (Q'.add_le_add (Q'.le_of_eqv htargetPair) (Q'.le_refl' _)))

/-! ## 4. Normalized covariance target -/

/-- The exact probability mass of the paired-support connected source sector.
The coupling, cutoff, and volume remain explicit through `D`; no uniform bound
on this quantity is asserted. -/
def slabObservableNormalizedPairedSupportConnectedMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  Q'.divPos
    (listQSum (slabObservableTwoReplicaPairWeight D)
      (slabObservablePairedSupportConnectedFourCellSourcePairs
        D rootFaceId targetFaceId))
    (D.physicalPartition * D.physicalPartition)
    (YMGap.Continuum.HKPos.q_mul_pos
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))

/-- The arbitrary-coupling normalized four-cell excess is bounded by the
literal normalized mass of the connected paired-support carrier. -/
theorem slabObservableNormalizedFourCellExcess_le_pairedSupportConnectedMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabObservableNormalizedFourCellExcess
        D rootFaceId targetFaceId <=
      slabObservableNormalizedPairedSupportConnectedMass
        D rootFaceId targetFaceId := by
  have hdenominator :
      (0 : Q') < D.physicalPartition * D.physicalPartition :=
    YMGap.Continuum.HKPos.q_mul_pos
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
  have hdefect :=
    slabObservableFourCell_defect_le_pairedSupportConnected
      D rootFaceId targetFaceId htarget
  have hnumerator :
      listQSum (slabObservablePositiveEntryWeight D)
            (slabObservableRootTargetEntries
              D rootFaceId targetFaceId) *
          listQSum (slabExpandedFineEntryWeight D)
            (slabObservableRootComplementTargetComplementEntries
              D rootFaceId targetFaceId) +
        -(listQSum (slabObservablePositiveEntryWeight D)
              (slabObservableRootTargetComplementEntries
                D rootFaceId targetFaceId) *
            listQSum (slabExpandedFineEntryWeight D)
              (slabObservableRootComplementTargetEntries
                D rootFaceId targetFaceId)) <=
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId) :=
    Q'.sub_le_of_le_add hdefect
  unfold slabObservableNormalizedFourCellExcess
  unfold slabObservableNormalizedPairedSupportConnectedMass
  exact divPos_le_divPos_of_le_local hdenominator hnumerator

/-- **Arbitrary-coupling signed connected reduction.**  The ordinary centered
Boolean face covariance is no larger than the normalized probability mass of
the literal connected two-replica support carrier. -/
theorem slabObservableFaceBooleanCovariance_le_pairedSupportConnectedMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabObservableFaceBooleanCovariance
        D rootFaceId targetFaceId <=
      slabObservableNormalizedPairedSupportConnectedMass
        D rootFaceId targetFaceId := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (slabObservableFaceBooleanCovariance_eqv_normalizedFourCellExcess
        D rootFaceId targetFaceId))
    (slabObservableNormalizedFourCellExcess_le_pairedSupportConnectedMass
      D rootFaceId targetFaceId htarget)

#print axioms slabExpandedFineEntryWeight_nonnegative
#print axioms slabObservablePositiveEntryWeight_nonnegative
#print axioms slabObservableTwoReplicaPairWeight_nonnegative
#print axioms slabObservablePairedSupportSeparatedFourCellSourcePairs_weight_le
#print axioms slabObservableFourCellSourcePairs_weight_le_target_add_pairedSupportConnected
#print axioms slabObservableFourCell_defect_le_pairedSupportConnected
#print axioms slabObservableNormalizedPairedSupportConnectedMass
#print axioms slabObservableNormalizedFourCellExcess_le_pairedSupportConnectedMass
#print axioms slabObservableFaceBooleanCovariance_le_pairedSupportConnectedMass

end YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
