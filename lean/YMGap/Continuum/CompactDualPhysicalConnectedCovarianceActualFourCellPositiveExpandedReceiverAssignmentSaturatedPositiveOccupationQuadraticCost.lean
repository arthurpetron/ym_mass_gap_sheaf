/-
# Reduce assignment-saturated unreachable mass to one-face occupation

The assignment-saturated covariance compiler asks for quadratic control of
the physical mass whose endpoint pair is absent from every positive
raw-supported path.  This module removes that two-replica endpoint estimate
as an independent analytic input.

Both four-cell receiver carriers are literal sublists of

  root-positive first replica x arbitrary expanded second replica.

Consequently their combined mass, and hence the unreachable submass, is at
most twice the root-positive one-face mass times the physical partition.  On
the matched AF chart, a one-face estimate

  positive root mass <= c * g^2 * Z_coarse

therefore supplies the old unreachable-mass field with coefficient `c + c`.
The covered-calibration, spacing, and raw-mismatch inputs remain unchanged.

No one-face occupation estimate is inhabited here.  This is a finite exact
reduction, not an arbitrary-cutoff contraction, continuum construction,
OS/GNS reconstruction, Hamiltonian gap, or Yang--Mills mass gap.

Constructive contract: exact rational finite sums and inequalities only; no
choice, `Classical`, `native_decide`, proof hole, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedMatchedAFQuadraticCost
import YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
import YMGap.Continuum.FiniteDependentKernelFirstSourceThinning

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPositiveOccupationQuadraticCost

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedMatchedAFQuadraticCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedMatchedAFQuadraticCost.MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedNormalizedVariation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateCoverageDeficit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Int.add_mul,
               Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

local instance positiveOccupationPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

private theorem sourcePair_mem_positiveTimesAll
    (D : SlabPhysicalData) (root target : Nat)
    (pair : SlabObservableTwoReplicaPair D root)
    (hpair : pair ∈ slabObservableFourCellSourcePairs D root target) :
    pair ∈ slabObservablePositiveTimesAllPairs D root := by
  have hsource :=
    (mem_cartesian_iff
      (slabObservableRootTargetEntries D root target)
      (slabObservableRootComplementTargetComplementEntries
        D root target) pair).mp hpair
  apply (mem_cartesian_iff
    (slabObservablePositiveSourceEntries D root)
    (slabExpandedFineSourceEntries D) pair).mpr
  exact ⟨(List.mem_filter.mp hsource.1).1,
    (List.mem_filter.mp hsource.2).1⟩

private theorem targetPair_mem_positiveTimesAll
    (D : SlabPhysicalData) (root target : Nat)
    (pair : SlabObservableTwoReplicaPair D root)
    (hpair : pair ∈ slabObservableFourCellTargetPairs D root target) :
    pair ∈ slabObservablePositiveTimesAllPairs D root := by
  have htarget :=
    (mem_cartesian_iff
      (slabObservableRootTargetComplementEntries D root target)
      (slabObservableRootComplementTargetEntries D root target)
      pair).mp hpair
  apply (mem_cartesian_iff
    (slabObservablePositiveSourceEntries D root)
    (slabExpandedFineSourceEntries D) pair).mpr
  exact ⟨(List.mem_filter.mp htarget.1).1,
    (List.mem_filter.mp htarget.2).1⟩

/-! ## 1. Both four-cell carriers cost one positive marginal -/

/-- The full source determinant cell is bounded by the root-positive
one-face mass times the complete physical partition. -/
theorem slabObservableFourCellSourcePairs_weight_le_positiveSourceProduct
    (D : SlabPhysicalData) (root target : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs D root target) ≤
      slabObservablePositiveSourceWeight D root *
        D.physicalPartition := by
  have hsub :
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellSourcePairs D root target) ≤
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePositiveTimesAllPairs D root) := by
    apply listQSum_le_of_injective
      (slabObservableFourCellSourcePairs D root target)
      (slabObservablePositiveTimesAllPairs D root)
      (slabObservableTwoReplicaPairWeight D)
      (slabObservableTwoReplicaPairWeight D)
      (fun pair => pair)
      (slabObservableFourCellSourcePairs_nodup D root target)
    · intro pair hpair
      exact sourcePair_mem_positiveTimesAll D root target pair hpair
    · intro first _ second _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact slabObservableTwoReplicaPairWeight_nonnegative D root pair
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_of_eqv
      (slabObservablePositiveTimesAllPairs_weight_eqv D root))

/-- The opposite target determinant cell obeys the same one-face bound. -/
theorem slabObservableFourCellTargetPairs_weight_le_positiveSourceProduct
    (D : SlabPhysicalData) (root target : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs D root target) ≤
      slabObservablePositiveSourceWeight D root *
        D.physicalPartition := by
  have hsub :
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellTargetPairs D root target) ≤
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePositiveTimesAllPairs D root) := by
    apply listQSum_le_of_injective
      (slabObservableFourCellTargetPairs D root target)
      (slabObservablePositiveTimesAllPairs D root)
      (slabObservableTwoReplicaPairWeight D)
      (slabObservableTwoReplicaPairWeight D)
      (fun pair => pair)
      (slabObservableFourCellTargetPairs_nodup D root target)
    · intro pair hpair
      exact targetPair_mem_positiveTimesAll D root target pair hpair
    · intro first _ second _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact slabObservableTwoReplicaPairWeight_nonnegative D root pair
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_of_eqv
      (slabObservablePositiveTimesAllPairs_weight_eqv D root))

/-- The complete source-plus-target receiver carrier costs at most two
copies of the same root-positive marginal product. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_le_twice_positiveSourceProduct
    (S : SlabScalePair) (root target : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
        S root target ≤
      slabObservablePositiveSourceWeight S.coarse root *
          S.coarse.physicalPartition +
        slabObservablePositiveSourceWeight S.coarse root *
          S.coarse.physicalPartition := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
  exact Q'.add_le_add
    (slabObservableFourCellSourcePairs_weight_le_positiveSourceProduct
      S.coarse root target)
    (slabObservableFourCellTargetPairs_weight_le_positiveSourceProduct
      S.coarse root target)

/-! ## 2. Unreachable endpoints are a submass of the same carrier -/

/-- Assignment-saturated unreachable endpoint mass is no larger than the
complete two-cell receiver mass. -/
theorem actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_fullReceiverCellMass
    (S : SlabScalePair) (root target : Nat) :
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
        S root target ≤
      actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
        S root target := by
  have hsource :=
    listQSum_filter_le_of_nonnegative
      (slabObservableTwoReplicaPairWeight S.coarse)
      (fun receiver : SlabObservableTwoReplicaPair S.coarse root =>
        !(decide
          (receiver ∈
            positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
              S root target)))
      (fun pair =>
        slabObservableTwoReplicaPairWeight_nonnegative
          S.coarse root pair)
      (slabObservableFourCellSourcePairs S.coarse root target)
  have htarget :=
    listQSum_filter_le_of_nonnegative
      (slabObservableTwoReplicaPairWeight S.coarse)
      (fun receiver : SlabObservableTwoReplicaPair S.coarse root =>
        !(decide
          (receiver ∈
            positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
              S root target)))
      (fun pair =>
        slabObservableTwoReplicaPairWeight_nonnegative
          S.coarse root pair)
      (slabObservableFourCellTargetPairs S.coarse root target)
  unfold actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
    actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass
    actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass
    actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
  exact Q'.add_le_add hsource htarget

/-- The desired endpoint remainder is controlled by two copies of a single
one-face occupation mass. -/
theorem actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_twice_positiveSourceProduct
    (S : SlabScalePair) (root target : Nat) :
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
        S root target ≤
      slabObservablePositiveSourceWeight S.coarse root *
          S.coarse.physicalPartition +
        slabObservablePositiveSourceWeight S.coarse root *
          S.coarse.physicalPartition := by
  exact Q'.le_trans' _ _ _
    (actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_fullReceiverCellMass
      S root target)
    (actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_le_twice_positiveSourceProduct
      S root target)

/-! ## 3. Matched-AF one-face occupation compiler -/

/-- Producer-facing inputs in which the unreachable endpoint estimate has
been replaced by a one-face root-positive occupation estimate. -/
structure MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry) : Type where
  start : Nat
  spacingFloor : Q'
  spacingFloor_pos : (0 : Q') < spacingFloor
  mismatchQuadraticCeiling : Q'
  mismatchQuadraticCeiling_pos : (0 : Q') < mismatchQuadraticCeiling
  coveredVariationQuadraticCeiling : Q'
  coveredVariationQuadraticCeiling_pos :
    (0 : Q') < coveredVariationQuadraticCeiling
  positiveOccupationQuadraticCeiling : Q'
  positiveOccupationQuadraticCeiling_pos :
    (0 : Q') < positiveOccupationQuadraticCeiling
  spacingQuadratic_lower : ∀ scale : Nat, start ≤ scale →
    spacingFloor * (coupling scale * coupling scale) ≤
      spacing.a (coupling scale)
  rawMismatch_quadratic_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget
        (matchedShiftedAFPhysicalObservableRefinementSchedule
          family law spacing C coupling coupling_pos coupling_le_window
          identification nested)
        scale ≤
      mismatchQuadraticCeiling * (coupling scale * coupling scale)
  coveredVariation_quadratic_le : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
          S rfl (schedule.effectiveCoupling_pos scale) root target ≤
      (coveredVariationQuadraticCeiling *
          (coupling scale * coupling scale)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)
  positiveOccupation_quadratic_le : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    slabObservablePositiveSourceWeight S.coarse root ≤
      (positiveOccupationQuadraticCeiling *
          (coupling scale * coupling scale)) *
        S.coarse.physicalPartition

namespace MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {C : AFTrajectoryCertificate}
    {coupling : Nat → Q'}
    {coupling_pos : ∀ scale, (0 : Q') < coupling scale}
    {coupling_le_window : ∀ scale, coupling scale ≤ law.g₁}
    {identification : ShiftedAFTrajectoryIdentification C coupling}
    {nested : NestedCutoffOneFaceGeometry}

/-- The one-face occupation ceiling is paid once for each determinant cell. -/
def unreachableMassQuadraticCeiling
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) : Q' :=
  control.positiveOccupationQuadraticCeiling +
    control.positiveOccupationQuadraticCeiling

theorem unreachableMassQuadraticCeiling_pos
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    (0 : Q') < control.unreachableMassQuadraticCeiling :=
  Q'.add_pos control.positiveOccupationQuadraticCeiling_pos
    control.positiveOccupationQuadraticCeiling_pos

/-- A quadratic one-face occupation estimate supplies the unreachable-mass
field of the direct assignment-saturated covariance compiler. -/
def toCoveredVariationUnreachableMassQuadraticCostControl
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  coveredVariationQuadraticCeiling :=
    control.coveredVariationQuadraticCeiling
  coveredVariationQuadraticCeiling_pos :=
    control.coveredVariationQuadraticCeiling_pos
  unreachableMassQuadraticCeiling := control.unreachableMassQuadraticCeiling
  unreachableMassQuadraticCeiling_pos :=
    control.unreachableMassQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  coveredVariation_quadratic_le := control.coveredVariation_quadratic_le
  unreachableMass_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    let positive := slabObservablePositiveSourceWeight S.coarse root
    let quadratic := control.positiveOccupationQuadraticCeiling *
      (coupling scale * coupling scale)
    let partition := S.coarse.physicalPartition
    have hunreachable :
        actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
            S root target ≤
          positive * partition + positive * partition := by
      simpa only [positive, partition] using
        (actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_twice_positiveSourceProduct
          S root target)
    have hpositive : positive ≤ quadratic * partition := by
      simpa only [schedule, S, root, positive, quadratic, partition] using
        control.positiveOccupation_quadratic_le scale hscale
    have hscaled : positive * partition ≤
        (quadratic * partition) * partition :=
      Q'.mul_le_mul_of_nonneg_right positive (quadratic * partition)
        partition hpositive
        (Q'.le_of_lt
          (slabParametricKPhysicalPartition_pos
            S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent))
    have hdouble := Q'.add_le_add hscaled hscaled
    exact Q'.le_trans' _ _ _ hunreachable
      (Q'.le_trans' _ _ _ hdouble (Q'.le_of_eqv (by
        simp only [unreachableMassQuadraticCeiling, quadratic, partition]
        ring_qeqv)))

def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.toCovarianceRawCrossSeparatedLinearRawTransportTail

def toConnectedSeparatedLinearRawTransportTail
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail

theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl

#print axioms slabObservableFourCellSourcePairs_weight_le_positiveSourceProduct
#print axioms slabObservableFourCellTargetPairs_weight_le_positiveSourceProduct
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_le_twice_positiveSourceProduct
#print axioms actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_fullReceiverCellMass
#print axioms actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_twice_positiveSourceProduct
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl.toCoveredVariationUnreachableMassQuadraticCostControl
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationPositiveOccupationQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPositiveOccupationQuadraticCost
