/-
# Compile pointwise relative receiver calibration into full variation

Exact spin-four endpoint coverage has reduced the matched-AF receiver
obligation to the unfiltered source-plus-target scale-defect `l1`.  This
module isolates a sufficient pointwise analytic input for that remaining
finite sum.

If every source and target receiver defect is at most

  relative * Z_fine^2,

then summing against the physical receiver weights costs no carrier
cardinality.  Both receiver cells together have mass at most
`2 * Z_coarse^2`, so division by the fine partition square leaves the full
normalized variation at most `2 * relative * Z_coarse^2`.  Specializing
`relative = coefficient * coupling^2` gives exactly the quadratic shape
required by the matched-AF receiver producer.

No pointwise calibration estimate is inhabited here.  In particular this
is not an all-cutoff contraction, continuum construction, OS/GNS
reconstruction, Hamiltonian gap, or Yang--Mills mass gap.

Constructive contract: exact rational finite sums and inequalities only; no
choice, `Classical`, `native_decide`, proof hole, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourMatchedAFCoverage
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPositiveOccupationQuadraticCost
import YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness

namespace YMGap.Continuum.Z4DyadicSpinFourReceiverPointwiseCalibration

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedNormalizedVariation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPositiveOccupationQuadraticCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateCoverageDeficit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourMatchedAFCoverage

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Int.add_mul,
               Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem abs_mul_weight_le_of_abs_le
    (defect weight budget : Q')
    (hweight : (0 : Q') ≤ weight)
    (hdefect : Q'.abs defect ≤ budget) :
    Q'.abs (defect * weight) ≤ budget * weight := by
  refine Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le defect weight) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right
      (Q'.abs defect) budget (Q'.abs weight)
      hdefect (Q'.abs_nonneg weight)) ?_
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_left budget (Q'.abs weight) weight
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hweight))

/-! ## 1. Pointwise bounds sum without cardinality loss -/

/-- A common source-receiver defect budget factors through the exact source
receiver mass. -/
theorem actualPositiveExpandedAssignmentSaturatedSourceScaleDefectL1_le_pointwiseBudget_mul_mass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (budget : Q')
    (hpointwise : ∀ receiver,
      receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
      Q'.abs
          (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≤ budget) :
    actualPositiveExpandedAssignmentSaturatedSourceScaleDefectL1
        S hfineCutoff hcoarseCoupling root target ≤
      budget *
        listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservableFourCellSourcePairs S.coarse root target) := by
  unfold actualPositiveExpandedAssignmentSaturatedSourceScaleDefectL1
  refine Q'.le_trans' _ _ _
    (listQSum_le_termwise_local
      (fun receiver =>
        Q'.abs
          (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver))
      (fun receiver =>
        budget * slabObservableTwoReplicaPairWeight S.coarse receiver)
      (slabObservableFourCellSourcePairs S.coarse root target)
      (fun receiver hreceiver =>
        abs_mul_weight_le_of_abs_le
          (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver)
          (slabObservableTwoReplicaPairWeight S.coarse receiver)
          budget
          (slabObservableTwoReplicaPairWeight_nonnegative
            S.coarse root receiver)
          (hpointwise receiver hreceiver))) ?_
  exact Q'.le_of_eqv
    (listQSum_mul_left budget
      (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellSourcePairs S.coarse root target))

/-- The same cardinality-free summation for the opposite target cell. -/
theorem actualPositiveExpandedAssignmentSaturatedTargetScaleDefectL1_le_pointwiseBudget_mul_mass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (budget : Q')
    (hpointwise : ∀ receiver,
      receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
      Q'.abs
          (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≤ budget) :
    actualPositiveExpandedAssignmentSaturatedTargetScaleDefectL1
        S hfineCutoff hcoarseCoupling root target ≤
      budget *
        listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservableFourCellTargetPairs S.coarse root target) := by
  unfold actualPositiveExpandedAssignmentSaturatedTargetScaleDefectL1
  refine Q'.le_trans' _ _ _
    (listQSum_le_termwise_local
      (fun receiver =>
        Q'.abs
          (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver))
      (fun receiver =>
        budget * slabObservableTwoReplicaPairWeight S.coarse receiver)
      (slabObservableFourCellTargetPairs S.coarse root target)
      (fun receiver hreceiver =>
        abs_mul_weight_le_of_abs_le
          (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver)
          (slabObservableTwoReplicaPairWeight S.coarse receiver)
          budget
          (slabObservableTwoReplicaPairWeight_nonnegative
            S.coarse root receiver)
          (hpointwise receiver hreceiver))) ?_
  exact Q'.le_of_eqv
    (listQSum_mul_left budget
      (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellTargetPairs S.coarse root target))

/-- A common pointwise budget controls the full source-plus-target `l1` by
that budget times the exact full receiver-cell mass. -/
theorem actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1_le_pointwiseBudget_mul_fullReceiverCellMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (budget : Q')
    (hsource : ∀ receiver,
      receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
      Q'.abs
          (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≤ budget)
    (htarget : ∀ receiver,
      receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
      Q'.abs
          (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≤ budget) :
    actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
        S hfineCutoff hcoarseCoupling root target ≤
      budget *
        actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
          S root target := by
  unfold actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
    actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add
      (actualPositiveExpandedAssignmentSaturatedSourceScaleDefectL1_le_pointwiseBudget_mul_mass
        S hfineCutoff hcoarseCoupling root target budget hsource)
      (actualPositiveExpandedAssignmentSaturatedTargetScaleDefectL1_le_pointwiseBudget_mul_mass
        S hfineCutoff hcoarseCoupling root target budget htarget)) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.mul_add_eqv budget
        (listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservableFourCellSourcePairs S.coarse root target))
        (listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservableFourCellTargetPairs S.coarse root target))))

/-! ## 2. Exact partition-scale accounting -/

/-- The two canonical receiver cells together cost at most two copies of the
coarse physical partition square. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_le_twice_coarseSquare
    (S : SlabScalePair) (root target : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
        S root target ≤
      S.coarse.physicalPartition * S.coarse.physicalPartition +
        S.coarse.physicalPartition * S.coarse.physicalPartition := by
  have hpositiveAdd :=
    slabObservablePositiveSourceWeight_add_one_le_partition S.coarse root
  have hpositive :
      slabObservablePositiveSourceWeight S.coarse root ≤
        S.coarse.physicalPartition :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg
        (slabObservablePositiveSourceWeight S.coarse root) 1 (by decide))
      hpositiveAdd
  have hpartitionNonnegative :
      (0 : Q') ≤ S.coarse.physicalPartition :=
    Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
  have hproduct :
      slabObservablePositiveSourceWeight S.coarse root *
          S.coarse.physicalPartition ≤
        S.coarse.physicalPartition * S.coarse.physicalPartition :=
    Q'.mul_le_mul_of_nonneg_right
      (slabObservablePositiveSourceWeight S.coarse root)
      S.coarse.physicalPartition S.coarse.physicalPartition
      hpositive hpartitionNonnegative
  exact Q'.le_trans' _ _ _
    (actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_le_twice_positiveSourceProduct
      S root target)
    (Q'.add_le_add hproduct hproduct)

/-- A pointwise receiver calibration in fine-partition-square units implies
the full normalized-variation bound with exactly one prescribed coarse
partition-square factor and no receiver-cardinality loss. -/
theorem actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_twice_relative_mul_coarseSquare_of_pointwise
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (relative : Q')
    (hrelative : (0 : Q') ≤ relative)
    (hsource : ∀ receiver,
      receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
      Q'.abs
          (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≤
        relative *
          (S.fine.physicalPartition * S.fine.physicalPartition))
    (htarget : ∀ receiver,
      receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
      Q'.abs
          (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≤
        relative *
          (S.fine.physicalPartition * S.fine.physicalPartition)) :
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
        S hfineCutoff hcoarseCoupling root target ≤
      (relative + relative) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  let fineSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let budget := relative * fineSquare
  have hfull :
      actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
          S hfineCutoff hcoarseCoupling root target ≤
        budget *
          actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
            S root target :=
    actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1_le_pointwiseBudget_mul_fullReceiverCellMass
      S hfineCutoff hcoarseCoupling root target budget hsource htarget
  have hbudgetNonnegative : (0 : Q') ≤ budget := by
    exact Q'.mul_nonneg relative fineSquare hrelative
      (Q'.le_of_lt (finePhysicalPartitionSquare_pos S))
  have hmass :
      actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
          S root target ≤
        coarseSquare + coarseSquare :=
    actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_le_twice_coarseSquare
      S root target
  have hscaled :
      budget *
          actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
            S root target ≤
        budget * (coarseSquare + coarseSquare) :=
    Q'.mul_le_mul_of_nonneg_left _ _ budget hmass hbudgetNonnegative
  have hcollapse :
      budget * (coarseSquare + coarseSquare) ≈
        ((relative + relative) * coarseSquare) * fineSquare := by
    simp only [budget]
    ring_qeqv
  unfold actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hfull
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse))

/-- Quadratic specialization in exactly the units consumed by the matched-AF
covered-variation field. -/
theorem actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_quadratic_mul_coarseSquare_of_pointwise
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (coefficient coupling : Q')
    (hcoefficient : (0 : Q') ≤ coefficient)
    (hcoupling : (0 : Q') ≤ coupling)
    (hsource : ∀ receiver,
      receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
      Q'.abs
          (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≤
        (coefficient * (coupling * coupling)) *
          (S.fine.physicalPartition * S.fine.physicalPartition))
    (htarget : ∀ receiver,
      receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
      Q'.abs
          (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≤
        (coefficient * (coupling * coupling)) *
          (S.fine.physicalPartition * S.fine.physicalPartition)) :
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
        S hfineCutoff hcoarseCoupling root target ≤
      ((coefficient + coefficient) * (coupling * coupling)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  have hrelative :
      (0 : Q') ≤ coefficient * (coupling * coupling) :=
    Q'.mul_nonneg coefficient (coupling * coupling) hcoefficient
      (Q'.mul_nonneg coupling coupling hcoupling hcoupling)
  have hbase :=
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_twice_relative_mul_coarseSquare_of_pointwise
      S hfineCutoff hcoarseCoupling root target
      (coefficient * (coupling * coupling)) hrelative hsource htarget
  exact Q'.le_trans' _ _ _ hbase
    (Q'.le_of_eqv (by ring_qeqv))

/-- Exact endpoint coverage transfers the pointwise quadratic estimate into
the covered-variation field used by the matched-AF covariance compiler. -/
theorem actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1_le_quadratic_mul_coarseSquare_of_pointwise_endpointCoverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (coefficient coupling : Q')
    (hcoefficient : (0 : Q') ≤ coefficient)
    (hcoupling : (0 : Q') ≤ coupling)
    (hsource : ∀ receiver,
      receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
      Q'.abs
          (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≤
        (coefficient * (coupling * coupling)) *
          (S.fine.physicalPartition * S.fine.physicalPartition))
    (htarget : ∀ receiver,
      receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
      Q'.abs
          (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≤
        (coefficient * (coupling * coupling)) *
          (S.fine.physicalPartition * S.fine.physicalPartition)) :
    actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
        S hfineCutoff hcoarseCoupling root target ≤
      ((coefficient + coefficient) * (coupling * coupling)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) :=
  coveredCoarseNormalizedVariationL1_le_of_full_le_endpointCoverage
    S hfineCutoff hcoarseCoupling root target coverage _
      (actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_quadratic_mul_coarseSquare_of_pointwise
        S hfineCutoff hcoarseCoupling root target coefficient coupling
        hcoefficient hcoupling hsource htarget)

#print axioms actualPositiveExpandedAssignmentSaturatedSourceScaleDefectL1_le_pointwiseBudget_mul_mass
#print axioms actualPositiveExpandedAssignmentSaturatedTargetScaleDefectL1_le_pointwiseBudget_mul_mass
#print axioms actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1_le_pointwiseBudget_mul_fullReceiverCellMass
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_le_twice_coarseSquare
#print axioms actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_twice_relative_mul_coarseSquare_of_pointwise
#print axioms actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_quadratic_mul_coarseSquare_of_pointwise
#print axioms actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1_le_quadratic_mul_coarseSquare_of_pointwise_endpointCoverage

end YMGap.Continuum.Z4DyadicSpinFourReceiverPointwiseCalibration
