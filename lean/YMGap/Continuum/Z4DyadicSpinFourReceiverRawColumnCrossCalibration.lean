/-
# Cancellation-preserving raw column calibration for spin-four receivers

The pointwise receiver calibration is sufficient for total-variation control,
but the connected four-cell observable only consumes one signed source-minus-
target cross.  This module preserves that cancellation and identifies the
assignment-saturated raw cell totals with the literal pushed column law.

For each of the source and opposite four-cell carriers it proves exactly

  sum_receiver saturatedRawPushforwardMass(receiver)
    = sum_(coarse target pair) pushedColumnMass(left) * pushedColumnMass(right).

Consequently the connected receiver scale-defect cross is a single explicit
comparison between the coarse Gibbs cell cross and products of actual
one-replica pushed column masses.  A quadratic bound on that signed aggregate
cross compiles directly to the existing matched-AF finite covariance theorem.
No pointwise receiver estimate or receiver-cardinality factor is required on
this branch.

No aggregate estimate is inhabited here.  In particular this module proves
no stationarity or small-coupling perturbation theorem for the literal kernel,
no total-variation contraction, no all-cutoff persistence, no continuum
measure, no OS/GNS reconstruction, no Hamiltonian gap, and no Yang--Mills mass
gap.

Constructive contract: exact finite rational Fubini, signed cancellation,
positive rational division, and inequalities only; no choice, `Classical`,
`native_decide`, proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourReceiverRawPushforwardCalibration
import YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail

namespace YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawPushforwardCalibration

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem quadraticCost_le_normalizedSpacing_local
    (spacingFloor coefficient g spacingValue : Q')
    (hspacingFloor : (0 : Q') < spacingFloor)
    (hcoefficient : (0 : Q') < coefficient)
    (hlower : spacingFloor * (g * g) ≤ spacingValue) :
    coefficient * (g * g) ≤
      Q'.divPos coefficient spacingFloor hspacingFloor * spacingValue := by
  let normalized := Q'.divPos coefficient spacingFloor hspacingFloor
  have hnormalized : (0 : Q') ≤ normalized :=
    Q'.le_of_lt
      (Q'.divPos_pos coefficient spacingFloor hspacingFloor hcoefficient)
  have hmul := Q'.mul_le_mul_of_nonneg_left
    (spacingFloor * (g * g)) spacingValue normalized
    hlower hnormalized
  have hleft :
      normalized * (spacingFloor * (g * g)) ≈
        coefficient * (g * g) := by
    refine Q'.eqv_trans _
      ((normalized * spacingFloor) * (g * g)) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv normalized spacingFloor (g * g))
    · exact Q'.mul_eqv_congr_right _ _ (g * g)
        (Q'.divPos_mul_eqv coefficient spacingFloor hspacingFloor)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hleft)) hmul

/-! ## 1. Assignment-saturated raw cell totals -/

/-- Total source-cell raw mass after summing every accepted receiver
assignment with multiplicity. -/
def positiveExpandedFourCellSourceSaturatedReceiverRawCellMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (positiveExpandedFourCellSourceSaturatedReceiverFiberRawMass
      S hfineCutoff hcoarseCoupling root target)
    (slabObservableFourCellSourcePairs S.coarse root target)

/-- Total opposite-cell raw mass after the forced replica orientation and
summation over every accepted receiver assignment. -/
def positiveExpandedFourCellTargetSaturatedReceiverRawCellMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (positiveExpandedFourCellTargetSaturatedReceiverFiberRawMass
      S hfineCutoff hcoarseCoupling root target)
    (slabObservableFourCellTargetPairs S.coarse root target)

/-- Summing the new division-free source raw masses is exactly the earlier
receiver-density-weighted cell mass. -/
theorem positiveExpandedFourCellSourceSaturatedReceiverRawCellMass_eqv_weightedDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellSourceSaturatedReceiverRawCellMass
        S hfineCutoff hcoarseCoupling root target ≈
      listQSum
        (fun receiver =>
          positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
                S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellSourcePairs S.coarse root target) := by
  unfold positiveExpandedFourCellSourceSaturatedReceiverRawCellMass
  apply listQSum_congr_on
  intro receiver _
  exact Q'.eqv_symm
    (positiveExpandedFourCellSourceSaturatedReceiverFiberDensity_mul_weight_eqv_rawMass
      S hfineCutoff hcoarseCoupling root target receiver)

/-- Target analogue of the raw-cell/weighted-density identity. -/
theorem positiveExpandedFourCellTargetSaturatedReceiverRawCellMass_eqv_weightedDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellTargetSaturatedReceiverRawCellMass
        S hfineCutoff hcoarseCoupling root target ≈
      listQSum
        (fun receiver =>
          positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
                S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellTargetPairs S.coarse root target) := by
  unfold positiveExpandedFourCellTargetSaturatedReceiverRawCellMass
  apply listQSum_congr_on
  intro receiver _
  exact Q'.eqv_symm
    (positiveExpandedFourCellTargetSaturatedReceiverFiberDensity_mul_weight_eqv_rawMass
      S hfineCutoff hcoarseCoupling root target receiver)

/-! ## 2. Exact reduction to literal one-replica pushed columns -/

/-- The complete assignment-saturated source-cell raw total is exactly the
sum of products of the two actual pushed one-replica column masses. -/
theorem positiveExpandedFourCellSourceSaturatedReceiverRawCellMass_eqv_pushedColumns
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellSourceSaturatedReceiverRawCellMass
        S hfineCutoff hcoarseCoupling root target ≈
      listQSum
        (pushedPhysicalTargetPairRawMass
          (physicalKernel S hfineCutoff hcoarseCoupling))
        (pushedFaceRawFourCellSourcePairs (S := S) root target) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun receiver =>
        positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver *
          slabObservableTwoReplicaPairWeight S.coarse receiver)
      (slabObservableFourCellSourcePairs S.coarse root target)) _
    (positiveExpandedFourCellSourceSaturatedReceiverRawCellMass_eqv_weightedDensity
      S hfineCutoff hcoarseCoupling root target) ?_
  refine Q'.eqv_trans _
    (listQSum
      (positiveExpandedFourCellSourceSupportedPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positiveExpandedFourCellSourceSupportedPaths S root target)) _
    (positiveExpandedFourCellSourceSaturatedReceiverFiberMass_eqv
      S hfineCutoff hcoarseCoupling root target) ?_
  refine Q'.eqv_trans _
    (listQSum
      (positiveExpandedPushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positiveExpandedPushedFaceRawFourCellSourcePaths
        S root target)) _
    (Q'.eqv_symm
      (positiveExpandedFourCellSourcePaths_mass_eqv_supported
        S hfineCutoff hcoarseCoupling root target)) ?_
  refine Q'.eqv_trans _
    (listQSum
      (positivePushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positivePushedFaceRawFourCellSourcePaths S root target)) _
    (Q'.eqv_symm
      (positivePushedFaceRawFourCellSourcePaths_mass_eqv_expandedPaths
        S hfineCutoff hcoarseCoupling root target)) ?_
  refine Q'.eqv_trans _
    (listQSum
      (pushedPhysicalTwoReplicaPathRawMass
        (physicalKernel S hfineCutoff hcoarseCoupling))
      (pushedFaceRawFourCellSourcePaths S root target)) _
    (Q'.eqv_symm
      (pushedFaceRawFourCellSourcePaths_mass_eqv_positivePaths
        S hfineCutoff hcoarseCoupling root target)) ?_
  exact pushedFaceRawFourCellSourcePaths_mass_eqv_pair_mass
    (physicalKernel S hfineCutoff hcoarseCoupling) root target

/-- The opposite cell has the same exact reduction, with its literal
`FT x TF` coarse target-pair carrier. -/
theorem positiveExpandedFourCellTargetSaturatedReceiverRawCellMass_eqv_pushedColumns
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellTargetSaturatedReceiverRawCellMass
        S hfineCutoff hcoarseCoupling root target ≈
      listQSum
        (pushedPhysicalTargetPairRawMass
          (physicalKernel S hfineCutoff hcoarseCoupling))
        (pushedFaceRawFourCellTargetPairs (S := S) root target) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun receiver =>
        positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver *
          slabObservableTwoReplicaPairWeight S.coarse receiver)
      (slabObservableFourCellTargetPairs S.coarse root target)) _
    (positiveExpandedFourCellTargetSaturatedReceiverRawCellMass_eqv_weightedDensity
      S hfineCutoff hcoarseCoupling root target) ?_
  refine Q'.eqv_trans _
    (listQSum
      (positiveExpandedFourCellTargetSupportedPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positiveExpandedFourCellTargetSupportedPaths S root target)) _
    (positiveExpandedFourCellTargetSaturatedReceiverFiberMass_eqv
      S hfineCutoff hcoarseCoupling root target) ?_
  refine Q'.eqv_trans _
    (listQSum
      (positiveExpandedPushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positiveExpandedPushedFaceRawFourCellTargetPaths
        S root target)) _
    (Q'.eqv_symm
      (positiveExpandedFourCellTargetPaths_mass_eqv_supported
        S hfineCutoff hcoarseCoupling root target)) ?_
  refine Q'.eqv_trans _
    (listQSum
      (positivePushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positivePushedFaceRawFourCellTargetPaths S root target)) _
    (Q'.eqv_symm
      (positivePushedFaceRawFourCellTargetPaths_mass_eqv_expandedPaths
        S hfineCutoff hcoarseCoupling root target)) ?_
  refine Q'.eqv_trans _
    (listQSum
      (pushedPhysicalTwoReplicaPathRawMass
        (physicalKernel S hfineCutoff hcoarseCoupling))
      (pushedFaceRawFourCellTargetPaths S root target)) _
    (Q'.eqv_symm
      (pushedFaceRawFourCellTargetPaths_mass_eqv_positivePaths
        S hfineCutoff hcoarseCoupling root target)) ?_
  exact pushedFaceRawFourCellTargetPaths_mass_eqv_pair_mass
    (physicalKernel S hfineCutoff hcoarseCoupling) root target

/-- Signed receiver raw-cell cross, retaining exactly the cancellation used
by the connected four-cell observable. -/
def positiveExpandedAssignmentSaturatedReceiverRawColumnCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  positiveExpandedFourCellSourceSaturatedReceiverRawCellMass
      S hfineCutoff hcoarseCoupling root target -
    positiveExpandedFourCellTargetSaturatedReceiverRawCellMass
      S hfineCutoff hcoarseCoupling root target

/-- The signed receiver raw-cell cross is the actual pushed four-cell cross;
the two-replica entries on the right are products of literal one-replica
column masses by definition. -/
theorem positiveExpandedAssignmentSaturatedReceiverRawColumnCross_eqv_actualPushed
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedAssignmentSaturatedReceiverRawColumnCross
        S hfineCutoff hcoarseCoupling root target ≈
      actualPushedFaceRawFourCellCross
        S hfineCutoff hcoarseCoupling root target := by
  refine Q'.eqv_trans _
    (listQSum
        (pushedPhysicalTargetPairRawMass
          (physicalKernel S hfineCutoff hcoarseCoupling))
        (pushedFaceRawFourCellSourcePairs (S := S) root target) -
      listQSum
        (pushedPhysicalTargetPairRawMass
          (physicalKernel S hfineCutoff hcoarseCoupling))
        (pushedFaceRawFourCellTargetPairs (S := S) root target)) _ ?_ ?_
  · unfold positiveExpandedAssignmentSaturatedReceiverRawColumnCross
    exact sub_eqv_both_local
      (positiveExpandedFourCellSourceSaturatedReceiverRawCellMass_eqv_pushedColumns
        S hfineCutoff hcoarseCoupling root target)
      (positiveExpandedFourCellTargetSaturatedReceiverRawCellMass_eqv_pushedColumns
        S hfineCutoff hcoarseCoupling root target)
  · exact Q'.eqv_trans _
      (pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling) root target) _
      (Q'.eqv_symm
        (pushedFaceRawFourCellCross_eqv_pair_mass_difference
          (physicalKernel S hfineCutoff hcoarseCoupling) root target))
      (pushedFaceRawFourCellCross_physicalKernel_eqv_actualRaw
        S hfineCutoff hcoarseCoupling root target)

/-! ## 3. Aggregate raw column scale defect -/

def positiveExpandedFourCellSourceRawColumnScaleDefectMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  (S.fine.physicalPartition * S.fine.physicalPartition) *
      listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellSourcePairs S.coarse root target) -
    (S.coarse.physicalPartition * S.coarse.physicalPartition) *
      positiveExpandedFourCellSourceSaturatedReceiverRawCellMass
        S hfineCutoff hcoarseCoupling root target

def positiveExpandedFourCellTargetRawColumnScaleDefectMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  (S.fine.physicalPartition * S.fine.physicalPartition) *
      listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellTargetPairs S.coarse root target) -
    (S.coarse.physicalPartition * S.coarse.physicalPartition) *
      positiveExpandedFourCellTargetSaturatedReceiverRawCellMass
        S hfineCutoff hcoarseCoupling root target

def positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  positiveExpandedFourCellSourceRawColumnScaleDefectMass
      S hfineCutoff hcoarseCoupling root target -
    positiveExpandedFourCellTargetRawColumnScaleDefectMass
      S hfineCutoff hcoarseCoupling root target

theorem positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass_eqv_rawColumn
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass
        S hfineCutoff hcoarseCoupling root target ≈
      positiveExpandedFourCellSourceRawColumnScaleDefectMass
        S hfineCutoff hcoarseCoupling root target := by
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * S.fine.physicalPartition) *
        listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservableFourCellSourcePairs S.coarse root target) -
      (S.coarse.physicalPartition * S.coarse.physicalPartition) *
        listQSum
          (fun receiver =>
            positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver *
              slabObservableTwoReplicaPairWeight S.coarse receiver)
          (slabObservableFourCellSourcePairs S.coarse root target)) _
    (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass_eqv
      S hfineCutoff hcoarseCoupling root target) ?_
  unfold positiveExpandedFourCellSourceRawColumnScaleDefectMass
  exact sub_eqv_both_local (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_left
      (S.coarse.physicalPartition * S.coarse.physicalPartition) _ _
      (Q'.eqv_symm
        (positiveExpandedFourCellSourceSaturatedReceiverRawCellMass_eqv_weightedDensity
          S hfineCutoff hcoarseCoupling root target)))

theorem positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass_eqv_rawColumn
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass
        S hfineCutoff hcoarseCoupling root target ≈
      positiveExpandedFourCellTargetRawColumnScaleDefectMass
        S hfineCutoff hcoarseCoupling root target := by
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * S.fine.physicalPartition) *
        listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservableFourCellTargetPairs S.coarse root target) -
      (S.coarse.physicalPartition * S.coarse.physicalPartition) *
        listQSum
          (fun receiver =>
            positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver *
              slabObservableTwoReplicaPairWeight S.coarse receiver)
          (slabObservableFourCellTargetPairs S.coarse root target)) _
    (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass_eqv
      S hfineCutoff hcoarseCoupling root target) ?_
  unfold positiveExpandedFourCellTargetRawColumnScaleDefectMass
  exact sub_eqv_both_local (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_left
      (S.coarse.physicalPartition * S.coarse.physicalPartition) _ _
      (Q'.eqv_symm
        (positiveExpandedFourCellTargetSaturatedReceiverRawCellMass_eqv_weightedDensity
          S hfineCutoff hcoarseCoupling root target)))

/-- The earlier signed receiver scale-defect cross is exactly the new
division-free column cross. -/
theorem actualPositiveExpandedAssignmentSaturatedScaleDefectCross_eqv_rawColumn
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedAssignmentSaturatedScaleDefectCross
        S hfineCutoff hcoarseCoupling root target ≈
      positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
        S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedAssignmentSaturatedScaleDefectCross
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
  exact sub_eqv_both_local
    (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass_eqv_rawColumn
      S hfineCutoff hcoarseCoupling root target)
    (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass_eqv_rawColumn
      S hfineCutoff hcoarseCoupling root target)

/-- Cancellation-preserving analytic input.  Unlike pointwise receiver
calibration, this asks only for the signed four-cell column cross needed by
the chosen connected observable. -/
def PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (relative : Q') : Prop :=
  Q'.abs
      (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
        S hfineCutoff hcoarseCoupling root target) ≤
    relative *
      ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
        (S.fine.physicalPartition * S.fine.physicalPartition))

/-- The aggregate raw-column calibration has exactly the normalization
needed by the complete physical covariance raw-cross denominator. -/
theorem physicalConnectedCovarianceRawCrossDefect_abs_le_of_rawColumnCrossCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (relative : Q')
    (hcalibration :
      PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
        S hfineCutoff hcoarseCoupling
        M.coarseRoot M.coarseTarget relative) :
    Q'.abs
        (physicalConnectedCovarianceRawCrossDefect
          S hfineCutoff hcoarseCoupling M) ≤
      relative * connectedCovarianceRawCrossDenominator S := by
  let cross :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  let coarseFine :=
    S.coarse.physicalPartition * S.fine.physicalPartition
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let fineSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  have hfactor :
      physicalConnectedCovarianceRawCrossDefect
          S hfineCutoff hcoarseCoupling M ≈
        coarseFine * cross :=
    Q'.eqv_trans _
      (coarseFine *
        actualPositiveExpandedAssignmentSaturatedScaleDefectCross
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget) _
      (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedAssignmentSaturatedScaleDefect
        S hfineCutoff hcoarseCoupling M)
      (Q'.mul_eqv_congr_left coarseFine _ _
        (actualPositiveExpandedAssignmentSaturatedScaleDefectCross_eqv_rawColumn
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget))
  have habsProduct :
      Q'.abs
          (physicalConnectedCovarianceRawCrossDefect
            S hfineCutoff hcoarseCoupling M) ≤
        Q'.abs coarseFine * Q'.abs cross :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hfactor))
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le coarseFine cross)
  have hscaledCalibration :
      Q'.abs coarseFine * Q'.abs cross ≤
        Q'.abs coarseFine * (relative * (coarseSquare * fineSquare)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs coarseFine)
      (by simpa only [PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration,
          cross, coarseSquare, fineSquare] using hcalibration)
      (Q'.abs_nonneg coarseFine)
  refine Q'.le_trans' _ _ _ habsProduct
    (Q'.le_trans' _ _ _ hscaledCalibration (Q'.le_of_eqv ?_))
  refine Q'.eqv_trans _
    (coarseFine * (relative * (coarseSquare * fineSquare))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt
            (slabParametricKPhysicalPartition_pos
              S.coarse.coupling_nonnegative
              S.coarse.cutoff S.coarse.extent))
          (Q'.le_of_lt
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative
              S.fine.cutoff S.fine.extent))))
  · unfold connectedCovarianceRawCrossDenominator
      rawCovarianceDenominator
    simp only [coarseFine, coarseSquare, fineSquare]
    ring_qeqv

/-! ## 4. Matched-AF schedule compiler -/

/-- Matched-AF producer whose connected field is the single signed aggregate
raw-column calibration.  This branch is tailored to the selected four-cell
covariance and does not assert full receiver total-variation contraction. -/
structure MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl
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
  rawColumnCrossQuadraticCeiling : Q'
  rawColumnCrossQuadraticCeiling_pos :
    (0 : Q') < rawColumnCrossQuadraticCeiling
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
  rawColumnCross_quadratic : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
      S rfl (schedule.effectiveCoupling_pos scale) root target
        (rawColumnCrossQuadraticCeiling *
          (coupling scale * coupling scale))

namespace MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl

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

def mismatchCeiling
    (control : MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) : Q' :=
  Q'.divPos control.mismatchQuadraticCeiling control.spacingFloor
    control.spacingFloor_pos

theorem mismatchCeiling_pos
    (control : MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :
    (0 : Q') < control.mismatchCeiling :=
  Q'.divPos_pos _ _ control.spacingFloor_pos
    control.mismatchQuadraticCeiling_pos

def connectedCeiling
    (control : MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) : Q' :=
  Q'.divPos control.rawColumnCrossQuadraticCeiling control.spacingFloor
    control.spacingFloor_pos

theorem connectedCeiling_pos
    (control : MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :
    (0 : Q') < control.connectedCeiling :=
  Q'.divPos_pos _ _ control.spacingFloor_pos
    control.rawColumnCrossQuadraticCeiling_pos

/-- The aggregate quadratic column producer compiles to the existing exact
actual-covariance raw-cross tail. -/
def toActualCovarianceRawCrossSeparatedLinearRawTransportTail
    (control : MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :
    ActualCovarianceRawCrossSeparatedLinearRawTransportTail
      (matchedShiftedAFPhysicalObservableRefinementSchedule
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) where
  start := control.start
  mismatchCeiling := control.mismatchCeiling
  mismatchCeiling_pos := control.mismatchCeiling_pos
  connectedCeiling := control.connectedCeiling
  connectedCeiling_pos := control.connectedCeiling_pos
  mismatch_le := fun scale hscale => by
    exact Q'.le_trans' _ _ _
      (control.rawMismatch_quadratic_le scale hscale)
      (by
        simpa only [mismatchCeiling,
          matchedShiftedAFPhysicalObservableRefinementSchedule_spacing] using
          (quadraticCost_le_normalizedSpacing_local
            control.spacingFloor control.mismatchQuadraticCeiling
            (coupling scale) (spacing.a (coupling scale))
            control.spacingFloor_pos
            control.mismatchQuadraticCeiling_pos
            (control.spacingQuadratic_lower scale hscale)))
  actualConnectedCovarianceRawCross_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let M := schedule.faceMap scale
    let quadratic := control.rawColumnCrossQuadraticCeiling *
      (coupling scale * coupling scale)
    let denominator := connectedCovarianceRawCrossDenominator S
    have hphysical :
        Q'.abs
            (physicalConnectedCovarianceRawCrossDefect
              S rfl (schedule.effectiveCoupling_pos scale) M) ≤
          quadratic * denominator := by
      simpa only [quadratic, denominator] using
        (physicalConnectedCovarianceRawCrossDefect_abs_le_of_rawColumnCrossCalibration
          S rfl (schedule.effectiveCoupling_pos scale) M quadratic
          (by
            simpa only [schedule, S, M, quadratic] using
              (control.rawColumnCross_quadratic scale hscale)))
    have hquadratic :
        quadratic ≤ control.connectedCeiling *
          spacing.a (coupling scale) := by
      simpa only [quadratic, connectedCeiling] using
        (quadraticCost_le_normalizedSpacing_local
          control.spacingFloor control.rawColumnCrossQuadraticCeiling
          (coupling scale) (spacing.a (coupling scale))
          control.spacingFloor_pos
          control.rawColumnCrossQuadraticCeiling_pos
          (control.spacingQuadratic_lower scale hscale))
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      quadratic
      (control.connectedCeiling * spacing.a (coupling scale))
      denominator hquadratic
      (Q'.le_of_lt (connectedCovarianceRawCrossDenominator_pos S))
    exact Q'.le_trans' _ _ _ hphysical
      (by simpa only [schedule, S, M, denominator,
          matchedShiftedAFPhysicalObservableRefinementSchedule_spacing] using
        hscaled)

/-- Final finite covariance consumer for the cancellation-preserving raw
column cross.  Its aggregate calibration remains an explicit analytic field. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (control : MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toActualCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toActualCovarianceRawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl

#print axioms positiveExpandedFourCellSourceSaturatedReceiverRawCellMass
#print axioms positiveExpandedFourCellTargetSaturatedReceiverRawCellMass
#print axioms positiveExpandedFourCellSourceSaturatedReceiverRawCellMass_eqv_pushedColumns
#print axioms positiveExpandedFourCellTargetSaturatedReceiverRawCellMass_eqv_pushedColumns
#print axioms positiveExpandedAssignmentSaturatedReceiverRawColumnCross_eqv_actualPushed
#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
#print axioms actualPositiveExpandedAssignmentSaturatedScaleDefectCross_eqv_rawColumn
#print axioms PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
#print axioms physicalConnectedCovarianceRawCrossDefect_abs_le_of_rawColumnCrossCalibration
#print axioms MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl
#print axioms MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl.toActualCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration
