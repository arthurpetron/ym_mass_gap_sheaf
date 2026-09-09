/-
# Coupling-one reference decomposition of the raw-column scale defect

The assignment-saturated covariance consumer asks for a quadratic estimate
on a *scale defect*: the coarse Gibbs four-cell cross, multiplied by the
fine partition square, minus the actual pushed receiver cross, multiplied by
the coarse partition square.  The preceding coupling-one comparison controls
only the second cross.

This module performs the exact missing recentering.  It defines the literal
coarse Gibbs cross and the reference scale defect obtained by replacing the
actual pushed cross with the coupling-one pushed cross.  The full raw-column
scale defect then splits exactly as

  referenceScaleDefect
    + coarsePartition^2 * (unitPushedCross - actualReceiverCross).

Consequently the matched-AF perturbation pays `2*g^2` times the localized
Casimir moment.  If the remaining reference scale defect is quadratically
calibrated and the localized moment is bounded by a volume-uniform multiple
of the fine partition square, the result compiles directly to the existing
raw-column calibration with coefficient

  referenceCeiling + 2 * momentCeiling.

The coarse law uses the explicitly decimated strong-coupling nome, so this
module does not assert that the coupling-one reference cross vanishes.  Its
remaining reference calibration is a genuine coarse/fine blocking input.
Nothing here proves volume-uniformity, all-cutoff persistence, a continuum
measure, OS/GNS reconstruction, a Hamiltonian gap, or the Yang--Mills mass
gap.

Constructive contract: exact rational algebra, positivity, and the preceding
finite coupling-one perturbation only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceScaleDefect

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration

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

private theorem scale_cross_reference_decomposition
    (fineSquare coarseCross coarseSquare unitCross actualCross : Q') :
    fineSquare * coarseCross - coarseSquare * actualCross ≈
      (fineSquare * coarseCross - coarseSquare * unitCross) +
        coarseSquare * (unitCross - actualCross) := by
  let A := fineSquare * coarseCross
  let B := coarseSquare * actualCross
  let C := coarseSquare * unitCross
  have hscaled :
      coarseSquare * (unitCross + -actualCross) ≈ C + -B := by
    refine Q'.eqv_trans _
      (coarseSquare * unitCross + coarseSquare * (-actualCross)) _
      (Q'.mul_add_eqv coarseSquare unitCross (-actualCross)) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_neg_eqv coarseSquare actualCross)
  have hcancel : -C + (C + -B) ≈ -B := by
    refine Q'.eqv_trans _ ((-C + C) + -B) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-C) C (-B))) ?_
    refine Q'.eqv_trans _ ((0 : Q') + -B) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.neg_add_self_eqv C)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-B))
  apply Q'.eqv_symm
  refine Q'.eqv_trans _ ((A + -C) + (C + -B)) _
    (Q'.add_eqv_congr_left _ _ _ hscaled) ?_
  refine Q'.eqv_trans _ (A + (-C + (C + -B))) _
    (Q'.add_assoc_eqv A (-C) (C + -B)) ?_
  exact Q'.add_eqv_congr_left A _ _ hcancel

private theorem scale_defect_cross_regroup
    (fineSquare coarseSquare coarseSource coarseTarget
      receiverSource receiverTarget : Q') :
    (fineSquare * coarseSource - coarseSquare * receiverSource) -
        (fineSquare * coarseTarget - coarseSquare * receiverTarget) ≈
      fineSquare * (coarseSource - coarseTarget) -
        coarseSquare * (receiverSource - receiverTarget) := by
  change
    (fineSquare * coarseSource + -(coarseSquare * receiverSource)) +
        -(fineSquare * coarseTarget + -(coarseSquare * receiverTarget)) ≈
      fineSquare * (coarseSource + -coarseTarget) +
        -(coarseSquare * (receiverSource + -receiverTarget))
  ring_qeqv

private theorem physicalPartitionSquare_nonnegative
    (D : SlabPhysicalData) :
    (0 : Q') ≤ D.physicalPartition * D.physicalPartition :=
  Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
    (Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))

/-! ## 1. Exact coarse-cross regrouping -/

/-- Signed coarse Gibbs mass on the same two four-cell carriers selected by
the raw-column covariance consumer. -/
def coarseObservableFourCellRawColumnCross
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellSourcePairs S.coarse root target) -
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellTargetPairs S.coarse root target)

/-- The raw-column scale defect is exactly fine-partition-square times the
coarse Gibbs cross minus coarse-partition-square times the actual receiver
cross. -/
theorem positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_crosses
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
        S hfineCutoff hcoarseCoupling root target ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
          coarseObservableFourCellRawColumnCross S root target -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          positiveExpandedAssignmentSaturatedReceiverRawColumnCross
            S hfineCutoff hcoarseCoupling root target := by
  unfold positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
    positiveExpandedFourCellSourceRawColumnScaleDefectMass
    positiveExpandedFourCellTargetRawColumnScaleDefectMass
    coarseObservableFourCellRawColumnCross
    positiveExpandedAssignmentSaturatedReceiverRawColumnCross
  exact scale_defect_cross_regroup _ _ _ _ _ _

/-! ## 2. Coupling-one reference scale defect -/

/-- Scale defect with the actual pushed receiver cross recentered at the
fine coupling-one pushed cross.  The coarse cross and both physical
partitions remain the literal objects from the actual scale pair. -/
def fineUnitCouplingReferenceRawColumnScaleDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  (S.fine.physicalPartition * S.fine.physicalPartition) *
      coarseObservableFourCellRawColumnCross S root target -
    (S.coarse.physicalPartition * S.coarse.physicalPartition) *
      fineUnitCouplingPushedRawColumnCross
        (physicalKernel S hfineCutoff hcoarseCoupling) root target

/-- Exact reference-plus-perturbation decomposition of the aggregate scale
defect. -/
theorem positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_reference_add
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
        S hfineCutoff hcoarseCoupling root target ≈
      fineUnitCouplingReferenceRawColumnScaleDefect
          S hfineCutoff hcoarseCoupling root target +
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          (fineUnitCouplingPushedRawColumnCross
              (physicalKernel S hfineCutoff hcoarseCoupling) root target -
            positiveExpandedAssignmentSaturatedReceiverRawColumnCross
              S hfineCutoff hcoarseCoupling root target) := by
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * S.fine.physicalPartition) *
          coarseObservableFourCellRawColumnCross S root target -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          positiveExpandedAssignmentSaturatedReceiverRawColumnCross
            S hfineCutoff hcoarseCoupling root target) _
    (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_crosses
      S hfineCutoff hcoarseCoupling root target) ?_
  exact scale_cross_reference_decomposition
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (coarseObservableFourCellRawColumnCross S root target)
    (S.coarse.physicalPartition * S.coarse.physicalPartition)
    (fineUnitCouplingPushedRawColumnCross
      (physicalKernel S hfineCutoff hcoarseCoupling) root target)
    (positiveExpandedAssignmentSaturatedReceiverRawColumnCross
      S hfineCutoff hcoarseCoupling root target)

/-- Absolute version of the exact split.  The only perturbative term left is
the localized coupling-one/actual receiver cross difference. -/
theorem positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_abs_le_reference_add
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    Q'.abs
        (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
          S hfineCutoff hcoarseCoupling root target) ≤
      Q'.abs
          (fineUnitCouplingReferenceRawColumnScaleDefect
            S hfineCutoff hcoarseCoupling root target) +
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          Q'.abs
            (fineUnitCouplingPushedRawColumnCross
                (physicalKernel S hfineCutoff hcoarseCoupling) root target -
              positiveExpandedAssignmentSaturatedReceiverRawColumnCross
                S hfineCutoff hcoarseCoupling root target) := by
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let reference := fineUnitCouplingReferenceRawColumnScaleDefect
    S hfineCutoff hcoarseCoupling root target
  let perturbation :=
    fineUnitCouplingPushedRawColumnCross
        (physicalKernel S hfineCutoff hcoarseCoupling) root target -
      positiveExpandedAssignmentSaturatedReceiverRawColumnCross
        S hfineCutoff hcoarseCoupling root target
  have hsplit :
      positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
          S hfineCutoff hcoarseCoupling root target ≈
        reference + coarseSquare * perturbation := by
    simpa only [reference, coarseSquare, perturbation] using
      (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_reference_add
        S hfineCutoff hcoarseCoupling root target)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _
      (Q'.abs_add_le' reference (coarseSquare * perturbation)) ?_)
  apply Q'.add_le_add_left
  refine Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le coarseSquare perturbation)
    (Q'.le_of_eqv ?_)
  exact Q'.mul_eqv_congr_right _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
      (by
        simpa only [coarseSquare] using
          (physicalPartitionSquare_nonnegative S.coarse)))

/-! ## 3. Matched-AF residual bound and calibration compiler -/

/-- On the matched AF window, the full scale defect is bounded by its honest
coarse/fine reference residual plus the explicit localized `2*g^2` moment
payment. -/
theorem positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_abs_le_reference_add_two_square_mul_moment
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (root target : Nat) :
    Q'.abs
        (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
          S hfineCutoff hcoarseCoupling root target) ≤
      Q'.abs
          (fineUnitCouplingReferenceRawColumnScaleDefect
            S hfineCutoff hcoarseCoupling root target) +
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          ((Q'.ofNat 2 * (g * g)) *
            (fineUnitCouplingPushedFourCellSourceCasimirMoment
                (physicalKernel S hfineCutoff hcoarseCoupling) root target +
              fineUnitCouplingPushedFourCellTargetCasimirMoment
                (physicalKernel S hfineCutoff hcoarseCoupling)
                root target)) := by
  have hsplit :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_abs_le_reference_add
      S hfineCutoff hcoarseCoupling root target
  have hperturbation :=
    fineUnitCouplingPhysicalRawColumnCross_sub_receiver_abs_le_two_square_mul_moment
      S hfineCutoff hcoarseCoupling hfineCoupling_le_one
      family law g hg hgle hcoupling root target
  exact Q'.le_trans' _ _ _ hsplit
    (Q'.add_le_add_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _
        (S.coarse.physicalPartition * S.coarse.physicalPartition)
        hperturbation
        (physicalPartitionSquare_nonnegative S.coarse)))

/-- Honest remaining analytic input for the reference scale defect.  The
normalization is exactly the one consumed by the aggregate raw-column
calibration. -/
def FineUnitCouplingReferenceRawColumnScaleDefectCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (g referenceCeiling : Q') : Prop :=
  Q'.abs
      (fineUnitCouplingReferenceRawColumnScaleDefect
        S hfineCutoff hcoarseCoupling root target) ≤
    (referenceCeiling * (g * g)) *
      ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
        (S.fine.physicalPartition * S.fine.physicalPartition))

/-- Honest remaining volume-normalization input for the localized pair-cell
Casimir moment. -/
def FineUnitCouplingLocalizedFourCellCasimirMomentBound
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (momentCeiling : Q') : Prop :=
  fineUnitCouplingPushedFourCellSourceCasimirMoment
        (physicalKernel S hfineCutoff hcoarseCoupling) root target +
      fineUnitCouplingPushedFourCellTargetCasimirMoment
        (physicalKernel S hfineCutoff hcoarseCoupling) root target ≤
    momentCeiling *
      (S.fine.physicalPartition * S.fine.physicalPartition)

/-- The reference residual calibration and localized moment normalization
compile to the exact aggregate raw-column calibration required by the finite
covariance theorem. -/
theorem positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_reference_and_moment
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (root target : Nat)
    (referenceCeiling momentCeiling : Q')
    (hreference :
      FineUnitCouplingReferenceRawColumnScaleDefectCalibration
        S hfineCutoff hcoarseCoupling root target g referenceCeiling)
    (hmoment :
      FineUnitCouplingLocalizedFourCellCasimirMomentBound
        S hfineCutoff hcoarseCoupling root target momentCeiling) :
    PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
      S hfineCutoff hcoarseCoupling root target
        ((referenceCeiling + Q'.ofNat 2 * momentCeiling) * (g * g)) := by
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let fineSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let moment :=
    fineUnitCouplingPushedFourCellSourceCasimirMoment
          (physicalKernel S hfineCutoff hcoarseCoupling) root target +
      fineUnitCouplingPushedFourCellTargetCasimirMoment
          (physicalKernel S hfineCutoff hcoarseCoupling) root target
  have hbase :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_abs_le_reference_add_two_square_mul_moment
      S hfineCutoff hcoarseCoupling hfineCoupling_le_one
      family law g hg hgle hcoupling root target
  have hmomentScaled :
      coarseSquare * ((Q'.ofNat 2 * (g * g)) * moment) ≤
        coarseSquare *
          ((Q'.ofNat 2 * (g * g)) * (momentCeiling * fineSquare)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ coarseSquare
      (Q'.mul_le_mul_of_nonneg_left _ _
        (Q'.ofNat 2 * (g * g))
        (by simpa only [FineUnitCouplingLocalizedFourCellCasimirMomentBound,
            moment, fineSquare] using hmoment)
        (Q'.mul_nonneg _ _
          (by decide : (0 : Q') ≤ Q'.ofNat 2)
          (Q'.mul_nonneg _ _ (Q'.le_of_lt hg) (Q'.le_of_lt hg))))
      (by simpa only [coarseSquare] using
        (physicalPartitionSquare_nonnegative S.coarse))
  have hsum := Q'.add_le_add
    (by simpa only [FineUnitCouplingReferenceRawColumnScaleDefectCalibration,
        coarseSquare, fineSquare] using hreference)
    hmomentScaled
  refine Q'.le_trans' _ _ _ hbase
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_))
  simp only [coarseSquare, fineSquare]
  ring_qeqv

#print axioms coarseObservableFourCellRawColumnCross
#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_crosses
#print axioms fineUnitCouplingReferenceRawColumnScaleDefect
#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_reference_add
#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_abs_le_reference_add
#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_abs_le_reference_add_two_square_mul_moment
#print axioms FineUnitCouplingReferenceRawColumnScaleDefectCalibration
#print axioms FineUnitCouplingLocalizedFourCellCasimirMomentBound
#print axioms positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_reference_and_moment

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceScaleDefect
