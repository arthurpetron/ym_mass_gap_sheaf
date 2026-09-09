/-
# Division-free raw pushforward calibration for saturated spin-four receivers

The saturated receiver density is defined by dividing each supported path
mass across the complete accepted coarse-assignment fiber and then summing
over coincident receiver lifts.  The analytic statement needed by the
matched-AF covariance compiler should therefore be expressible without any
quotient: compare the literal raw mass pushed to one receiver with

  partitionDensity * receiverWeight.

This module constructs that receiver-wise raw pushforward mass explicitly and
proves

  saturatedDensity * receiverWeight = saturatedRawPushforwardMass.

Strict positivity of every physical receiver weight then makes the raw-mass
calibration exactly equivalent to the previous relative-density calibration.
Thus the remaining analytic obligation is now stated directly on finite raw
recoupling weights; no denominator estimate or receiver-cardinality factor is
hidden in the interface.

No raw calibration estimate is inhabited here.  In particular this module
does not prove stationarity or a perturbation bound for the literal
recoupling kernel, an all-cutoff contraction, a continuum construction,
OS/GNS reconstruction, a Hamiltonian gap, or the Yang--Mills mass gap.

Constructive contract: finite exact rational sums, positive-factor
cancellation, and no choice, `Classical`, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourReceiverRelativeDensityCalibration
import YMGap.Continuum.FiniteCoefficientZeroExtension
import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.TsumDeriv

namespace YMGap.Continuum.Z4DyadicSpinFourReceiverRawPushforwardCalibration

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.TsumDeriv
open YMGap.Continuum.Z4DyadicSpinFourReceiverRelativeDensityCalibration

local infix:50 " ≈ " => Q'.eqv

local instance rawPushforwardReceiverPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

/-- Multiplying a zero-extended fiber coefficient by a target value is the
same as zero-extending the source coefficient already multiplied by the
value at its coded target. -/
private theorem finiteCoefficientZeroExtension_mul_value_eqv_local
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (coefficient : Source → Q')
    (code : Source → Target) (value : Target → Q')
    (target : Target) :
    finiteCoefficientZeroExtension source coefficient code target *
        value target ≈
      finiteCoefficientZeroExtension source
        (fun item => coefficient item * value (code item))
        code target := by
  unfold finiteCoefficientZeroExtension fiberWeight
  refine Q'.eqv_trans _
    (listQSum
      (fun item => coefficient item * value target)
      (source.filter (fun item => decide (target = code item)))) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_mul_right coefficient (value target)
        (source.filter (fun item => decide (target = code item))))
  · apply listQSum_congr_on
    intro item hitem
    have hcode : target = code item :=
      of_decide_eq_true (List.mem_filter.mp hitem).2
    rw [hcode]
    exact Q'.eqv_refl _

/-! ## 1. Literal receiver-wise raw pushforward masses -/

/-- Raw source-cell mass pushed to one receiver, before division by that
receiver's physical Gibbs weight.  Each saturated lift contributes its
assignment-apportioned path mass, and coincident lifts retain multiplicity. -/
def positiveExpandedFourCellSourceSaturatedReceiverFiberRawMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) : Q' :=
  finiteCoefficientZeroExtension
    (positiveExpandedFourCellSourceSaturatedReceiverLifts
      S root target)
    (fun lift =>
      positiveExpandedFourCellSourceSaturatedLiftDensity
          S hfineCutoff hcoarseCoupling lift *
        slabObservableTwoReplicaPairWeight S.coarse lift.receiver)
    PositiveExpandedFourCellSourceSaturatedReceiverLift.receiver
    receiver

/-- The saturated source density times the receiver Gibbs weight is exactly
the literal raw mass pushed to that receiver. -/
theorem positiveExpandedFourCellSourceSaturatedReceiverFiberDensity_mul_weight_eqv_rawMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) :
    positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver *
        slabObservableTwoReplicaPairWeight S.coarse receiver ≈
      positiveExpandedFourCellSourceSaturatedReceiverFiberRawMass
        S hfineCutoff hcoarseCoupling root target receiver := by
  unfold positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
    positiveExpandedFourCellSourceSaturatedReceiverFiberRawMass
  exact finiteCoefficientZeroExtension_mul_value_eqv_local
    (positiveExpandedFourCellSourceSaturatedReceiverLifts S root target)
    (positiveExpandedFourCellSourceSaturatedLiftDensity
      S hfineCutoff hcoarseCoupling)
    PositiveExpandedFourCellSourceSaturatedReceiverLift.receiver
    (slabObservableTwoReplicaPairWeight S.coarse)
    receiver

/-- Raw opposite-cell mass pushed to one replica-oriented receiver, before
division by that receiver's physical Gibbs weight. -/
def positiveExpandedFourCellTargetSaturatedReceiverFiberRawMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) : Q' :=
  finiteCoefficientZeroExtension
    (positiveExpandedFourCellTargetSaturatedReceiverLifts
      S root target)
    (fun lift =>
      positiveExpandedFourCellTargetSaturatedLiftDensity
          S hfineCutoff hcoarseCoupling lift *
        slabObservableTwoReplicaPairWeight S.coarse lift.receiver)
    PositiveExpandedFourCellTargetSaturatedReceiverLift.receiver
    receiver

/-- The saturated target density times the receiver Gibbs weight is exactly
the literal raw mass pushed to that receiver. -/
theorem positiveExpandedFourCellTargetSaturatedReceiverFiberDensity_mul_weight_eqv_rawMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) :
    positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver *
        slabObservableTwoReplicaPairWeight S.coarse receiver ≈
      positiveExpandedFourCellTargetSaturatedReceiverFiberRawMass
        S hfineCutoff hcoarseCoupling root target receiver := by
  unfold positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
    positiveExpandedFourCellTargetSaturatedReceiverFiberRawMass
  exact finiteCoefficientZeroExtension_mul_value_eqv_local
    (positiveExpandedFourCellTargetSaturatedReceiverLifts S root target)
    (positiveExpandedFourCellTargetSaturatedLiftDensity
      S hfineCutoff hcoarseCoupling)
    PositiveExpandedFourCellTargetSaturatedReceiverLift.receiver
    (slabObservableTwoReplicaPairWeight S.coarse)
    receiver

/-! ## 2. Positive-weight cancellation -/

/-- A density error bound is equivalent to the corresponding unnormalized
raw-mass error bound whenever the receiver weight is strictly positive. -/
private theorem densityCalibration_iff_rawMassCalibration_local
    (partitionDensity density weight rawMass relative : Q')
    (hweight : (0 : Q') < weight)
    (hdensityWeight : density * weight ≈ rawMass) :
    Q'.abs (partitionDensity - density) ≤
        relative * partitionDensity ↔
      Q'.abs (partitionDensity * weight - rawMass) ≤
        (relative * partitionDensity) * weight := by
  have hdiffMul :
      (partitionDensity - density) * weight ≈
        partitionDensity * weight - rawMass :=
    Q'.eqv_trans _
      (partitionDensity * weight - density * weight) _
      (Q'.sub_mul_eqv partitionDensity density weight)
      (sub_eqv_both_local (Q'.eqv_refl _)
        hdensityWeight)
  have habsDiffMul :
      Q'.abs ((partitionDensity - density) * weight) ≈
        Q'.abs (partitionDensity * weight - rawMass) :=
    YMGap.Constructive.Q'.abs_eqv_congr hdiffMul
  have habsMul :
      Q'.abs ((partitionDensity - density) * weight) ≈
        Q'.abs (partitionDensity - density) * weight :=
    YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
      (partitionDensity - density) (Q'.le_of_lt hweight)
  have hrawAbs :
      Q'.abs (partitionDensity * weight - rawMass) ≈
        Q'.abs (partitionDensity - density) * weight :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm habsDiffMul) habsMul
  constructor
  · intro hdensity
    have hscaled :=
      Q'.mul_le_mul_of_nonneg_right
        (Q'.abs (partitionDensity - density))
        (relative * partitionDensity) weight
        hdensity (Q'.le_of_lt hweight)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrawAbs) hscaled
  · intro hraw
    have hscaled :
        Q'.abs (partitionDensity - density) * weight ≤
          (relative * partitionDensity) * weight :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm hrawAbs)) hraw
    exact q_le_of_mul_le_mul_right
      (Q'.abs (partitionDensity - density))
      (relative * partitionDensity) weight hweight hscaled

/-! ## 3. Exact raw calibration seam -/

/-- The division-free analytic input: on every canonical source and target
receiver, the literal saturated pushforward raw mass is close to the physical
receiver mass prescribed by the fine/coarse partition ratio. -/
def PositiveExpandedAssignmentSaturatedRawMassCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (relative : Q') : Prop :=
  (∀ receiver,
    receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
    Q'.abs
        (positiveExpandedReceiverFiberPartitionDensity S *
            slabObservableTwoReplicaPairWeight S.coarse receiver -
          positiveExpandedFourCellSourceSaturatedReceiverFiberRawMass
            S hfineCutoff hcoarseCoupling root target receiver) ≤
      (relative * positiveExpandedReceiverFiberPartitionDensity S) *
        slabObservableTwoReplicaPairWeight S.coarse receiver) ∧
  (∀ receiver,
    receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
    Q'.abs
        (positiveExpandedReceiverFiberPartitionDensity S *
            slabObservableTwoReplicaPairWeight S.coarse receiver -
          positiveExpandedFourCellTargetSaturatedReceiverFiberRawMass
            S hfineCutoff hcoarseCoupling root target receiver) ≤
      (relative * positiveExpandedReceiverFiberPartitionDensity S) *
        slabObservableTwoReplicaPairWeight S.coarse receiver)

/-- The raw-mass and relative-density formulations are exactly equivalent;
strict receiver-weight positivity is the only cancellation input. -/
theorem positiveExpandedAssignmentSaturatedRawMassCalibration_iff_relativeDensityCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (relative : Q') :
    PositiveExpandedAssignmentSaturatedRawMassCalibration
        S hfineCutoff hcoarseCoupling root target relative ↔
      PositiveExpandedAssignmentSaturatedRelativeDensityCalibration
        S hfineCutoff hcoarseCoupling root target relative := by
  constructor
  · intro hraw
    constructor
    · intro receiver hreceiver
      exact
        (densityCalibration_iff_rawMassCalibration_local
          (positiveExpandedReceiverFiberPartitionDensity S)
          (positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver)
          (slabObservableTwoReplicaPairWeight S.coarse receiver)
          (positiveExpandedFourCellSourceSaturatedReceiverFiberRawMass
            S hfineCutoff hcoarseCoupling root target receiver)
          relative
          (slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
            S.coarse hcoarseCoupling receiver)
          (positiveExpandedFourCellSourceSaturatedReceiverFiberDensity_mul_weight_eqv_rawMass
            S hfineCutoff hcoarseCoupling root target receiver)).mpr
          (hraw.1 receiver hreceiver)
    · intro receiver hreceiver
      exact
        (densityCalibration_iff_rawMassCalibration_local
          (positiveExpandedReceiverFiberPartitionDensity S)
          (positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver)
          (slabObservableTwoReplicaPairWeight S.coarse receiver)
          (positiveExpandedFourCellTargetSaturatedReceiverFiberRawMass
            S hfineCutoff hcoarseCoupling root target receiver)
          relative
          (slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
            S.coarse hcoarseCoupling receiver)
          (positiveExpandedFourCellTargetSaturatedReceiverFiberDensity_mul_weight_eqv_rawMass
            S hfineCutoff hcoarseCoupling root target receiver)).mpr
          (hraw.2 receiver hreceiver)
  · intro hdensity
    constructor
    · intro receiver hreceiver
      exact
        (densityCalibration_iff_rawMassCalibration_local
          (positiveExpandedReceiverFiberPartitionDensity S)
          (positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver)
          (slabObservableTwoReplicaPairWeight S.coarse receiver)
          (positiveExpandedFourCellSourceSaturatedReceiverFiberRawMass
            S hfineCutoff hcoarseCoupling root target receiver)
          relative
          (slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
            S.coarse hcoarseCoupling receiver)
          (positiveExpandedFourCellSourceSaturatedReceiverFiberDensity_mul_weight_eqv_rawMass
            S hfineCutoff hcoarseCoupling root target receiver)).mp
          (hdensity.1 receiver hreceiver)
    · intro receiver hreceiver
      exact
        (densityCalibration_iff_rawMassCalibration_local
          (positiveExpandedReceiverFiberPartitionDensity S)
          (positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver)
          (slabObservableTwoReplicaPairWeight S.coarse receiver)
          (positiveExpandedFourCellTargetSaturatedReceiverFiberRawMass
            S hfineCutoff hcoarseCoupling root target receiver)
          relative
          (slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
            S.coarse hcoarseCoupling receiver)
          (positiveExpandedFourCellTargetSaturatedReceiverFiberDensity_mul_weight_eqv_rawMass
            S hfineCutoff hcoarseCoupling root target receiver)).mp
          (hdensity.2 receiver hreceiver)

/-! ## 4. Matched-AF schedule handoff -/

/-- Producer-facing matched-AF control whose receiver premise is stated
directly on the literal unnormalized raw pushforward mass.  Spacing and raw
event mismatch remain independent analytic fields. -/
structure MatchedShiftedAFSpinFourRawPushforwardQuadraticCostControl
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
  rawPushforwardQuadraticCeiling : Q'
  rawPushforwardQuadraticCeiling_pos :
    (0 : Q') < rawPushforwardQuadraticCeiling
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
  rawPushforward_quadratic : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    PositiveExpandedAssignmentSaturatedRawMassCalibration
      S rfl (schedule.effectiveCoupling_pos scale) root target
        (rawPushforwardQuadraticCeiling *
          (coupling scale * coupling scale))

namespace MatchedShiftedAFSpinFourRawPushforwardQuadraticCostControl

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

/-- The division-free raw producer compiles without loss to the existing
relative-density schedule control. -/
def toRelativeDensityQuadraticCostControl
    (control : MatchedShiftedAFSpinFourRawPushforwardQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :
    MatchedShiftedAFSpinFourRelativeDensityQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  relativeDensityQuadraticCeiling :=
    control.rawPushforwardQuadraticCeiling
  relativeDensityQuadraticCeiling_pos :=
    control.rawPushforwardQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  relativeDensity_quadratic := by
    intro scale hscale
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    exact
      (positiveExpandedAssignmentSaturatedRawMassCalibration_iff_relativeDensityCalibration
        S rfl (schedule.effectiveCoupling_pos scale) root target
        (control.rawPushforwardQuadraticCeiling *
          (coupling scale * coupling scale))).mp
        (control.rawPushforward_quadratic scale hscale)

/-- Final finite covariance consumer with the literal raw-pushforward
calibration as its receiver input. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (control : MatchedShiftedAFSpinFourRawPushforwardQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toRelativeDensityQuadraticCostControl.toCoveredVariationQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toRelativeDensityQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFSpinFourRawPushforwardQuadraticCostControl

#print axioms positiveExpandedFourCellSourceSaturatedReceiverFiberRawMass
#print axioms positiveExpandedFourCellSourceSaturatedReceiverFiberDensity_mul_weight_eqv_rawMass
#print axioms positiveExpandedFourCellTargetSaturatedReceiverFiberRawMass
#print axioms positiveExpandedFourCellTargetSaturatedReceiverFiberDensity_mul_weight_eqv_rawMass
#print axioms PositiveExpandedAssignmentSaturatedRawMassCalibration
#print axioms positiveExpandedAssignmentSaturatedRawMassCalibration_iff_relativeDensityCalibration
#print axioms MatchedShiftedAFSpinFourRawPushforwardQuadraticCostControl
#print axioms MatchedShiftedAFSpinFourRawPushforwardQuadraticCostControl.toRelativeDensityQuadraticCostControl
#print axioms MatchedShiftedAFSpinFourRawPushforwardQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.Z4DyadicSpinFourReceiverRawPushforwardCalibration
