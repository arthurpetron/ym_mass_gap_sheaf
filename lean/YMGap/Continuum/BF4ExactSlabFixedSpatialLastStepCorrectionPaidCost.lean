/-
Pay the reciprocal-gradient correction in the COMPLETE ORIGINAL signed cost.
Only fixed kinetic/spatial floors enter the partition payment; no terminal
mass or source norm is inverted.  All three approximation onsets depend
only on fixed nome, width and tolerances.  The remaining bulk keeps the
literal paired score and BOTH signed Taylor remainders.  Its useful bound
on a justified changing family, and the continuum/Clay goal, remain OPEN.
-/
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepDriftPaidCost
import YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity (spatialFloor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative kineticCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (transferStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound (transferWeightedCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_one_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (kineticCap_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
  (comparisonKappa comparisonKappa_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepDriftPaidCost
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headCutoff headFloor headFloor_positive)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight terminalMessage weightedMass

def lastStepPartitionFloor (w : Q') (width : Nat) : Q' :=
  kineticCap w width * spatialFloor w width

theorem lastStepPartitionFloor_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) :
    (0 : Q') < lastStepPartitionFloor w width :=
  Q'.mul_pos (kineticCap_positive hw0 hw1 width)
    (HKPos.pow_pos (headFloor_positive hw0 hw1) (spatialFaces width).length)

/-- Only an explicit fixed-parameter floor is inverted, not a partition. -/
def lastStepPartitionPaymentCap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) : Q' :=
  comparisonKappa hw0 hw1 width *
    Q'.recipPos (lastStepPartitionFloor w width) (lastStepPartitionFloor_positive hw0 hw1 width)

theorem lastStepPartitionPaymentCap_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) :
    (0 : Q') < lastStepPartitionPaymentCap hw0 hw1 width :=
  Q'.mul_pos (comparisonKappa_positive hw0 hw1 width) (Q'.recipPos_pos _ _)

/-- The already checked original partition/cap estimate supplies Z0<=P*Z1.
P has no cutoff or terminal-depth dependence, but is NOT scaling-uniform. -/
theorem original_block_partition_relative_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t) :
    let A := terminalMessage w K width (n+t)
    weightedMass w K width (polyMul A A) ≤
      lastStepPartitionPaymentCap hw0 hw1 width *
        weightedMass w K width (polyMul A (transferStep w K width A)) := by
  dsimp only
  let A := terminalMessage w K width (n+t)
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let F := lastStepPartitionFloor w width
  let R := Q'.recipPos F (lastStepPartitionFloor_positive hw0 hw1 width)
  let C := comparisonKappa hw0 hw1 width
  have hZ0 : (0 : Q') ≤ Z0 := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square A (terminalMessage_supported w K width (n+t)))
  have hlo : F ≤ transferWeightedCap w K width :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (weightedMass_one_floor hw0 hw1 K width hK)
      (Q'.le_of_lt (kineticCap_positive hw0 hw1 width))
  have h := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hlo hZ0)
    (block_partition_cap_le_comparisonKappa hw0 hw1 K width hK n t hdepth)
  have hr := Q'.mul_le_mul_of_nonneg_right _ _ R h
    (Q'.le_of_lt (Q'.recipPos_pos F (lastStepPartitionFloor_positive hw0 hw1 width)))
  have hl : (Z0*F)*R ≈ Z0 := Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv Z0 F R)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv F _))
      (Q'.mul_one_eqv Z0))
  have hu : (C*Z1)*R ≈ (C*R)*Z1 :=
    poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => C | 1 => Z1 | _ => R)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hr (Q'.le_of_eqv hu))

private def correctionBulkDivisor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) : Q' :=
  1+(1-w)*lastStepPartitionPaymentCap hw0 hw1 width

private theorem correctionBulkDivisor_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) :
    (0 : Q') < correctionBulkDivisor hw0 hw1 width :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
      (Q'.le_of_lt (lastStepPartitionPaymentCap_positive hw0 hw1 width))))

def correctionBulkTolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) (epsilon : Q') : Q' :=
  epsilon * Q'.recipPos (correctionBulkDivisor hw0 hw1 width)
    (correctionBulkDivisor_positive hw0 hw1 width)

theorem correctionBulkTolerance_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) {epsilon : Q'}
    (he : (0 : Q') < epsilon) : (0 : Q') < correctionBulkTolerance hw0 hw1 width epsilon :=
  Q'.mul_pos he (Q'.recipPos_pos _ _)

private theorem correctionBulkTolerance_payment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) {epsilon : Q'}
    (he : (0 : Q') < epsilon) :
    ((1-w)*lastStepPartitionPaymentCap hw0 hw1 width)*
      correctionBulkTolerance hw0 hw1 width epsilon ≤ epsilon := by
  let c := (1-w)*lastStepPartitionPaymentCap hw0 hw1 width
  let d := correctionBulkDivisor hw0 hw1 width
  let R := Q'.recipPos d (correctionBulkDivisor_positive hw0 hw1 width)
  have hcd : c ≤ d := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg c 1 Q'.zero_le_one) (Q'.le_of_eqv (Q'.add_comm_eqv c 1))
  have h := Q'.mul_le_mul_of_nonneg_right _ _ _ hcd
    (Q'.le_of_lt (correctionBulkTolerance_positive hw0 hw1 width he))
  have hp : d*(epsilon*R) ≈ epsilon :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => d | 1 => epsilon | _ => R))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_recipPos_eqv d (correctionBulkDivisor_positive hw0 hw1 width)))
        (Q'.mul_one_eqv epsilon))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hp)

def lastStepCorrectionPaidCostCutoff {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) (epsilon : Q') : Nat :=
  lastStepCorrectionPaidCutoff hw0 hw1 width (correctionBulkTolerance hw0 hw1 width epsilon)

/-- The remaining literal bulk: original paired score, SAME G and Vbar²,
and Rmixed-Rdiagonal.  Nothing in this definition assumes a useful bound. -/
def originalBlockLastStepPairedBulkBudget {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let q := projectedEndpointSource w K width A
  weightedMass w K width (polyMul A A) *
    ((1-w)*originalBlockLastStepPairedAngularBudget hw0 hw1 K width hK n r psi k +
      (pairRemainder (N width-1) w K q (polyMul q (polyMul phi phi)) +
        -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi))))

/-- The complete correction is paid in Z1*B, not an absolute error budget. -/
theorem original_block_lastStep_bulk_correction_paid {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat)
    (psi : RatPoly) (hp : SupportedQuaternionBlocks (N width) psi)
    {epsilon : Q'} (he : (0 : Q') < epsilon) (k : Nat)
    (hk : lastStepCorrectionPaidCostCutoff hw0 hw1 width epsilon ≤ k) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    originalBlockLastStepBulkBudget hw0 hw1 K width hK n r psi (k+1) ≤
      originalBlockLastStepPairedBulkBudget hw0 hw1 K width hK n r psi (k+1) +
        epsilon*(weightedMass w K width (polyMul A (transferStep w K width A))*
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B := weightedMass w K width (polyMul b b)
  let eta := correctionBulkTolerance hw0 hw1 width epsilon
  let P := lastStepPartitionPaymentCap hw0 hw1 width
  let s := 1-w
  let L := originalBlockLastStepPairedAngularBudget hw0 hw1 K width hK n r psi (k+1)
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
  let q := projectedEndpointSource w K width A
  let S := pairRemainder (N width-1) w K q (polyMul q (polyMul phi phi)) +
    -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi))
  have hA := terminalMessage_supported w K width (n+(r+1))
  have PA := terminalMessage_certificate hw0 hw1 K width hhead (n+(r+1))
  have hZ0 := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square A hA)
  have hZ1 : (0 : Q') ≤ Z1 := weightedMass_nonnegative hw0 hw1 K width hhead
    (PA.mul (transferStep_certificate hw0 hw1 K width hhead hA PA))
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (r+1)
    (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square _ hb)
  have hs : (0 : Q') ≤ s := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have heta := correctionBulkTolerance_positive hw0 hw1 width he
  have hang := original_block_lastStep_angularBudget_correction_paid
    hw0 hw1 K width hK n r psi hp heta k hk
  have h : originalBlockLastStepBulkBudget hw0 hw1 K width hK n r psi (k+1) ≤
      Z0*(s*(L+eta*B)+S) := Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.add_le_add_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hang hs)) hZ0
  have hexpand : Z0*(s*(L+eta*B)+S) ≈ (Z0*(s*L+S))+(s*Z0)*(eta*B) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.add (.var 2) (.mul (.var 3) (.var 4)))) (.var 5)))
      (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 5)))
        (.mul (.mul (.var 1) (.var 0)) (.mul (.var 3) (.var 4))))
      (by decide) (fun | 0 => Z0 | 1 => s | 2 => L | 3 => eta | 4 => B | _ => S)
  have hpart := original_block_partition_relative_le hw0 hw1 K width hhead n (r+1) (by omega)
  have herr := Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hpart hs)
    (Q'.mul_nonneg _ _ (Q'.le_of_lt heta) hB)
  have horder : (s*(P*Z1))*(eta*B) ≈ ((s*P)*eta)*(Z1*B) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 3) (.var 4)))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.var 2) (.var 4)))
      (by decide) (fun | 0 => s | 1 => P | 2 => Z1 | 3 => eta | _ => B)
  have hpay := Q'.mul_le_mul_of_nonneg_right _ _ _
    (correctionBulkTolerance_payment hw0 hw1 width he) (Q'.mul_nonneg _ _ hZ1 hB)
  exact Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand)
      (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ herr
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv horder) hpay))))

/-- Forward original-action estimates meet the backward SAME-norm cost
consumer.  Correction, drift and reconstruction have separate explicit
fixed-parameter onsets; the signed paired bulk is the remaining frontier. -/
theorem original_block_lastStep_correctionPaid_cost_relative_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (delta epsilon zeta : Q') (hd : (0 : Q') < delta)
    (he : (0 : Q') < epsilon) (hz : (0 : Q') < zeta)
    (hdepth : blockConditionalDriftDepthCutoff hw0 hw1 width delta ≤ n+(r+1)-1)
    (k : Nat) (hk : blockEnergyRelativeErrorCutoff hw0 hw1 width epsilon ≤ k+1)
    (hc : lastStepCorrectionPaidCostCutoff hw0 hw1 width zeta ≤ k) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    clearedRayleighCost w K width A b ≤
      originalBlockLastStepPairedBulkBudget hw0 hw1 K width hK n r psi (k+1) +
        ((zeta+delta)+epsilon)*(weightedMass w K width (polyMul A (transferStep w K width A))*
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  have h := original_block_lastStep_driftPaid_cost_relative_tolerance
    hw0 hw1 K width hK n r hN hp delta epsilon hd he hdepth (k+1) hk
  have hc' := original_block_lastStep_bulk_correction_paid hw0 hw1 K width hK n r psi hp hz k hc
  refine Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _ hc')) (Q'.le_of_eqv ?_))
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  exact poly_identity_of_normal_eq
    (.add (.add (.add (.var 0) (.mul (.var 1) (.mul (.var 4) (.var 5))))
      (.mul (.mul (.var 2) (.var 4)) (.var 5))) (.mul (.var 3) (.mul (.var 4) (.var 5))))
    (.add (.var 0) (.mul (.add (.add (.var 1) (.var 2)) (.var 3)) (.mul (.var 4) (.var 5))))
    (by decide) (fun
      | 0 => originalBlockLastStepPairedBulkBudget hw0 hw1 K width hK n r psi (k+1)
      | 1 => zeta | 2 => delta | 3 => epsilon
      | 4 => weightedMass w K width (polyMul A (transferStep w K width A))
      | _ => weightedMass w K width (polyMul b b))

#print axioms lastStepPartitionFloor
#print axioms lastStepPartitionFloor_positive
#print axioms lastStepPartitionPaymentCap
#print axioms lastStepPartitionPaymentCap_positive
#print axioms original_block_partition_relative_le
#print axioms correctionBulkTolerance
#print axioms correctionBulkTolerance_positive
#print axioms lastStepCorrectionPaidCostCutoff
#print axioms originalBlockLastStepPairedBulkBudget
#print axioms original_block_lastStep_bulk_correction_paid
#print axioms original_block_lastStep_correctionPaid_cost_relative_tolerance

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost
