/-
# Cancellation-preserving normalized coupling-one recentering

The raw coupling-one comparison changes both the pushed four-cell cross and
the fine partition.  Bounding those two changes separately exposes a global
partition-drift term and can erase cancellation before the analytic estimate
is made.  This module instead normalizes the coupling-one pushed cross by its
own partition and proves the exact identity

  unitNormalizedCross - actualBlockedCovariance
    = centeredChangeNumerator / (unitPartition^2 * actualPartition^2),

where the centered numerator is the normalized cross determinant

  unitCross * actualPartition^2
    - actualCross * unitPartition^2.

The cross loss and partition drift therefore remain inside one signed
quantity.  A second exact identity inserts the unit-normalized cross between
the coarse and actual covariances.  This yields a cancellation-preserving
producer seam for the centered cylinder remainder with two honest premises:
a unit-normalized blocking residual and a centered raw change numerator.

No quadratic estimate is proved here.  In particular, no volume-uniform
bound, cutoff limit, continuum measure, OS/GNS reconstruction, Hamiltonian
gap, or Yang--Mills mass gap is claimed.

Constructive contract: exact finite rational algebra and positive-denominator
division only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
import YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedRecentering

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

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

private theorem sub_insert_local (a b middle : Q') :
    a - b ≈ (a - middle) + (middle - b) := by
  change a + -b ≈ (a + -middle) + (middle + -b)
  apply Q'.eqv_symm
  refine Q'.eqv_trans _ (a + (-middle + (middle + -b))) _
    (Q'.add_assoc_eqv a (-middle) (middle + -b)) ?_
  refine Q'.eqv_trans _ (a + ((-middle + middle) + -b)) _
    (Q'.add_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle (-b)))) ?_
  refine Q'.eqv_trans _ (a + ((0 : Q') + -b)) _
    (Q'.add_eqv_congr_left a _ _
      (Q'.add_eqv_congr_right _ _ (-b)
        (Q'.neg_add_self_eqv middle))) ?_
  exact Q'.add_eqv_congr_left a _ _
    (Q'.eqv_of_eq (Q'.zero_add' (-b)))

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

private theorem abs_divPos_le_of_abs_le_mul_local
    {numerator denominator budget : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hraw : Q'.abs numerator ≤ budget * denominator) :
    Q'.abs (Q'.divPos numerator denominator hdenominator) ≤ budget := by
  apply Q'.abs_le
  · apply Q'.le_divPos_of_mul_le
    have hnegRaw := Q'.neg_le_neg hraw
    have hnegAbs : -(Q'.abs numerator) ≤ numerator := by
      have h := Q'.neg_le_neg (Q'.neg_le_abs numerator)
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.neg_neg_eqv numerator))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_mul_eqv budget denominator))
      (Q'.le_trans' _ _ _ hnegRaw hnegAbs)
  · apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self numerator) hraw

/-! ## 1. The coupling-one normalized pushed cross -/

/-- The literal coupling-one fine partition is strictly positive. -/
theorem fineUnitCouplingPhysicalPartition_pos (S : SlabScalePair) :
    (0 : Q') < fineUnitCouplingPhysicalPartition S := by
  unfold fineUnitCouplingPhysicalPartition
    fineUnitCouplingPhysicalTerm
    SlabPhysicalData.physicalLabellings
    SlabPhysicalData.faceEdges
  exact slabParametricKPhysicalPartition_pos
    (by decide : (0 : Q') ≤ (1 : Q')) S.fine.cutoff S.fine.extent

/-- Coupling-one pushed four-cell cross normalized by the coupling-one
partition square. -/
def fineUnitCouplingPushedNormalizedRawColumnCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  Q'.divPos
    (fineUnitCouplingPushedRawColumnCross K root target)
    (fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S)
    (Q'.mul_pos
      (fineUnitCouplingPhysicalPartition_pos S)
      (fineUnitCouplingPhysicalPartition_pos S))

/-- The actual blocked covariance is the actual pushed four-cell cross
divided by the actual fine partition square. -/
theorem blockedFaceCovariance_eqv_fourCell_divPos
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    blockedSlabFaceBooleanCovariance K M ≈
      Q'.divPos
        (pushedFaceRawFourCellCross
          K M.coarseRoot M.coarseTarget)
        (S.fine.physicalPartition * S.fine.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)) := by
  let partition := S.fine.physicalPartition
  let cross := pushedFaceRawFourCellCross
    K M.coarseRoot M.coarseTarget
  let cubic := pushedFaceRawCovarianceNumerator
    K M.coarseRoot M.coarseTarget
  have hpartition : (0 : Q') < partition := by
    simpa only [partition] using
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  have hsquare : (0 : Q') < partition * partition :=
    Q'.mul_pos hpartition hpartition
  have hcube : (0 : Q') < partition * (partition * partition) :=
    Q'.mul_pos hpartition hsquare
  have hcubic : cubic ≈ cross * partition := by
    simpa only [cubic, cross] using
      (pushedFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
        K M.coarseRoot M.coarseTarget)
  refine Q'.eqv_trans _
    (Q'.divPos cubic (partition * (partition * partition)) hcube) _ ?_ ?_
  · simpa only [cubic, partition, rawCovarianceDenominator] using
      (blockedFaceCovariance_eqv_raw_divPos K M)
  refine Q'.eqv_trans _
    (Q'.divPos cross (partition * partition) hsquare) _ ?_ ?_
  · apply divPos_eqv_of_eqv_mul_local hcube
    refine Q'.eqv_trans _ (cross * partition) _ hcubic ?_
    apply Q'.eqv_symm
    refine Q'.eqv_trans _
      ((Q'.divPos cross (partition * partition) hsquare *
          (partition * partition)) * partition) _ ?_ ?_
    · ring_qeqv
    · exact Q'.mul_eqv_congr_right _ _ partition
        (Q'.divPos_mul_eqv cross (partition * partition) hsquare)
  · exact Q'.eqv_refl _

/-! ## 2. One signed numerator for cross and normalization change -/

/-- Cancellation-preserving cross determinant for the normalized change from
the coupling-one pushed law to the actual pushed law.  Cross loss and global
partition drift are intentionally not bounded separately. -/
def fineUnitCouplingCenteredNormalizedChangeNumerator
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  let actualSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  let unitCross := fineUnitCouplingPushedRawColumnCross K root target
  let actualCross := pushedFaceRawFourCellCross K root target
  unitCross * actualSquare - actualCross * unitSquare

/-- Positive common denominator for the normalized centered change. -/
def fineUnitCouplingCenteredNormalizedChangeDenominator
    (S : SlabScalePair) : Q' :=
  (fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S) *
    (S.fine.physicalPartition * S.fine.physicalPartition)

theorem fineUnitCouplingCenteredNormalizedChangeDenominator_pos
    (S : SlabScalePair) :
    (0 : Q') < fineUnitCouplingCenteredNormalizedChangeDenominator S := by
  unfold fineUnitCouplingCenteredNormalizedChangeDenominator
  exact Q'.mul_pos
    (Q'.mul_pos
      (fineUnitCouplingPhysicalPartition_pos S)
      (fineUnitCouplingPhysicalPartition_pos S))
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))

/-- Exact normalized change-of-measure identity.  The two raw changes cancel
inside the numerator before any absolute value is taken. -/
theorem fineUnitCouplingPushedNormalizedRawColumnCross_sub_actual_eqv_centeredChange
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineUnitCouplingPushedNormalizedRawColumnCross K root target -
        Q'.divPos
          (pushedFaceRawFourCellCross K root target)
          (S.fine.physicalPartition * S.fine.physicalPartition)
          (Q'.mul_pos
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)) ≈
      Q'.divPos
        (fineUnitCouplingCenteredNormalizedChangeNumerator
          K root target)
        (fineUnitCouplingCenteredNormalizedChangeDenominator S)
        (fineUnitCouplingCenteredNormalizedChangeDenominator_pos S) := by
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  let actualSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let unitCross := fineUnitCouplingPushedRawColumnCross K root target
  let actualCross := pushedFaceRawFourCellCross K root target
  have hunitSquare : (0 : Q') < unitSquare :=
    Q'.mul_pos
      (fineUnitCouplingPhysicalPartition_pos S)
      (fineUnitCouplingPhysicalPartition_pos S)
  have hactualSquare : (0 : Q') < actualSquare :=
    Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  have hdenominator : (0 : Q') < unitSquare * actualSquare :=
    Q'.mul_pos hunitSquare hactualSquare
  change
    Q'.divPos unitCross unitSquare hunitSquare -
        Q'.divPos actualCross actualSquare hactualSquare ≈
      Q'.divPos
        (unitCross * actualSquare - actualCross * unitSquare)
        (unitSquare * actualSquare) hdenominator
  exact divPos_sub_divPos_eq_crossDifference
    unitCross actualCross unitSquare actualSquare
      hunitSquare hactualSquare

theorem fineUnitCouplingPushedNormalizedRawColumnCross_sub_blocked_eqv_centeredChange
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    fineUnitCouplingPushedNormalizedRawColumnCross
          K M.coarseRoot M.coarseTarget -
        blockedSlabFaceBooleanCovariance K M ≈
      Q'.divPos
        (fineUnitCouplingCenteredNormalizedChangeNumerator
          K M.coarseRoot M.coarseTarget)
        (fineUnitCouplingCenteredNormalizedChangeDenominator S)
        (fineUnitCouplingCenteredNormalizedChangeDenominator_pos S) := by
  refine Q'.eqv_trans _
    (fineUnitCouplingPushedNormalizedRawColumnCross
          K M.coarseRoot M.coarseTarget -
      Q'.divPos
        (pushedFaceRawFourCellCross
          K M.coarseRoot M.coarseTarget)
        (S.fine.physicalPartition * S.fine.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))) _ ?_ ?_
  · exact sub_eqv_both_local (Q'.eqv_refl _)
      (blockedFaceCovariance_eqv_fourCell_divPos K M)
  · exact
      fineUnitCouplingPushedNormalizedRawColumnCross_sub_actual_eqv_centeredChange
        K M.coarseRoot M.coarseTarget

/-! ## 3. Exact centered-remainder split and quantitative interface -/

/-- Insert the unit-normalized pushed law between the coarse and actual
blocked covariances. -/
theorem centeredCylinderRemainder_eqv_unitNormalizedResidual_add_centeredChange
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    centeredCylinderRemainder K M ≈
      (normalizedSlabFaceBooleanCovariance
          S.coarse M.coarseRoot M.coarseTarget -
        fineUnitCouplingPushedNormalizedRawColumnCross
          K M.coarseRoot M.coarseTarget) +
      Q'.divPos
        (fineUnitCouplingCenteredNormalizedChangeNumerator
          K M.coarseRoot M.coarseTarget)
        (fineUnitCouplingCenteredNormalizedChangeDenominator S)
        (fineUnitCouplingCenteredNormalizedChangeDenominator_pos S) := by
  let coarse := normalizedSlabFaceBooleanCovariance
    S.coarse M.coarseRoot M.coarseTarget
  let unit := fineUnitCouplingPushedNormalizedRawColumnCross
    K M.coarseRoot M.coarseTarget
  let actual := blockedSlabFaceBooleanCovariance K M
  refine Q'.eqv_trans _ (coarse - actual) _ ?_ ?_
  · exact Q'.eqv_symm
      (coarse_sub_blocked_covariance_eqv_centeredCylinderRemainder K M)
  refine Q'.eqv_trans _ ((coarse - unit) + (unit - actual)) _
    (sub_insert_local coarse actual unit) ?_
  exact Q'.add_eqv_congr_left (coarse - unit) _ _
    (fineUnitCouplingPushedNormalizedRawColumnCross_sub_blocked_eqv_centeredChange
      K M)

/-- Quadratic calibration of the unit-normalized blocking residual. -/
def FineUnitCouplingNormalizedBlockingResidualCalibration
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (g referenceCeiling : Q') : Prop :=
  Q'.abs
      (normalizedSlabFaceBooleanCovariance
          S.coarse M.coarseRoot M.coarseTarget -
        fineUnitCouplingPushedNormalizedRawColumnCross
          K M.coarseRoot M.coarseTarget) ≤
    referenceCeiling * (g * g)

/-- Raw quadratic calibration of the single signed centered-change
numerator.  This premise preserves cancellation between cross loss and
partition drift. -/
def FineUnitCouplingCenteredNormalizedChangeRawCalibration
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (g changeCeiling : Q') : Prop :=
  Q'.abs
      (fineUnitCouplingCenteredNormalizedChangeNumerator
        K M.coarseRoot M.coarseTarget) ≤
    (changeCeiling * (g * g)) *
      fineUnitCouplingCenteredNormalizedChangeDenominator S

/-- The two cancellation-preserving normalized premises imply the preferred
quadratic estimate on the centered cylinder remainder. -/
theorem centeredCylinderRemainder_abs_le_of_unitNormalizedResidual_and_centeredChange
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (g referenceCeiling changeCeiling : Q')
    (hreference :
      FineUnitCouplingNormalizedBlockingResidualCalibration
        K M g referenceCeiling)
    (hchange :
      FineUnitCouplingCenteredNormalizedChangeRawCalibration
        K M g changeCeiling) :
    Q'.abs (centeredCylinderRemainder K M) ≤
      (referenceCeiling + changeCeiling) * (g * g) := by
  let reference :=
    normalizedSlabFaceBooleanCovariance
        S.coarse M.coarseRoot M.coarseTarget -
      fineUnitCouplingPushedNormalizedRawColumnCross
        K M.coarseRoot M.coarseTarget
  let change := Q'.divPos
    (fineUnitCouplingCenteredNormalizedChangeNumerator
      K M.coarseRoot M.coarseTarget)
    (fineUnitCouplingCenteredNormalizedChangeDenominator S)
    (fineUnitCouplingCenteredNormalizedChangeDenominator_pos S)
  have hchangeBound : Q'.abs change ≤ changeCeiling * (g * g) := by
    apply abs_divPos_le_of_abs_le_mul_local
      (fineUnitCouplingCenteredNormalizedChangeDenominator_pos S)
    simpa only [change,
      FineUnitCouplingCenteredNormalizedChangeRawCalibration] using hchange
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (centeredCylinderRemainder_eqv_unitNormalizedResidual_add_centeredChange
          K M))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le' reference change) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add hreference hchangeBound) ?_
  exact Q'.le_of_eqv (by ring_qeqv)

#print axioms fineUnitCouplingPhysicalPartition_pos
#print axioms fineUnitCouplingPushedNormalizedRawColumnCross
#print axioms blockedFaceCovariance_eqv_fourCell_divPos
#print axioms fineUnitCouplingCenteredNormalizedChangeNumerator
#print axioms fineUnitCouplingPushedNormalizedRawColumnCross_sub_actual_eqv_centeredChange
#print axioms fineUnitCouplingPushedNormalizedRawColumnCross_sub_blocked_eqv_centeredChange
#print axioms centeredCylinderRemainder_eqv_unitNormalizedResidual_add_centeredChange
#print axioms FineUnitCouplingNormalizedBlockingResidualCalibration
#print axioms FineUnitCouplingCenteredNormalizedChangeRawCalibration
#print axioms centeredCylinderRemainder_abs_le_of_unitNormalizedResidual_and_centeredChange

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedRecentering
