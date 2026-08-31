/-
# Aggregate guarded floor as a same-object face contraction

The guarded reflected-bent construction supplies a cutoff-independent lower
bound on the complete opposite determinant cell `10 x 01`.  This file turns
that two-replica statement into a one-replica transition floor and then into
a relative form bound for the literal centered reflected-face indicator.

The conclusion concerns one explicit centered observable at the fixed anchor
coupling, slab half-width two, and every positive representation cutoff.  It
is not an all-vector form gap, an operator-norm estimate, spacing or volume
uniformity, a continuum limit, or a Clay theorem.

Constructive contract: exact finite `Q'` algebra, nonnegative filter
domination, and the existing physical same-object/variance bridges only.  No
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableFaceVarianceBridge
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateRetainedFloor
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRetainedContraction

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectContraction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservableFaceVarianceBridge
open YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedRowPartition
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateRetainedFloor
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRetainedContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem one_add_neg_lt_one_of_pos {epsilon : Q'}
    (hpositive : (0 : Q') < epsilon) :
    (1 : Q') + (-epsilon) < (1 : Q') := by
  show ((1 : Q') + -epsilon).num * ((1 : Q').den : Int) <
    (1 : Q').num * (((1 : Q') + -epsilon).den : Int)
  have hnum : (0 : Int) < epsilon.num := Q'.num_pos_of_pos hpositive
  change
    (((1 : Int) * (epsilon.den : Int) + (-epsilon.num) * (1 : Int)) *
      (1 : Int)) <
      ((1 : Int) * (((1 : Nat) * epsilon.den : Nat) : Int))
  push_cast
  omega

private theorem one_sub_mul_eqv
    (rate value : Q') :
    ((1 : Q') + -rate) * value ≈ value + -(rate * value) := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv (1 : Q') (-rate) value)
    (Q'.add_eqv_congr'
      (Q'.one_mul_eqv value)
      (Q'.neg_mul_eqv rate value))

private theorem factors_mul_le_total_sq
    (left right total : Q')
    (hleft : (0 : Q') ≤ left) (hright : (0 : Q') ≤ right)
    (hsplit : total ≈ left + right) :
    left * right ≤ total * total := by
  have hleftTotal : left ≤ total :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg left right hright)
      (Q'.ge_of_eqv hsplit)
  have hrightTotal : right ≤ total := by
    have hadd : right ≤ left + right := by
      have h := Q'.add_le_add_right (0 : Q') left right hleft
      rwa [Q'.zero_add'] at h
    exact Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hsplit)
  have htotal : (0 : Q') ≤ total :=
    Q'.le_trans' _ _ _ hleft hleftTotal
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ right hleftTotal hright)
    (Q'.mul_le_mul_of_nonneg_left _ _ total hrightTotal htotal)

/-! ## 1. The exact one-replica off-diagonal floor -/

/-- The second factor of the opposite determinant cell is an event mass and
therefore cannot exceed the complete one-replica partition. -/
theorem reflectedBentGuardRootComplementTargetMass_le_partition
    (cutoff : Nat) :
    listQSum
        (slabExpandedFineEntryWeight (anchorSlabPhysicalData cutoff 2))
        (slabObservableRootComplementTargetEntries
          (anchorSlabPhysicalData cutoff 2)
          reflectedBentRootFaceId reflectedBentTargetFaceId) ≤
      (anchorSlabPhysicalData cutoff 2).physicalPartition := by
  let D := anchorSlabPhysicalData cutoff 2
  have hnonnegative : ∀ source,
      (0 : Q') ≤ slabExpandedFineSourceWeight D source := by
    intro source
    exact slabObservableExpandedFineSourceWeight_nonnegative D source
  have hfilter := listQSum_filter_le
    (slabExpandedFineSourceWeight D)
    (fun source =>
      !(slabObservableRawFacePositiveB reflectedBentRootFaceId source) &&
        slabObservableRawFacePositiveB reflectedBentTargetFaceId source)
    hnonnegative (slabExpandedFineSources D)
  have hcell := slabObservableRootComplementTargetEntries_weight_eqv_FT
    D reflectedBentRootFaceId reflectedBentTargetFaceId
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hcell)
    (Q'.le_trans' _ _ _ hfilter
      (Q'.le_of_eqv (slabExpandedFineSources_weight_total D)))

/-- The first factor of the opposite determinant cell is nonnegative. -/
theorem reflectedBentGuardRootTargetComplementMass_nonnegative
    (cutoff : Nat) :
    (0 : Q') ≤
      listQSum
        (slabObservablePositiveEntryWeight
          (anchorSlabPhysicalData cutoff 2))
        (slabObservableRootTargetComplementEntries
          (anchorSlabPhysicalData cutoff 2)
          reflectedBentRootFaceId reflectedBentTargetFaceId) := by
  exact listQSum_nonnegative_on _ _
    (fun entry _ => slabObservablePositiveEntryWeight_nonnegative
      (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId entry)

/-- The two-replica determinant-cell floor cancels one positive partition
factor.  Thus the one-replica `root positive, reflected target zero` event has
mass at least the same fixed rate times the partition. -/
theorem reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_le_rootTargetComplement
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    reflectedBentGuardScaledSeparatedTransitionRate *
        (anchorSlabPhysicalData cutoff 2).physicalPartition ≤
      listQSum
        (slabObservablePositiveEntryWeight
          (anchorSlabPhysicalData cutoff 2))
        (slabObservableRootTargetComplementEntries
          (anchorSlabPhysicalData cutoff 2)
          reflectedBentRootFaceId reflectedBentTargetFaceId) := by
  let D := anchorSlabPhysicalData cutoff 2
  let rate := reflectedBentGuardScaledSeparatedTransitionRate
  let first := listQSum (slabObservablePositiveEntryWeight D)
    (slabObservableRootTargetComplementEntries
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
  let second := listQSum (slabExpandedFineEntryWeight D)
    (slabObservableRootComplementTargetEntries
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
  let partition := D.physicalPartition
  have hfloor :=
    reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_sq_le_targetCell
      cutoff hcutoff
  have hproduct := slabObservableFourCellTargetPairs_weight_product
    D reflectedBentRootFaceId reflectedBentTargetFaceId
  have hfloorProduct : rate * (partition * partition) ≤ first * second :=
    Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv hproduct)
  have hsecond : second ≤ partition := by
    simpa only [D, second, partition] using
      (reflectedBentGuardRootComplementTargetMass_le_partition cutoff)
  have hfirstNonnegative : (0 : Q') ≤ first := by
    simpa only [D, first] using
      (reflectedBentGuardRootTargetComplementMass_nonnegative cutoff)
  have htoPartition : first * second ≤ first * partition :=
    Q'.mul_le_mul_of_nonneg_left _ _ first hsecond hfirstNonnegative
  have hright : (rate * partition) * partition ≤ first * partition :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_assoc_eqv rate partition partition))
      (Q'.le_trans' _ _ _ hfloorProduct htoPartition)
  have hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hcancel : partition * (rate * partition) ≤ partition * first :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv partition (rate * partition)))
      (Q'.le_trans' _ _ _ hright
        (Q'.le_of_eqv (Q'.mul_comm_eqv first partition)))
  exact Q'.le_of_mul_le_mul_left hcancel hpartition

/-! ## 2. A genuine fixed contraction factor -/

/-- Residual factor left after spending the uniform off-diagonal floor. -/
def reflectedBentGuardAggregateSameObjectContractionFactor : Q' :=
  (1 : Q') + -reflectedBentGuardScaledSeparatedTransitionRate

theorem reflectedBentGuardScaledSeparatedTransitionRate_le_one :
    reflectedBentGuardScaledSeparatedTransitionRate ≤ (1 : Q') := by
  let D := anchorSlabPhysicalData 1 2
  have hfloor :=
    reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_le_rootTargetComplement
      1 (by decide)
  have hfirst :
      listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetComplementEntries
            D reflectedBentRootFaceId reflectedBentTargetFaceId) ≤
        D.physicalPartition := by
    let states := slabExpandedFineSources D
    let weight := slabExpandedFineSourceWeight D
    let root := slabObservableRawFacePositiveB reflectedBentRootFaceId
    let target := slabObservableRawFacePositiveB reflectedBentTargetFaceId
    have hnonnegative : ∀ source, (0 : Q') ≤ weight source := by
      intro source
      exact slabObservableExpandedFineSourceWeight_nonnegative D source
    have hfilter := listQSum_filter_le weight
      (fun source => root source && !(target source))
      hnonnegative states
    have hcell := slabObservableRootTargetComplementEntries_weight_eqv_TF
      D reflectedBentRootFaceId reflectedBentTargetFaceId
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hcell)
      (Q'.le_trans' _ _ _ hfilter
        (Q'.le_of_eqv (slabExpandedFineSources_weight_total D)))
  have hscaled :
      reflectedBentGuardScaledSeparatedTransitionRate * D.physicalPartition ≤
        (1 : Q') * D.physicalPartition :=
    Q'.le_trans' _ _ _ hfloor
      (Q'.le_trans' _ _ _ hfirst
        (Q'.ge_of_eqv (Q'.one_mul_eqv D.physicalPartition)))
  have hpartition : (0 : Q') < D.physicalPartition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hcancel :
      D.physicalPartition * reflectedBentGuardScaledSeparatedTransitionRate ≤
        D.physicalPartition * (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv D.physicalPartition
          reflectedBentGuardScaledSeparatedTransitionRate))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv
          (Q'.mul_comm_eqv (1 : Q') D.physicalPartition)))
  exact Q'.le_of_mul_le_mul_left hcancel hpartition

theorem reflectedBentGuardAggregateSameObjectContractionFactor_nonnegative :
    (0 : Q') ≤ reflectedBentGuardAggregateSameObjectContractionFactor := by
  exact Q'.sub_nonneg_of_le
    reflectedBentGuardScaledSeparatedTransitionRate_le_one

theorem reflectedBentGuardAggregateSameObjectContractionFactor_lt_one :
    reflectedBentGuardAggregateSameObjectContractionFactor < (1 : Q') := by
  exact one_add_neg_lt_one_of_pos
    reflectedBentGuardScaledSeparatedTransitionRate_pos

/-! ## 3. The determinant deficit is relative to the face variance -/

theorem reflectedBentGuardRootTargetMass_le_positiveMass
    (cutoff : Nat) :
    listQSum
        (slabObservablePositiveEntryWeight
          (anchorSlabPhysicalData cutoff 2))
        (slabObservableRootTargetEntries
          (anchorSlabPhysicalData cutoff 2)
          reflectedBentRootFaceId reflectedBentTargetFaceId) ≤
      slabObservablePositiveSourceWeight
        (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId := by
  let D := anchorSlabPhysicalData cutoff 2
  have hfilter := listQSum_filter_le
    (slabObservablePositiveEntryWeight D)
    (fun entry =>
      SlabObservablePositiveSourceEntry.facePositiveB
        entry reflectedBentTargetFaceId)
    (fun entry => slabObservablePositiveEntryWeight_nonnegative
      D reflectedBentRootFaceId entry)
    (slabObservablePositiveSourceEntries D reflectedBentRootFaceId)
  have htotal :
      listQSum (slabObservablePositiveEntryWeight D)
          (slabObservablePositiveSourceEntries D reflectedBentRootFaceId) =
        slabObservablePositiveSourceWeight D reflectedBentRootFaceId := by
    unfold slabObservablePositiveSourceEntries
      slabObservablePositiveEntryWeight slabObservablePositiveSourceWeight
    exact listQSum_attach
      (slabExpandedFineSourceWeight D)
      (slabObservablePositiveExpandedSources D reflectedBentRootFaceId)
  simpa only [D, slabObservableRootTargetEntries, htotal] using hfilter

theorem reflectedBentGuardRootComplementTargetComplementMass_le_rootZeroMass
    (cutoff : Nat) :
    listQSum
        (slabExpandedFineEntryWeight (anchorSlabPhysicalData cutoff 2))
        (slabObservableRootComplementTargetComplementEntries
          (anchorSlabPhysicalData cutoff 2)
          reflectedBentRootFaceId reflectedBentTargetFaceId) ≤
      slabObservableExpandedRootZeroMass
        (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId := by
  let D := anchorSlabPhysicalData cutoff 2
  let states := slabExpandedFineSources D
  let weight := slabExpandedFineSourceWeight D
  let root := slabObservableRawFacePositiveB reflectedBentRootFaceId
  let target := slabObservableRawFacePositiveB reflectedBentTargetFaceId
  have hnonnegative : ∀ source, (0 : Q') ≤ weight source := by
    intro source
    exact slabObservableExpandedFineSourceWeight_nonnegative D source
  have hfilter := listQSum_filter_le_filter weight
    (fun source => !(root source) && !(target source))
    (fun source => !(root source)) hnonnegative
    (fun source hsource => by
      cases hroot : root source with
      | false => simp [hroot]
      | true => simp [hroot] at hsource)
    states
  have hcell :=
    slabObservableRootComplementTargetComplementEntries_weight_eqv_FF
      D reflectedBentRootFaceId reflectedBentTargetFaceId
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hcell)
    (by simpa only [finiteWeightedFF, finiteWeightedEventMass,
        slabObservableExpandedRootZeroMass, states, weight, root, target]
      using hfilter)

theorem reflectedBentGuardPositiveMulRootZero_le_partitionSq
    (cutoff : Nat) :
    slabObservablePositiveSourceWeight
          (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId *
        slabObservableExpandedRootZeroMass
          (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId ≤
      (anchorSlabPhysicalData cutoff 2).physicalPartition *
        (anchorSlabPhysicalData cutoff 2).physicalPartition := by
  let D := anchorSlabPhysicalData cutoff 2
  let positive := slabObservablePositiveSourceWeight
    D reflectedBentRootFaceId
  let zero := slabObservableExpandedRootZeroMass
    D reflectedBentRootFaceId
  let partition := D.physicalPartition
  have hpositiveNonnegative : (0 : Q') ≤ positive := by
    unfold positive slabObservablePositiveSourceWeight
    exact listQSum_nonnegative_on _ _
      (fun source _ =>
        slabObservableExpandedFineSourceWeight_nonnegative D source)
  have hzeroNonnegative : (0 : Q') ≤ zero := by
    unfold zero slabObservableExpandedRootZeroMass finiteWeightedEventMass
    exact listQSum_nonnegative_on _ _
      (fun source _ =>
        slabObservableExpandedFineSourceWeight_nonnegative D source)
  exact factors_mul_le_total_sq positive zero partition
    hpositiveNonnegative hzeroNonnegative
    (slabExpandedPartition_eqv_rootPositive_add_zero
      D reflectedBentRootFaceId)

/-- The uniform opposite-cell floor improves the reflected four-cell excess
by the same fixed factor relative to the root-face variance. -/
theorem reflectedBentGuardNormalizedFourCellExcess_le_factor_mul_variance
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    slabObservableNormalizedFourCellExcess
        (anchorSlabPhysicalData cutoff 2)
        reflectedBentRootFaceId reflectedBentTargetFaceId ≤
      reflectedBentGuardAggregateSameObjectContractionFactor *
        slabObservableFaceBooleanCovariance
          (anchorSlabPhysicalData cutoff 2)
          reflectedBentRootFaceId reflectedBentRootFaceId := by
  let D := anchorSlabPhysicalData cutoff 2
  let rate := reflectedBentGuardScaledSeparatedTransitionRate
  let factor := reflectedBentGuardAggregateSameObjectContractionFactor
  let positive := slabObservablePositiveSourceWeight
    D reflectedBentRootFaceId
  let zero := slabObservableExpandedRootZeroMass
    D reflectedBentRootFaceId
  let source :=
    listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetEntries
            D reflectedBentRootFaceId reflectedBentTargetFaceId) *
      listQSum (slabExpandedFineEntryWeight D)
        (slabObservableRootComplementTargetComplementEntries
          D reflectedBentRootFaceId reflectedBentTargetFaceId)
  let target :=
    listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetComplementEntries
            D reflectedBentRootFaceId reflectedBentTargetFaceId) *
      listQSum (slabExpandedFineEntryWeight D)
        (slabObservableRootComplementTargetEntries
          D reflectedBentRootFaceId reflectedBentTargetFaceId)
  let partitionSq := D.physicalPartition * D.physicalPartition
  have hsourceFirst := reflectedBentGuardRootTargetMass_le_positiveMass cutoff
  have hsourceSecond :=
    reflectedBentGuardRootComplementTargetComplementMass_le_rootZeroMass cutoff
  have hsecondNonnegative : (0 : Q') ≤
      listQSum (slabExpandedFineEntryWeight D)
        (slabObservableRootComplementTargetComplementEntries
          D reflectedBentRootFaceId reflectedBentTargetFaceId) := by
    exact listQSum_nonnegative_on _ _
      (fun entry _ => slabExpandedFineEntryWeight_nonnegative D entry)
  have hpositiveNonnegative : (0 : Q') ≤ positive := by
    unfold positive slabObservablePositiveSourceWeight
    exact listQSum_nonnegative_on _ _
      (fun state _ =>
        slabObservableExpandedFineSourceWeight_nonnegative D state)
  have hsource : source ≤ positive * zero := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hsourceFirst
        hsecondNonnegative)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hsourceSecond
        hpositiveNonnegative)
  have htarget : rate * partitionSq ≤ target := by
    have hfloor :=
      reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_sq_le_targetCell
        cutoff hcutoff
    have hproduct := slabObservableFourCellTargetPairs_weight_product
      D reflectedBentRootFaceId reflectedBentTargetFaceId
    exact Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv hproduct)
  have hraw : source + -target ≤
      positive * zero + -(rate * partitionSq) :=
    Q'.add_le_add hsource (Q'.neg_le_neg htarget)
  have hpositiveZero :=
    reflectedBentGuardPositiveMulRootZero_le_partitionSq cutoff
  have hrateNonnegative : (0 : Q') ≤ rate :=
    Q'.le_of_lt reflectedBentGuardScaledSeparatedTransitionRate_pos
  have hrateScaled : rate * (positive * zero) ≤ rate * partitionSq :=
    Q'.mul_le_mul_of_nonneg_left _ _ rate hpositiveZero hrateNonnegative
  have hfactorRaw : source + -target ≤ factor * (positive * zero) := by
    exact Q'.le_trans' _ _ _ hraw
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left (positive * zero) _ _
          (Q'.neg_le_neg hrateScaled))
        (Q'.ge_of_eqv (by
          unfold factor
          exact one_sub_mul_eqv rate (positive * zero))))
  have hpartition : (0 : Q') < D.physicalPartition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hpartitionSq : (0 : Q') < partitionSq :=
    Q'.mul_pos hpartition hpartition
  have hvariance := slabObservableFaceVariance_eqv_rootPositive_mul_zero
    D reflectedBentRootFaceId
  unfold slabObservableNormalizedFourCellExcess
  apply Q'.divPos_le_of_le_mul
  have hrecover :
      (factor *
          slabObservableFaceBooleanCovariance
            D reflectedBentRootFaceId reflectedBentRootFaceId) *
          partitionSq ≈
        factor * (positive * zero) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ partitionSq
        (Q'.mul_eqv_congr_left factor _ _ hvariance))
      (Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv factor
          (Q'.divPos (positive * zero) partitionSq hpartitionSq)
          partitionSq)
        (Q'.mul_eqv_congr_left factor _ _
          (Q'.divPos_mul_eqv
            (positive * zero) partitionSq hpartitionSq)))
  exact Q'.le_trans' _ _ _ hfactorRaw (Q'.ge_of_eqv hrecover)

/-! ## 4. Same-object finite form contraction -/

theorem reflectedBentGuardFaceBooleanCovariance_le_factor_mul_variance
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    slabObservableFaceBooleanCovariance
        (anchorSlabPhysicalData cutoff 2)
        reflectedBentRootFaceId reflectedBentTargetFaceId ≤
      reflectedBentGuardAggregateSameObjectContractionFactor *
        slabObservableFaceBooleanCovariance
          (anchorSlabPhysicalData cutoff 2)
          reflectedBentRootFaceId reflectedBentRootFaceId := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (slabObservableFaceBooleanCovariance_eqv_normalizedFourCellExcess
        (anchorSlabPhysicalData cutoff 2)
        reflectedBentRootFaceId reflectedBentTargetFaceId))
    (reflectedBentGuardNormalizedFourCellExcess_le_factor_mul_variance
      cutoff hcutoff)

/-- **Cutoff-uniform same-object face-vector form contraction.**  The literal
centered lower-face indicator contracts under the genuine physical Markov
operator by one fixed rational factor strictly below one, for every positive
representation cutoff at the anchor coupling and fixed slab half-width two. -/
theorem reflectedBentGuardSameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment
        (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId ≤
      reflectedBentGuardAggregateSameObjectContractionFactor *
        centralPhysicalWeightedInner
          (anchorSlabPhysicalData cutoff 2).coupling
          (anchorSlabPhysicalData cutoff 2).coupling_nonnegative
          (anchorSlabPhysicalData cutoff 2).cutoff
          (anchorSlabPhysicalData cutoff 2).half
          (centralPhysicalCenteredObservable
            (anchorSlabPhysicalData cutoff 2).coupling
            (anchorSlabPhysicalData cutoff 2).coupling_nonnegative
            (anchorSlabPhysicalData cutoff 2).cutoff
            (anchorSlabPhysicalData cutoff 2).half
            (slabPhysicalFacePositiveUnitObservable
              reflectedBentRootFaceId).value)
          (centralPhysicalCenteredObservable
            (anchorSlabPhysicalData cutoff 2).coupling
            (anchorSlabPhysicalData cutoff 2).coupling_nonnegative
            (anchorSlabPhysicalData cutoff 2).cutoff
            (anchorSlabPhysicalData cutoff 2).half
            (slabPhysicalFacePositiveUnitObservable
              reflectedBentRootFaceId).value) := by
  let D := anchorSlabPhysicalData cutoff 2
  have hroot : reflectedBentRootFaceId ∈ centralLowerFaceIds D.half :=
    reflectedBentRootFaceId_lower_at_extent D rfl
  have hreflect : reflectedBentTargetFaceId =
      slabFaceReflectId D.extent reflectedBentRootFaceId :=
    reflectedBentTargetFaceId_eq_reflect_at_extent D rfl
  have hsame := slabPhysicalReflectedFaceBooleanCovariance_eqv_sameObject
    D hroot
  have hphysical := slabObservableFaceBooleanCovariance_eqv_physical
    D reflectedBentRootFaceId reflectedBentTargetFaceId
  have hleft :
      slabPhysicalFaceSameObjectConnectedMarkovMoment
          D reflectedBentRootFaceId ≈
        slabObservableFaceBooleanCovariance
          D reflectedBentRootFaceId reflectedBentTargetFaceId := by
    rw [hreflect]
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsame) (Q'.eqv_symm hphysical)
  have hnorm := centralPhysicalCenteredFaceObservable_norm_eqv_variance
    D hroot
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _
      (by simpa only [D] using
        (reflectedBentGuardFaceBooleanCovariance_le_factor_mul_variance
          cutoff hcutoff))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm hnorm))
        reflectedBentGuardAggregateSameObjectContractionFactor_nonnegative))

#print axioms reflectedBentGuardRootComplementTargetMass_le_partition
#print axioms reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_le_rootTargetComplement
#print axioms reflectedBentGuardScaledSeparatedTransitionRate_le_one
#print axioms reflectedBentGuardAggregateSameObjectContractionFactor_nonnegative
#print axioms reflectedBentGuardAggregateSameObjectContractionFactor_lt_one
#print axioms reflectedBentGuardNormalizedFourCellExcess_le_factor_mul_variance
#print axioms reflectedBentGuardFaceBooleanCovariance_le_factor_mul_variance
#print axioms reflectedBentGuardSameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectContraction
