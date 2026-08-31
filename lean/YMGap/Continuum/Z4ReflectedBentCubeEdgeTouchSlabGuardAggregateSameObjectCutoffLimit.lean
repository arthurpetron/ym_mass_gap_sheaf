/-
# Cutoff removal for the aggregate guarded same-object face contraction

The aggregate guarded opposite-cell floor controls more than the reflected
form numerator.  Both factors of that cell lie inside the root-positive and
root-zero events, so the same fixed rate is a lower bound for the variance of
the literal centered root-face indicator at every positive representation
cutoff.

Together with the cutoff-uniform relative contraction, this yields two
eventual-order statements after constructive representation-cutoff removal:
the connected norm stays above the positive guarded rate, and the connected
autocorrelation stays below the fixed factor `1 - rate` times that norm.

This is one explicit nonzero observable in the cutoff-removed fixed-volume
form.  It is not an all-vector form gap, a cutoff-independent transfer
operator, volume or spacing uniformity, a continuum limit, or a Clay theorem.

Constructive contract: finite filter domination, exact `Q'` division, and the
existing Bishop-real cutoff streams.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectContraction

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectCutoffLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedLimit
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
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectContraction
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRetainedContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The opposite cell lies inside the root variance product -/

theorem reflectedBentGuardRootTargetComplementMass_le_positiveMass
    (cutoff : Nat) :
    listQSum
        (slabObservablePositiveEntryWeight
          (anchorSlabPhysicalData cutoff 2))
        (slabObservableRootTargetComplementEntries
          (anchorSlabPhysicalData cutoff 2)
          reflectedBentRootFaceId reflectedBentTargetFaceId) ≤
      slabObservablePositiveSourceWeight
        (anchorSlabPhysicalData cutoff 2) reflectedBentRootFaceId := by
  let D := anchorSlabPhysicalData cutoff 2
  have hfilter := listQSum_filter_le
    (slabObservablePositiveEntryWeight D)
    (fun entry =>
      !(SlabObservablePositiveSourceEntry.facePositiveB
        entry reflectedBentTargetFaceId))
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
  simpa only [D, slabObservableRootTargetComplementEntries, htotal] using
    hfilter

theorem reflectedBentGuardRootComplementTargetMass_le_rootZeroMass
    (cutoff : Nat) :
    listQSum
        (slabExpandedFineEntryWeight (anchorSlabPhysicalData cutoff 2))
        (slabObservableRootComplementTargetEntries
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
    (fun source => !(root source) && target source)
    (fun source => !(root source)) hnonnegative
    (fun source hsource => by
      cases hroot : root source with
      | false => simp [hroot]
      | true => simp [hroot] at hsource)
    states
  have hcell := slabObservableRootComplementTargetEntries_weight_eqv_FT
    D reflectedBentRootFaceId reflectedBentTargetFaceId
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hcell)
    (by simpa only [finiteWeightedFT, finiteWeightedEventMass,
        slabObservableExpandedRootZeroMass, states, weight, root, target]
      using hfilter)

/-- The aggregate opposite-cell floor is a cutoff-independent positive lower
bound for the variance of the literal root-face indicator. -/
theorem reflectedBentGuardScaledSeparatedTransitionRate_le_faceVariance
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    reflectedBentGuardScaledSeparatedTransitionRate ≤
      slabObservableFaceBooleanCovariance
        (anchorSlabPhysicalData cutoff 2)
        reflectedBentRootFaceId reflectedBentRootFaceId := by
  let D := anchorSlabPhysicalData cutoff 2
  let rate := reflectedBentGuardScaledSeparatedTransitionRate
  let positive :=
    slabObservablePositiveSourceWeight D reflectedBentRootFaceId
  let zero :=
    slabObservableExpandedRootZeroMass D reflectedBentRootFaceId
  let first := listQSum (slabObservablePositiveEntryWeight D)
    (slabObservableRootTargetComplementEntries
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
  let second := listQSum (slabExpandedFineEntryWeight D)
    (slabObservableRootComplementTargetEntries
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
  let partitionSq := D.physicalPartition * D.physicalPartition
  have hfloor :=
    reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_sq_le_targetCell
      cutoff hcutoff
  have hproduct := slabObservableFourCellTargetPairs_weight_product
    D reflectedBentRootFaceId reflectedBentTargetFaceId
  have hfloorProduct : rate * partitionSq ≤ first * second :=
    Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv hproduct)
  have hfirst : first ≤ positive := by
    simpa only [D, first, positive] using
      (reflectedBentGuardRootTargetComplementMass_le_positiveMass cutoff)
  have hsecond : second ≤ zero := by
    simpa only [D, second, zero] using
      (reflectedBentGuardRootComplementTargetMass_le_rootZeroMass cutoff)
  have hfirstNonnegative : (0 : Q') ≤ first :=
    reflectedBentGuardRootTargetComplementMass_nonnegative cutoff
  have hzeroNonnegative : (0 : Q') ≤ zero := by
    unfold zero slabObservableExpandedRootZeroMass finiteWeightedEventMass
    exact listQSum_nonnegative_on _ _
      (fun source _ =>
        slabObservableExpandedFineSourceWeight_nonnegative D source)
  have hproductBound : first * second ≤ positive * zero :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ second hfirst
        (listQSum_nonnegative_on _ _
          (fun entry _ => slabExpandedFineEntryWeight_nonnegative D entry)))
      (Q'.mul_le_mul_of_nonneg_left _ _ positive hsecond
        (Q'.le_trans' _ _ _ hfirstNonnegative hfirst))
  have hcleared : rate * partitionSq ≤ positive * zero :=
    Q'.le_trans' _ _ _ hfloorProduct hproductBound
  have hpartition : (0 : Q') < D.physicalPartition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hpartitionSq : (0 : Q') < partitionSq :=
    Q'.mul_pos hpartition hpartition
  have hdiv : rate ≤
      Q'.divPos (positive * zero) partitionSq hpartitionSq :=
    Q'.le_divPos_of_mul_le _ _ hpartitionSq hcleared
  have hvariance := slabObservableFaceVariance_eqv_rootPositive_mul_zero
    D reflectedBentRootFaceId
  exact Q'.le_trans' _ _ _ hdiv
    (Q'.le_of_eqv (Q'.eqv_symm hvariance))

/-! ## 2. The exact cutoff-removed connected norm -/

def reflectedBentGuardFaceConnectedNormCutoffLimit : CReal :=
  centralPhysicalConnectedNormCutoffLimit
    (w := anchorCoupling) (by decide) (by decide) 2
    (slabPhysicalFacePositiveUnitObservable reflectedBentRootFaceId)

@[simp] theorem reflectedBentGuardFaceConnectedNormCutoffLimit_approx
    (cutoff : Nat) :
    reflectedBentGuardFaceConnectedNormCutoffLimit.approx cutoff =
      (centralPhysicalConnectedNormCutoffLimit
        (w := anchorCoupling) (by decide) (by decide) 2
        (slabPhysicalFacePositiveUnitObservable
          reflectedBentRootFaceId)).approx cutoff := rfl

/-- The cutoff-removed connected norm remains above the same positive guarded
rate in the Bishop-real eventual order. -/
theorem reflectedBentGuardScaledSeparatedTransitionRate_leEv_faceConnectedNorm :
    CReal.leEv
      (CReal.ofQ' reflectedBentGuardScaledSeparatedTransitionRate)
      reflectedBentGuardFaceConnectedNormCutoffLimit := by
  intro epsilon hepsilon
  refine ⟨1, ?_⟩
  intro cutoff hcutoff
  let D := anchorSlabPhysicalData cutoff 2
  have hfinite :=
    reflectedBentGuardScaledSeparatedTransitionRate_le_faceVariance
      cutoff hcutoff
  have hroot : reflectedBentRootFaceId ∈ centralLowerFaceIds D.half :=
    reflectedBentRootFaceId_lower_at_extent D rfl
  have hnorm :=
    centralPhysicalConnectedNormCutoffLimit_approx_eqv_centeredNorm
      (w := anchorCoupling) (by decide) (by decide) 2 cutoff
      (slabPhysicalFacePositiveUnitObservable reflectedBentRootFaceId)
  have hface := centralPhysicalCenteredFaceObservable_norm_eqv_variance
    D hroot
  have hnormVariance :
      reflectedBentGuardFaceConnectedNormCutoffLimit.approx cutoff ≈
        slabObservableFaceBooleanCovariance
          D reflectedBentRootFaceId reflectedBentRootFaceId :=
    Q'.eqv_trans _ _ _ hnorm hface
  change reflectedBentGuardScaledSeparatedTransitionRate ≤
    reflectedBentGuardFaceConnectedNormCutoffLimit.approx cutoff + epsilon
  exact Q'.le_trans' _ _ _ hfinite
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hnormVariance))
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)))

/-! ## 3. The cutoff-removed same-object relative form gap -/

def reflectedBentGuardFaceConnectedAutocorrelationCutoffLimit : CReal :=
  anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
    2 reflectedBentRootFaceId

@[simp] private theorem cRealMul_approx_local
    (left right : CReal) (cutoff : Nat) :
    (CReal.mul left right).approx cutoff =
      left.approx cutoff * right.approx cutoff := rfl

/-- The finite uniform contraction survives representation-cutoff removal for
the exact same centered face observable. -/
theorem reflectedBentGuardFaceConnectedAutocorrelationCutoffLimit_leEv_factor_mul_norm :
    CReal.leEv
      (anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
        2 reflectedBentRootFaceId)
      (CReal.mul
        (CReal.ofQ' reflectedBentGuardAggregateSameObjectContractionFactor)
        reflectedBentGuardFaceConnectedNormCutoffLimit) := by
  intro epsilon hepsilon
  refine ⟨1, ?_⟩
  intro cutoff hcutoff
  rw [anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit_approx,
    cRealMul_approx_local, CReal.ofQ'_approx]
  have hfinite :=
    reflectedBentGuardSameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
      cutoff hcutoff
  have hnorm :=
    centralPhysicalConnectedNormCutoffLimit_approx_eqv_centeredNorm
      (w := anchorCoupling) (by decide) (by decide) 2 cutoff
      (slabPhysicalFacePositiveUnitObservable reflectedBentRootFaceId)
  exact Q'.le_trans' _ _ _
    hfinite
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          reflectedBentGuardAggregateSameObjectContractionFactor _ _
          (Q'.eqv_symm hnorm)))
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)))

/-- Quotient-real packaging of the cutoff-removed guarded face form gap. -/
theorem reflectedBentGuardFaceConnectedAutocorrelationCutoffLimit_RC_gap :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
          2 reflectedBentRootFaceId))
      (CReal.RCscale
        reflectedBentGuardAggregateSameObjectContractionFactor
        (Quotient.mk CReal.crealSetoid
          reflectedBentGuardFaceConnectedNormCutoffLimit)) := by
  rw [CReal.RCscale_mk, CReal.RCle_mk]
  exact
    reflectedBentGuardFaceConnectedAutocorrelationCutoffLimit_leEv_factor_mul_norm

#print axioms reflectedBentGuardRootTargetComplementMass_le_positiveMass
#print axioms reflectedBentGuardRootComplementTargetMass_le_rootZeroMass
#print axioms reflectedBentGuardScaledSeparatedTransitionRate_le_faceVariance
#print axioms reflectedBentGuardFaceConnectedNormCutoffLimit
#print axioms reflectedBentGuardScaledSeparatedTransitionRate_leEv_faceConnectedNorm
#print axioms reflectedBentGuardFaceConnectedAutocorrelationCutoffLimit_leEv_factor_mul_norm
#print axioms reflectedBentGuardFaceConnectedAutocorrelationCutoffLimit_RC_gap

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectCutoffLimit
