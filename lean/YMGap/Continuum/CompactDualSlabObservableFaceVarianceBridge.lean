/-
# The connected source sector is bounded by the root-face variance

The retained-channel argument first bounds the reflected covariance by a
strict factor times the normalized mass of the support-connected part of the
determinant cell `11 x 00`.  This file keeps the normalization instead of
discarding it: `11` is contained in the root-positive event and `00` is
contained in its complement.  Hence the connected source mass is no larger
than `P(root) * (1 - P(root))`, exactly the squared norm of the centered
root-face indicator.

Consequently every reflected retained-channel certificate gives a genuine
relative form estimate for that one centered physical observable.

Constructive contract: finite filter domination, exact rational probability
algebra, and the existing physical GNS centering identities only; no choice,
`Classical`, `native_decide`, `sorry`, new axiom, noncomputable declaration,
or unbounded heartbeat option.
-/

import YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
import YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
import YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

namespace YMGap.Continuum.CompactDualSlabObservableFaceVarianceBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalTwoBlockProbabilityCovariance
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem divPos_numerator_eqv_local {p p' q : Q'}
    (hq : (0 : Q') < q) (hp : p ≈ p') :
    Q'.divPos p q hq ≈ Q'.divPos p' q hq := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ hp

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Root-event variance in the expanded physical law -/

/-- Exact expanded mass of the complement of the root-positive event. -/
def slabObservableExpandedRootZeroMass
    (D : SlabPhysicalData) (rootFaceId : Nat) : Q' :=
  finiteWeightedEventMass
    (slabExpandedFineSources D)
    (slabExpandedFineSourceWeight D)
    (fun source => !(slabObservableRawFacePositiveB rootFaceId source))

theorem slabExpandedPartition_eqv_rootPositive_add_zero
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    D.physicalPartition ≈
      slabObservablePositiveSourceWeight D rootFaceId +
        slabObservableExpandedRootZeroMass D rootFaceId := by
  let event := slabObservableRawFacePositiveB rootFaceId
  have hsplit := listQSum_filter_partition
    (slabExpandedFineSourceWeight D) event
    (slabExpandedFineSources D)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (slabExpandedFineSources_weight_total D))
    (Q'.eqv_trans _ _ _ hsplit (Q'.eqv_refl _))

theorem slabObservableFaceVariance_eqv_rootPositive_mul_zero
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    slabObservableFaceBooleanCovariance D rootFaceId rootFaceId ≈
      Q'.divPos
        (slabObservablePositiveSourceWeight D rootFaceId *
          slabObservableExpandedRootZeroMass D rootFaceId)
        (D.physicalPartition * D.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            D.coupling_nonnegative D.cutoff D.extent)
          (slabParametricKPhysicalPartition_pos
            D.coupling_nonnegative D.cutoff D.extent)) := by
  let states := slabExpandedFineSources D
  let weight := slabExpandedFineSourceWeight D
  let event := slabObservableRawFacePositiveB rootFaceId
  let positive := slabObservablePositiveSourceWeight D rootFaceId
  let zero := slabObservableExpandedRootZeroMass D rootFaceId
  let partition := D.physicalPartition
  have hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hjointFilter :
      states.filter (fun source => event source && event source) =
        states.filter event := by
    apply List.filter_congr
    intro source _
    cases event source <;> rfl
  have hpositive :
      finiteWeightedEventMass states weight event = positive := by
    rfl
  have hjoint :
      finiteWeightedEventMass states weight
          (fun source => event source && event source) = positive := by
    unfold finiteWeightedEventMass
    rw [hjointFilter]
    exact hpositive
  have hnormalized := normalizedProductDifference_eqv_crossNumerator
    positive positive positive partition hpartition
  have hpartitionSplit : partition ≈ positive + zero := by
    exact slabExpandedPartition_eqv_rootPositive_add_zero
      D rootFaceId
  have hnumerator :
      positive * partition - positive * positive ≈ positive * zero := by
    refine Q'.eqv_trans _
      (positive * (positive + zero) - positive * positive) _ ?_ ?_
    · exact sub_eqv_both_local
        (Q'.mul_eqv_congr_left positive _ _ hpartitionSplit)
        (Q'.eqv_refl _)
    · exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv positive positive zero)
          (Q'.eqv_refl _))
        (Q'.eqv_trans _
          ((positive * positive) +
            ((positive * zero) + -(positive * positive))) _
          (Q'.add_assoc_eqv _ _ _)
          (Q'.eqv_trans _
            ((positive * positive) +
              (-(positive * positive) + positive * zero)) _
            (Q'.add_eqv_congr_left _ _ _
              (Q'.add_comm_eqv _ _))
            (Q'.eqv_trans _
              (((positive * positive) + -(positive * positive)) +
                positive * zero) _
              (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
              (Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr_right _ _ _
                  (Q'.add_neg_self_eqv (positive * positive)))
                (Q'.eqv_of_eq (Q'.zero_add' _))))))
  unfold slabObservableFaceBooleanCovariance finiteWeightedBooleanCovariance
  change
    Q'.divPos
          (finiteWeightedEventMass states weight
            (fun source => event source && event source))
          partition hpartition -
        Q'.divPos (finiteWeightedEventMass states weight event)
            partition hpartition *
          Q'.divPos (finiteWeightedEventMass states weight event)
            partition hpartition ≈
      Q'.divPos (positive * zero) (partition * partition)
        (Q'.mul_pos hpartition hpartition)
  rw [hjoint, hpositive]
  exact Q'.eqv_trans _ _ _ hnormalized
    (divPos_numerator_eqv_local
      (Q'.mul_pos hpartition hpartition) hnumerator)

/-! ## 2. The connected determinant sector is no larger than the variance -/

private theorem finiteWeightedTT_le_firstEventMass
    {A : Type} (states : List A) (weight : A → Q')
    (hweight : ∀ state, (0 : Q') ≤ weight state)
    (first second : A → Bool) :
    finiteWeightedTT states weight first second ≤
      finiteWeightedEventMass states weight first := by
  unfold finiteWeightedTT finiteWeightedEventMass
  apply listQSum_filter_le_filter weight
    (fun state => first state && second state) first hweight
  intro state hboth
  cases hfirst : first state with
  | false => simp [hfirst] at hboth
  | true => rfl

private theorem finiteWeightedFF_le_firstComplementMass
    {A : Type} (states : List A) (weight : A → Q')
    (hweight : ∀ state, (0 : Q') ≤ weight state)
    (first second : A → Bool) :
    finiteWeightedFF states weight first second ≤
      finiteWeightedEventMass states weight (fun state => !(first state)) := by
  unfold finiteWeightedFF finiteWeightedEventMass
  apply listQSum_filter_le_filter weight
    (fun state => !(first state) && !(second state))
    (fun state => !(first state)) hweight
  intro state hboth
  cases hfirst : first state with
  | false => rfl
  | true => simp [hfirst] at hboth

theorem slabObservableNormalizedPairedSupportConnectedMass_le_faceVariance
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    slabObservableNormalizedPairedSupportConnectedMass
        D rootFaceId targetFaceId ≤
      slabObservableFaceBooleanCovariance D rootFaceId rootFaceId := by
  let states := slabExpandedFineSources D
  let weight := slabExpandedFineSourceWeight D
  let root := slabObservableRawFacePositiveB rootFaceId
  let target := slabObservableRawFacePositiveB targetFaceId
  let positive := slabObservablePositiveSourceWeight D rootFaceId
  let zero := slabObservableExpandedRootZeroMass D rootFaceId
  let connected := slabObservablePairedConnectedSourceMass
    D rootFaceId targetFaceId
  let sourceMass := listQSum (slabObservableTwoReplicaPairWeight D)
    (slabObservableFourCellSourcePairs D rootFaceId targetFaceId)
  have hweight : ∀ state, (0 : Q') ≤ weight state := by
    intro state
    exact slabObservableExpandedFineSourceWeight_nonnegative D state
  have hpairWeight : ∀ pair : SlabObservableTwoReplicaPair D rootFaceId,
      (0 : Q') ≤
      slabObservableTwoReplicaPairWeight D pair := by
    intro pair
    exact slabObservableTwoReplicaPairWeight_nonnegative
      D rootFaceId pair
  have hconnectedSource : connected ≤ sourceMass := by
    let separated := listQSum (slabObservableTwoReplicaPairWeight D)
      (slabObservablePairedSupportSeparatedFourCellSourcePairs
        D rootFaceId targetFaceId)
    have hsplit := slabObservableFourCellSourcePairs_pairedSupport_partition
      D rootFaceId targetFaceId
    have hseparated : (0 : Q') ≤ separated :=
      listQSum_nonnegative_on _ _ (fun pair _ => hpairWeight pair)
    have hadd : connected ≤ separated + connected := by
      have h := Q'.add_le_add_right (0 : Q') separated connected hseparated
      rwa [Q'.zero_add'] at h
    exact Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hsplit)
  have hfirst :
      listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetEntries
            D rootFaceId targetFaceId) ≤ positive := by
    have hTT := finiteWeightedTT_le_firstEventMass
      states weight hweight root target
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (slabObservableRootTargetEntries_weight_eqv_TT
          D rootFaceId targetFaceId)) hTT
  have hsecond :
      listQSum (slabExpandedFineEntryWeight D)
          (slabObservableRootComplementTargetComplementEntries
            D rootFaceId targetFaceId) ≤ zero := by
    have hFF := finiteWeightedFF_le_firstComplementMass
      states weight hweight root target
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (slabObservableRootComplementTargetComplementEntries_weight_eqv_FF
          D rootFaceId targetFaceId)) hFF
  have hfirstNonnegative : (0 : Q') ≤ positive := by
    unfold positive slabObservablePositiveSourceWeight
    exact listQSum_nonnegative_on _ _
      (fun source _ => slabObservableExpandedFineSourceWeight_nonnegative
        D source)
  have hsecondNonnegative : (0 : Q') ≤
      listQSum (slabExpandedFineEntryWeight D)
        (slabObservableRootComplementTargetComplementEntries
          D rootFaceId targetFaceId) :=
    listQSum_nonnegative_on _ _
      (fun entry _ => slabExpandedFineEntryWeight_nonnegative D entry)
  have hsourceProduct : sourceMass ≤ positive * zero := by
    have hproduct := slabObservableFourCellSourcePairs_weight_product
      D rootFaceId targetFaceId
    have hfirstMul := Q'.mul_le_mul_of_nonneg_right _ _ _ hfirst
      hsecondNonnegative
    have hsecondMul := Q'.mul_le_mul_of_nonneg_left _ _ _ hsecond
      hfirstNonnegative
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hproduct)
      (Q'.le_trans' _ _ _ hfirstMul hsecondMul)
  have hraw : connected ≤ positive * zero :=
    Q'.le_trans' _ _ _ hconnectedSource hsourceProduct
  have hpartition : (0 : Q') < D.physicalPartition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hdenominator : (0 : Q') <
      D.physicalPartition * D.physicalPartition :=
    Q'.mul_pos hpartition hpartition
  have hnormalized :
      slabObservableNormalizedPairedSupportConnectedMass
          D rootFaceId targetFaceId ≤
        Q'.divPos (positive * zero)
          (D.physicalPartition * D.physicalPartition) hdenominator := by
    unfold slabObservableNormalizedPairedSupportConnectedMass
    apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ hraw
      (Q'.ge_of_eqv
        (Q'.divPos_mul_eqv (positive * zero)
          (D.physicalPartition * D.physicalPartition) hdenominator))
  exact Q'.le_trans' _ _ _ hnormalized
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (slabObservableFaceVariance_eqv_rootPositive_mul_zero
          D rootFaceId)))

/-! ## 3. Exact identification with the centered physical GNS norm -/

private theorem centralPhysicalWeightedInner_symm_local
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (left right : EdgeLabelling → Q') :
    centralPhysicalWeightedInner w hw K half left right ≈
      centralPhysicalWeightedInner w hw K half right left := by
  unfold centralPhysicalWeightedInner
  apply listQSum_congr
  intro state
  exact Q'.mul_eqv_congr_left
    (centralPhysicalRowMarginal w hw K half state) _ _
    (Q'.mul_comm_eqv _ _)

theorem centralPhysicalCenteredFaceObservable_norm_eqv_variance
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half) :
    centralPhysicalWeightedInner
        D.coupling D.coupling_nonnegative D.cutoff D.half
        (centralPhysicalCenteredObservable
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (slabPhysicalFacePositiveUnitObservable rootFaceId).value)
        (centralPhysicalCenteredObservable
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (slabPhysicalFacePositiveUnitObservable rootFaceId).value) ≈
      slabObservableFaceBooleanCovariance D rootFaceId rootFaceId := by
  let observable :=
    (slabPhysicalFacePositiveUnitObservable rootFaceId).value
  let mean := centralPhysicalStationaryMean
    D.coupling D.coupling_nonnegative D.cutoff D.half observable
  have hself :
      centralPhysicalWeightedInner
          D.coupling D.coupling_nonnegative D.cutoff D.half
          observable observable ≈ mean := by
    dsimp only [mean]
    unfold centralPhysicalWeightedInner centralPhysicalStationaryMean
    apply listQSum_congr
    intro state
    apply Q'.mul_eqv_congr_left
    change
      ((if slabPhysicalFacePositiveB rootFaceId state
          then (1 : Q') else (0 : Q')) *
          (if slabPhysicalFacePositiveB rootFaceId state
            then (1 : Q') else (0 : Q'))) ≈
        (if slabPhysicalFacePositiveB rootFaceId state
          then (1 : Q') else (0 : Q'))
    cases slabPhysicalFacePositiveB rootFaceId state with
    | false => exact Q'.zero_mul_eqv 0
    | true => exact Q'.one_mul_eqv 1
  have hmean := slabPhysicalFaceStationaryMean_eqv_probability D hroot
  have hnorm := centralPhysicalCenteredObservable_norm_identity
    D.coupling D.coupling_nonnegative D.cutoff D.half observable
  have hjoint :
      finiteWeightedEventProbability
          D.physicalLabellings D.physicalTerm D.physicalPartition
          (slabParametricKPhysicalPartition_pos
            D.coupling_nonnegative D.cutoff D.extent)
          (fun state =>
            slabPhysicalFacePositiveB rootFaceId state &&
              slabPhysicalFacePositiveB rootFaceId state) ≈
        slabPhysicalFaceProbability D rootFaceId := by
    unfold finiteWeightedEventProbability finiteWeightedEventMass
      slabPhysicalFaceProbability
    apply divPos_numerator_eqv_local
    exact Q'.eqv_of_eq (congrArg (listQSum D.physicalTerm) (by
      apply List.filter_congr
      intro state _
      cases slabPhysicalFacePositiveB rootFaceId state <;> rfl))
  have hphysical :
      slabPhysicalFaceBooleanCovariance D rootFaceId rootFaceId ≈
        slabPhysicalFaceProbability D rootFaceId -
          slabPhysicalFaceProbability D rootFaceId *
            slabPhysicalFaceProbability D rootFaceId := by
    unfold slabPhysicalFaceBooleanCovariance finiteWeightedBooleanCovariance
    exact sub_eqv_both_local hjoint (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hnorm
    (Q'.eqv_trans _
      (mean - mean * mean) _
      (sub_eqv_both_local hself (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _
        (sub_eqv_both_local hmean
          (mul_eqv_both_local hmean hmean))
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm hphysical)
          (Q'.eqv_symm
            (slabObservableFaceBooleanCovariance_eqv_physical
              D rootFaceId rootFaceId)))))

theorem slabObservableNormalizedPairedSupportConnectedMass_le_centeredFaceNorm
    (D : SlabPhysicalData) {rootFaceId : Nat} (targetFaceId : Nat)
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half) :
    slabObservableNormalizedPairedSupportConnectedMass
        D rootFaceId targetFaceId ≤
      centralPhysicalWeightedInner
        D.coupling D.coupling_nonnegative D.cutoff D.half
        (centralPhysicalCenteredObservable
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (slabPhysicalFacePositiveUnitObservable rootFaceId).value)
        (centralPhysicalCenteredObservable
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (slabPhysicalFacePositiveUnitObservable rootFaceId).value) := by
  exact Q'.le_trans' _ _ _
    (slabObservableNormalizedPairedSupportConnectedMass_le_faceVariance
      D rootFaceId targetFaceId)
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (centralPhysicalCenteredFaceObservable_norm_eqv_variance
          D hroot)))

/-! ## 4. A retained reflected channel is a relative face-vector form gap -/

/-- The connected same-object scalar is exactly the Markov form of the
centered face indicator, with no normalization discarded. -/
theorem centralPhysicalCenteredFaceObservable_markovForm_eqv_sameObject
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    centralPhysicalWeightedInner
        D.coupling D.coupling_nonnegative D.cutoff D.half
        (centralPhysicalMarkovApply
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (centralPhysicalCenteredObservable
            D.coupling D.coupling_nonnegative D.cutoff D.half
            (slabPhysicalFacePositiveUnitObservable rootFaceId).value))
        (centralPhysicalCenteredObservable
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (slabPhysicalFacePositiveUnitObservable rootFaceId).value) ≈
      slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId := by
  let observable :=
    (slabPhysicalFacePositiveUnitObservable rootFaceId).value
  let mean := centralPhysicalStationaryMean
    D.coupling D.coupling_nonnegative D.cutoff D.half observable
  have hcentered := centralPhysicalCenteredObservable_markovForm_identity
    D.coupling D.coupling_nonnegative D.cutoff D.half observable
  have hsymm := centralPhysicalWeightedInner_symm_local
    D.coupling D.coupling_nonnegative D.cutoff D.half
    (centralPhysicalMarkovApply
      D.coupling D.coupling_nonnegative D.cutoff D.half observable)
    observable
  unfold slabPhysicalFaceSameObjectConnectedMarkovMoment
  exact Q'.eqv_trans _ _ _ hcentered
    (sub_eqv_both_local hsymm (Q'.eqv_refl (mean * mean)))

theorem sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    (data : SlabObservablePairedSplitRetainedContraction
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId ≤
      ((1 : Q') + -data.fraction) *
        centralPhysicalWeightedInner
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (centralPhysicalCenteredObservable
            D.coupling D.coupling_nonnegative D.cutoff D.half
            (slabPhysicalFacePositiveUnitObservable rootFaceId).value)
          (centralPhysicalCenteredObservable
            D.coupling D.coupling_nonnegative D.cutoff D.half
            (slabPhysicalFacePositiveUnitObservable rootFaceId).value) := by
  let targetFaceId := slabFaceReflectId D.extent rootFaceId
  have hsame := slabPhysicalReflectedFaceBooleanCovariance_eqv_sameObject
    D hroot
  have hphysical := slabObservableFaceBooleanCovariance_eqv_physical
    D rootFaceId targetFaceId
  have htoObservable :
      slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId ≈
        slabObservableFaceBooleanCovariance D rootFaceId targetFaceId :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hsame) (Q'.eqv_symm hphysical)
  have hconnected :=
    slabObservableNormalizedPairedSupportConnectedMass_le_centeredFaceNorm
      D targetFaceId hroot
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htoObservable)
    (Q'.le_trans' _ _ _
      data.faceBooleanCovariance_le_complement_mul_connectedMass
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hconnected
        data.complement_nonnegative))

#print axioms slabExpandedPartition_eqv_rootPositive_add_zero
#print axioms slabObservableFaceVariance_eqv_rootPositive_mul_zero
#print axioms slabObservableNormalizedPairedSupportConnectedMass_le_faceVariance
#print axioms centralPhysicalCenteredFaceObservable_norm_eqv_variance
#print axioms slabObservableNormalizedPairedSupportConnectedMass_le_centeredFaceNorm
#print axioms centralPhysicalCenteredFaceObservable_markovForm_eqv_sameObject
#print axioms sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm

end YMGap.Continuum.CompactDualSlabObservableFaceVarianceBridge
