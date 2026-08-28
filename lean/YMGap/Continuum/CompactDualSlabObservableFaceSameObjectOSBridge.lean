/-
# The paired-support face covariance is one same-object BF4 OS moment

The non-abelian paired-support peeling estimate already controls the ordinary
connected covariance of two face-positivity events in the corrected-slab
physical law.  This module chooses the target face to be the reflection of a
lower face and identifies that covariance with the connected same-object form

  `<a, P a> - E(a)^2`

of the literal physical BF4 conditional operator.  Here `a` is the actual
zero-one lower-face indicator, not an abstract observable supplied as an
interface field.

The exact equality has two consequences.  Osterwalder--Schrader positivity
gives nonnegativity of this reflected connected covariance, while the complete
paired-support component peel gives the geometric upper envelope

  `(25/9) * (16/25)^(distance + 1)`.

Both statements pass to the already-constructed representation-cutoff CReal
limit at fixed anchor coupling and fixed finite slab extent.  This does not
identify the conditional operator with one Euclidean lattice-time shift,
prove an all-observable spectral gap, vary the coupling along an asymptotically
free trajectory, or take a thermodynamic/continuum limit.

Constructive contract: finite reindexing, Boolean indicators, exact rational
algebra, and the existing Bishop-real cutoff limit only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableFaceEventLaw
import YMGap.Continuum.BF4PhysicalCutoffConnectedLimit

namespace YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCutoffAutocorrelationLimit
open YMGap.Continuum.BF4PhysicalCutoffConnectedLimit
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableFaceEventLaw
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem divPos_numerator_eqv_local {p p' q : Q'}
    (hq : (0 : Q') < q) (hp : p ≈ p') :
    Q'.divPos p q hq ≈ Q'.divPos p' q hq := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ hp

private theorem centralPhysicalWeightedInner_symm_local
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : EdgeLabelling → Q') :
    centralPhysicalWeightedInner w hw cutoff half left right ≈
      centralPhysicalWeightedInner w hw cutoff half right left := by
  unfold centralPhysicalWeightedInner
  apply listQSum_congr
  intro state
  exact Q'.mul_eqv_congr_left
    (centralPhysicalRowMarginal w hw cutoff half state) _ _
    (Q'.mul_comm_eqv _ _)

private theorem listQSum_indicator_mul_eqv_filter {A : Type}
    (weight : A → Q') (event : A → Bool) : ∀ items : List A,
    listQSum
        (fun item => (if event item then (1 : Q') else 0) * weight item)
        items ≈
      listQSum weight (items.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head with
      | false =>
          simp only [listQSum, hevent, Bool.false_eq_true, if_false,
            List.filter_cons]
          refine Q'.eqv_trans _
            (0 + listQSum weight (tail.filter event)) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.zero_mul_eqv (weight head))
              (listQSum_indicator_mul_eqv_filter weight event tail)
          · exact Q'.eqv_of_eq
              (Q'.zero_add' (listQSum weight (tail.filter event)))
      | true =>
          simp only [listQSum, hevent, if_true, List.filter_cons]
          exact Q'.add_eqv_congr'
            (Q'.one_mul_eqv (weight head))
            (listQSum_indicator_mul_eqv_filter weight event tail)

private theorem boolIndicator_mul_eqv_and (first second : Bool) :
    (if first then (1 : Q') else 0) *
        (if second then (1 : Q') else 0) ≈
      if first && second then 1 else 0 := by
  cases first with
  | false =>
      cases second with
      | false => exact Q'.zero_mul_eqv 0
      | true => exact Q'.zero_mul_eqv 1
  | true =>
      cases second with
      | false => exact Q'.one_mul_eqv 0
      | true => exact Q'.one_mul_eqv 1

/-! ## 1. The literal lower-face unit observable -/

/-- Zero-one indicator that one selected lower-half face carries positive
twice-spin. -/
def slabPhysicalFacePositiveUnitObservable
    (faceId : Nat) : CentralPhysicalUnitObservable where
  value state :=
    if slabPhysicalFacePositiveB faceId state then 1 else 0
  nonnegative := by
    intro state
    cases hface : slabPhysicalFacePositiveB faceId state with
    | false => exact Q'.le_refl' 0
    | true => exact Q'.zero_le_one
  le_one := by
    intro state
    cases hface : slabPhysicalFacePositiveB faceId state with
    | false => exact Q'.zero_le_one
    | true => exact Q'.le_refl' 1

@[simp] theorem slabPhysicalFacePositiveUnitObservable_value
    (faceId : Nat) (state : EdgeLabelling) :
    (slabPhysicalFacePositiveUnitObservable faceId).value state =
      if slabPhysicalFacePositiveB faceId state then 1 else 0 := rfl

theorem slabPhysicalFacePositiveUnitObservable_lowerRestriction
    {half rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds half)
    (physical : EdgeLabelling) :
    (slabPhysicalFacePositiveUnitObservable rootFaceId).value
        (centralLowerRestriction half physical) =
      if slabPhysicalFacePositiveB rootFaceId physical then 1 else 0 := by
  change
    (if slabPhysicalFacePositiveB rootFaceId
        (centralLowerRestriction half physical)
      then 1 else 0) =
      if slabPhysicalFacePositiveB rootFaceId physical then 1 else 0
  unfold slabPhysicalFacePositiveB centralLowerRestriction
  simp only [hroot, if_true]

theorem slabPhysicalFacePositiveUnitObservable_reflectedUpperRestriction
    {half rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds half)
    (physical : EdgeLabelling) :
    (slabPhysicalFacePositiveUnitObservable rootFaceId).value
        (centralReflectedUpperRestriction half physical) =
      if slabPhysicalFacePositiveB
          (slabFaceReflectId (centralExtent half) rootFaceId) physical
        then 1 else 0 := by
  change
    (if slabPhysicalFacePositiveB rootFaceId
        (centralReflectedUpperRestriction half physical)
      then 1 else 0) =
      if slabPhysicalFacePositiveB
          (slabFaceReflectId (centralExtent half) rootFaceId) physical
        then 1 else 0
  unfold slabPhysicalFacePositiveB centralReflectedUpperRestriction
  simp only [hroot, if_true]

/-! ## 2. Generic finite event-probability bridge -/

/-- A zero-one corrected-slab observable has expectation equal to the literal
filtered event probability in the production physical law. -/
theorem slabBoundedObservableExpectation_eqv_eventProbability
    (D : SlabPhysicalData)
    (observable : CutoffStableSlabUnitObservable D.extent)
    (event : EdgeLabelling → Bool)
    (hvalue : ∀ physical,
      observable.value D.cutoff physical ≈
        if event physical then 1 else 0) :
    slabNomeCutoffBoundedObservableExpectation
        D.coupling D.coupling_nonnegative D.cutoff D.extent observable ≈
      finiteWeightedEventProbability
        D.physicalLabellings D.physicalTerm D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)
        event := by
  unfold slabNomeCutoffBoundedObservableExpectation
    slabBoundedObservableNumerator finiteWeightedEventProbability
    finiteWeightedEventMass SlabPhysicalData.physicalLabellings
    SlabPhysicalData.physicalTerm SlabPhysicalData.physicalPartition
    SlabPhysicalData.faceEdges
  apply divPos_numerator_eqv_local
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        (if event physical then (1 : Q') else 0) *
          slabParametricKPhysicalTerm
            D.coupling D.cutoff D.extent physical)
      (boundedEdgeLabellings D.cutoff
        (slabPhysicalFaceEdges D.extent))) _ ?_ ?_
  · apply listQSum_congr
    intro physical
    exact Q'.mul_eqv_congr_right _ _ _ (hvalue physical)
  · exact listQSum_indicator_mul_eqv_filter
      (slabParametricKPhysicalTerm D.coupling D.cutoff D.extent)
      event
      (boundedEdgeLabellings D.cutoff
        (slabPhysicalFaceEdges D.extent))

/-- Probability of one literal face-positive event in the production
corrected-slab law. -/
def slabPhysicalFaceProbability
    (D : SlabPhysicalData) (faceId : Nat) : Q' :=
  finiteWeightedEventProbability
    D.physicalLabellings D.physicalTerm D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)
    (slabPhysicalFacePositiveB faceId)

/-- Probability of the joint positivity event at two literal slab faces. -/
def slabPhysicalFacePairProbability
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  finiteWeightedEventProbability
    D.physicalLabellings D.physicalTerm D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)
    (slabPhysicalFacePairEvent rootFaceId targetFaceId)

theorem slabPhysicalFaceStationaryMean_eqv_probability
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half) :
    centralPhysicalStationaryMean
        D.coupling D.coupling_nonnegative D.cutoff D.half
        (slabPhysicalFacePositiveUnitObservable rootFaceId).value ≈
      slabPhysicalFaceProbability D rootFaceId := by
  let observable := slabPhysicalFacePositiveUnitObservable rootFaceId
  refine Q'.eqv_trans _
    (slabNomeCutoffBoundedObservableExpectation
      D.coupling D.coupling_nonnegative D.cutoff D.extent
      (centralLowerSlabUnitObservable D.half observable)) _ ?_ ?_
  · simpa only [SlabPhysicalData.extent] using
      (centralPhysicalStationaryMean_eq_slabExpectation
        D.coupling D.coupling_nonnegative D.cutoff D.half observable)
  · unfold slabPhysicalFaceProbability
    apply slabBoundedObservableExpectation_eqv_eventProbability
    intro physical
    exact Q'.eqv_of_eq
      (slabPhysicalFacePositiveUnitObservable_lowerRestriction
        hroot physical)

theorem slabPhysicalFaceMarkovAutocorrelation_eqv_pairProbability
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half) :
    centralPhysicalWeightedInner
        D.coupling D.coupling_nonnegative D.cutoff D.half
        (slabPhysicalFacePositiveUnitObservable rootFaceId).value
        (centralPhysicalMarkovApply
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (slabPhysicalFacePositiveUnitObservable rootFaceId).value) ≈
      slabPhysicalFacePairProbability D rootFaceId
        (slabFaceReflectId D.extent rootFaceId) := by
  let observable := slabPhysicalFacePositiveUnitObservable rootFaceId
  let targetFaceId := slabFaceReflectId D.extent rootFaceId
  refine Q'.eqv_trans _
    (slabNomeCutoffBoundedObservableExpectation
      D.coupling D.coupling_nonnegative D.cutoff D.extent
      (centralAutocorrelationSlabUnitObservable D.half observable)) _ ?_ ?_
  · simpa only [SlabPhysicalData.extent] using
      (centralPhysicalMarkovAutocorrelation_eq_slabExpectation
        D.coupling D.coupling_nonnegative D.cutoff D.half observable)
  · unfold slabPhysicalFacePairProbability
    apply slabBoundedObservableExpectation_eqv_eventProbability
    intro physical
    have hlower :=
      slabPhysicalFacePositiveUnitObservable_lowerRestriction
        hroot physical
    have hupper :=
      slabPhysicalFacePositiveUnitObservable_reflectedUpperRestriction
        hroot physical
    change
      (slabPhysicalFacePositiveUnitObservable rootFaceId).value
          (centralLowerRestriction D.half physical) *
        (slabPhysicalFacePositiveUnitObservable rootFaceId).value
          (centralReflectedUpperRestriction D.half physical) ≈
        if slabPhysicalFacePairEvent rootFaceId
            (slabFaceReflectId D.extent rootFaceId) physical
          then 1 else 0
    rw [hlower, hupper]
    unfold slabPhysicalFacePairEvent
    exact boolIndicator_mul_eqv_and
      (slabPhysicalFacePositiveB rootFaceId physical)
      (slabPhysicalFacePositiveB
        (slabFaceReflectId D.extent rootFaceId) physical)

/-! ## 3. Reflection identifies both one-face marginals -/

private theorem finiteWeightedEventProbability_eqv_slabEventNumerator
    (D : SlabPhysicalData) (event : EdgeLabelling → Bool) :
    finiteWeightedEventProbability
        D.physicalLabellings D.physicalTerm D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)
        event ≈
      Q'.divPos
        (slabEventNumerator
          D.coupling D.cutoff D.extent event)
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent) := by
  unfold finiteWeightedEventProbability finiteWeightedEventMass
    slabEventNumerator SlabPhysicalData.physicalLabellings
    SlabPhysicalData.physicalTerm SlabPhysicalData.physicalPartition
    SlabPhysicalData.faceEdges
  apply divPos_numerator_eqv_local
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        (if event physical then (1 : Q') else 0) *
          slabParametricKPhysicalTerm
            D.coupling D.cutoff D.extent physical)
      (boundedEdgeLabellings D.cutoff
        (slabPhysicalFaceEdges D.extent))) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_indicator_mul_eqv_filter
        (slabParametricKPhysicalTerm D.coupling D.cutoff D.extent)
        event
        (boundedEdgeLabellings D.cutoff
          (slabPhysicalFaceEdges D.extent)))
  · apply listQSum_congr
    intro physical
    cases hevent : event physical with
    | false => exact Q'.zero_mul_eqv _
    | true => exact Q'.one_mul_eqv _

theorem slabPhysicalReflectedFaceProbability_eqv_root
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half) :
    slabPhysicalFaceProbability D
        (slabFaceReflectId D.extent rootFaceId) ≈
      slabPhysicalFaceProbability D rootFaceId := by
  have hrootPhysical : rootFaceId ∈ slabPhysicalFaceEdges D.extent := by
    simpa only [SlabPhysicalData.extent] using
      (mem_centralLowerFaceIds.mp hroot).1
  let rootEvent := slabPhysicalFacePositiveB rootFaceId
  let targetEvent := slabPhysicalFacePositiveB
    (slabFaceReflectId D.extent rootFaceId)
  have hevent : reflectSlabEvent D.extent rootEvent = targetEvent := by
    funext physical
    unfold reflectSlabEvent rootEvent targetEvent
      slabPhysicalFacePositiveB
    rw [reflectSupportedSlabFaceLabelling_eq_on_physical
      D.extent physical hrootPhysical]
    rfl
  have hreflection := slabEventNumerator_reflection
    D.coupling D.cutoff D.extent rootEvent
  rw [hevent] at hreflection
  unfold slabPhysicalFaceProbability
  refine Q'.eqv_trans _
    (Q'.divPos
      (slabEventNumerator D.coupling D.cutoff D.extent targetEvent)
      D.physicalPartition
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)) _ ?_ ?_
  · exact finiteWeightedEventProbability_eqv_slabEventNumerator
      D targetEvent
  · refine Q'.eqv_trans _
      (Q'.divPos
        (slabEventNumerator D.coupling D.cutoff D.extent rootEvent)
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)) _ ?_ ?_
    · exact divPos_numerator_eqv_local
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)
        hreflection
    · exact Q'.eqv_symm
        (finiteWeightedEventProbability_eqv_slabEventNumerator
          D rootEvent)

/-! ## 4. Exact same-object connected equality and OS positivity -/

/-- The literal connected same-object form of the selected face indicator. -/
def slabPhysicalFaceSameObjectConnectedMarkovMoment
    (D : SlabPhysicalData) (rootFaceId : Nat) : Q' :=
  centralPhysicalWeightedInner
      D.coupling D.coupling_nonnegative D.cutoff D.half
      (slabPhysicalFacePositiveUnitObservable rootFaceId).value
      (centralPhysicalMarkovApply
        D.coupling D.coupling_nonnegative D.cutoff D.half
        (slabPhysicalFacePositiveUnitObservable rootFaceId).value) -
    centralPhysicalStationaryMean
        D.coupling D.coupling_nonnegative D.cutoff D.half
        (slabPhysicalFacePositiveUnitObservable rootFaceId).value *
      centralPhysicalStationaryMean
        D.coupling D.coupling_nonnegative D.cutoff D.half
        (slabPhysicalFacePositiveUnitObservable rootFaceId).value

/-- **Exact observable-connected bridge.**  The ordinary face covariance for
a reflection pair is the connected same-object form of one literal observable
under the genuine physical BF4 conditional operator. -/
theorem slabPhysicalReflectedFaceBooleanCovariance_eqv_sameObject
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half) :
    slabPhysicalFaceBooleanCovariance D rootFaceId
        (slabFaceReflectId D.extent rootFaceId) ≈
      slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId := by
  have hpair := slabPhysicalFaceMarkovAutocorrelation_eqv_pairProbability
    D hroot
  have hmean := slabPhysicalFaceStationaryMean_eqv_probability D hroot
  have htarget := slabPhysicalReflectedFaceProbability_eqv_root D hroot
  unfold slabPhysicalFacePairProbability slabPhysicalFacePairEvent at hpair
  unfold slabPhysicalFaceProbability at hmean htarget
  unfold slabPhysicalFaceBooleanCovariance
    finiteWeightedBooleanCovariance
    slabPhysicalFaceSameObjectConnectedMarkovMoment
  exact sub_eqv_both_local (Q'.eqv_symm hpair)
    (mul_eqv_both_local
      (Q'.eqv_symm hmean)
      (Q'.eqv_trans _ _ _ htarget (Q'.eqv_symm hmean)))

/-- OS positivity makes the reflected connected covariance nonnegative. -/
theorem slabPhysicalReflectedFaceBooleanCovariance_nonnegative
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half) :
    (0 : Q') ≤
      slabPhysicalFaceBooleanCovariance D rootFaceId
        (slabFaceReflectId D.extent rootFaceId) := by
  let centered := centralPhysicalCenteredObservable
    D.coupling D.coupling_nonnegative D.cutoff D.half
      (slabPhysicalFacePositiveUnitObservable rootFaceId).value
  have hpositive := centralPhysicalMarkovApply_positive_left
    D.coupling D.coupling_nonnegative D.cutoff D.half centered
  have hcentered := centralPhysicalCenteredObservable_markovForm_identity
    D.coupling D.coupling_nonnegative D.cutoff D.half
      (slabPhysicalFacePositiveUnitObservable rootFaceId).value
  have hsymm := centralPhysicalWeightedInner_symm_local
    D.coupling D.coupling_nonnegative D.cutoff D.half
    (centralPhysicalMarkovApply
      D.coupling D.coupling_nonnegative D.cutoff D.half
      (slabPhysicalFacePositiveUnitObservable rootFaceId).value)
    (slabPhysicalFacePositiveUnitObservable rootFaceId).value
  have hmoment :
      centralPhysicalWeightedInner
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (centralPhysicalMarkovApply
            D.coupling D.coupling_nonnegative D.cutoff D.half centered)
          centered ≈
        slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId := by
    unfold slabPhysicalFaceSameObjectConnectedMarkovMoment
    exact Q'.eqv_trans _ _ _ hcentered
      (Q'.add_eqv_congr' hsymm (Q'.eqv_refl _))
  exact Q'.le_trans' _ _ _ hpositive
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hmoment)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (slabPhysicalReflectedFaceBooleanCovariance_eqv_sameObject
            D hroot))))

/-! ## 5. The full component-peel rate on the same OS observable -/

/-- The complete four-cell component peel gives its full geometric rate,
before specializing the separation to two lattice units. -/
theorem slabObservableNormalizedFourCellExcess_le_globalAnchorRate
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half)) :
    slabObservableNormalizedFourCellExcess
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId ≤
      slabObservablePairedSupportGlobalAnchorRate
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId := by
  let D := anchorSlabPhysicalData cutoff half
  have hfour := slabObservableFourCell_defect_le_pairedSupportConnected
    cutoff half rootFaceId targetFaceId htarget
  have hconnected :=
    slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare
      cutoff half rootFaceId targetFaceId htarget
  have hcombined := Q'.le_trans' _ _ _ hfour
    (Q'.add_le_add (Q'.le_refl' _) hconnected)
  unfold slabObservableNormalizedFourCellExcess
  apply Q'.divPos_le_of_le_mul
  exact Q'.sub_le_of_le_add hcombined

theorem slabPhysicalFaceBooleanCovariance_le_globalAnchorRate
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half)) :
    slabPhysicalFaceBooleanCovariance
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId ≤
      slabObservablePairedSupportGlobalAnchorRate
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId := by
  have hphysical := slabObservableFaceBooleanCovariance_eqv_physical
    (anchorSlabPhysicalData cutoff half) rootFaceId targetFaceId
  have hfour := slabObservableFaceBooleanCovariance_eqv_normalizedFourCellExcess
    (anchorSlabPhysicalData cutoff half) rootFaceId targetFaceId
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hphysical) hfour))
    (slabObservableNormalizedFourCellExcess_le_globalAnchorRate
      cutoff half rootFaceId targetFaceId htarget)

/-- The same-object reflected face moment is squeezed between zero and the
full geometric component-peel envelope at the anchor coupling. -/
theorem slabPhysicalReflectedFaceSameObject_geometric_interval
    (cutoff half rootFaceId : Nat)
    (hroot : rootFaceId ∈ centralLowerFaceIds half) :
    (0 : Q') ≤
        slabPhysicalFaceSameObjectConnectedMarkovMoment
          (anchorSlabPhysicalData cutoff half) rootFaceId ∧
      slabPhysicalFaceSameObjectConnectedMarkovMoment
          (anchorSlabPhysicalData cutoff half) rootFaceId ≤
        slabObservablePairedSupportGlobalAnchorRate
          (anchorSlabPhysicalData cutoff half) rootFaceId
          (slabFaceReflectId (centralExtent half) rootFaceId) := by
  have hrootPhysical := (mem_centralLowerFaceIds.mp hroot).1
  have htarget := slabFaceReflectId_physical hrootPhysical
  have heq := slabPhysicalReflectedFaceBooleanCovariance_eqv_sameObject
    (anchorSlabPhysicalData cutoff half) hroot
  constructor
  · exact Q'.le_trans' _ _ _
      (slabPhysicalReflectedFaceBooleanCovariance_nonnegative
        (anchorSlabPhysicalData cutoff half) hroot)
      (Q'.le_of_eqv heq)
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm heq))
      (slabPhysicalFaceBooleanCovariance_le_globalAnchorRate
        cutoff half rootFaceId
        (slabFaceReflectId (centralExtent half) rootFaceId) htarget)

/-! ## 6. Representation-cutoff limit of the exact same observable -/

/-- Cutoff-removed connected autocorrelation of the literal lower-face
indicator at the fixed production nome. -/
def anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
    (half rootFaceId : Nat) : CReal :=
  centralPhysicalConnectedAutocorrelationCutoffLimit
    (w := anchorCoupling) (by decide) (by decide) half
    (slabPhysicalFacePositiveUnitObservable rootFaceId)

@[simp] theorem
    anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit_approx
    (half rootFaceId cutoff : Nat) :
    (anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
      half rootFaceId).approx cutoff =
      slabPhysicalFaceSameObjectConnectedMarkovMoment
        (anchorSlabPhysicalData cutoff half) rootFaceId := rfl

theorem anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit_approx_eqv_covariance
    (half rootFaceId cutoff : Nat)
    (hroot : rootFaceId ∈ centralLowerFaceIds half) :
    (anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
        half rootFaceId).approx cutoff ≈
      slabPhysicalFaceBooleanCovariance
        (anchorSlabPhysicalData cutoff half) rootFaceId
        (slabFaceReflectId (centralExtent half) rootFaceId) := by
  exact Q'.eqv_symm
    (slabPhysicalReflectedFaceBooleanCovariance_eqv_sameObject
      (anchorSlabPhysicalData cutoff half) hroot)

theorem anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit_nonnegative
    (half rootFaceId : Nat) :
    CReal.czero ≤
      anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
        half rootFaceId := by
  exact centralPhysicalConnectedAutocorrelationCutoffLimit_nonnegative
    (w := anchorCoupling) (by decide) (by decide) half
      (slabPhysicalFacePositiveUnitObservable rootFaceId)

/-- **Cutoff-removed observable-connected decay.**  The representation-cutoff
limit of the actual reflected face autocorrelation obeys the same geometric
component-peel rate.  The displayed bound is independent of the representation
cutoff because that cutoff has been constructively removed. -/
theorem anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit_le_globalRate
    (half rootFaceId : Nat)
    (hroot : rootFaceId ∈ centralLowerFaceIds half) :
    anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
        half rootFaceId ≤
      CReal.ofQ'
        (slabObservablePairedSupportGlobalAnchorRate
          (anchorSlabPhysicalData 0 half) rootFaceId
          (slabFaceReflectId (centralExtent half) rootFaceId)) := by
  apply CReal.le_ofQ'_of_approx_le
  intro cutoff
  have htarget := slabFaceReflectId_physical
    (mem_centralLowerFaceIds.mp hroot).1
  have hbridge :=
    anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit_approx_eqv_covariance
      half rootFaceId cutoff hroot
  have hcov := slabPhysicalFaceBooleanCovariance_le_globalAnchorRate
    cutoff half rootFaceId
      (slabFaceReflectId (centralExtent half) rootFaceId) htarget
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hbridge)
    (by simpa only [slabObservablePairedSupportGlobalAnchorRate,
      SlabPhysicalData.extent, anchorSlabPhysicalData] using hcov)

#print axioms slabPhysicalFacePositiveUnitObservable
#print axioms slabBoundedObservableExpectation_eqv_eventProbability
#print axioms slabPhysicalFaceStationaryMean_eqv_probability
#print axioms slabPhysicalFaceMarkovAutocorrelation_eqv_pairProbability
#print axioms slabPhysicalReflectedFaceProbability_eqv_root
#print axioms slabPhysicalReflectedFaceBooleanCovariance_eqv_sameObject
#print axioms slabPhysicalReflectedFaceBooleanCovariance_nonnegative
#print axioms slabObservableNormalizedFourCellExcess_le_globalAnchorRate
#print axioms slabPhysicalFaceBooleanCovariance_le_globalAnchorRate
#print axioms slabPhysicalReflectedFaceSameObject_geometric_interval
#print axioms anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
#print axioms anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit_approx_eqv_covariance
#print axioms anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit_nonnegative
#print axioms anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit_le_globalRate

end YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
