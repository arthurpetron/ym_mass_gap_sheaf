/-
# Face observables in the corrected-slab conditional support law

This module compiles events on the corrected-slab physical labelling through
the exact zero-extension image and the arbitrary-cutoff spin-summed support
bridge.  Its generic theorem applies whenever a canonical-family event,
evaluated after slab zero extension, is definitionally the selected physical
event.

For a physical slab face, a constructive ambient coordinate is obtained by
list search.  Canonical-family occupancy of that ambient face is then proved
to be exactly positivity of the original slab spin.  Consequently the strict
two-face covariance already established on the production physical law is
also the ordinary connected covariance of two face-occupancy events in the
compatible support gas conditioned to the corrected slab.

This is still a finite fixed-coupling covariance statement.  It does not yet
identify the event with an Osterwalder--Schrader cylinder vector or a transfer
translate.

Constructive contract: explicit finite reindexing, Boolean masks, and exact
rational quotient algebra only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
import YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
import YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
import YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
import YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder

namespace YMGap.Continuum.CompactDualSlabObservableFaceEventLaw

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem listQSum_mask_eq_filter_local {A : Type}
    (weight : A → Q') (event : A → Bool) : ∀ source : List A,
    listQSum (fun item => if event item then weight item else 0) source ≈
      listQSum weight (source.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head with
      | false =>
          simp only [hevent, Bool.false_eq_true, if_false,
            List.filter_cons, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum weight (tail.filter event)) _
            (Q'.add_eqv_congr' (Q'.eqv_refl 0)
              (listQSum_mask_eq_filter_local weight event tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [hevent, if_true, List.filter_cons, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_mask_eq_filter_local weight event tail)

private theorem listQSum_congr_on_mem_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≈ right item) →
      listQSum left items ≈ listQSum right items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, h =>
      Q'.add_eqv_congr'
        (h head List.mem_cons_self)
        (listQSum_congr_on_mem_local left right tail
          (fun item hitem =>
            h item (List.mem_cons_of_mem head hitem)))

private def boolQIndicator (event : Bool) : Q' :=
  if event then 1 else 0

private theorem finiteWeightedEventMass_eqv_indicatorSum {A : Type}
    (states : List A) (weight : A → Q') (event : A → Bool) :
    finiteWeightedEventMass states weight event ≈
      listQSum
        (fun state => boolQIndicator (event state) * weight state)
        states := by
  unfold finiteWeightedEventMass
  refine Q'.eqv_trans _
    (listQSum (fun state => if event state then weight state else 0)
      states) _
    (Q'.eqv_symm
      (listQSum_mask_eq_filter_local weight event states)) ?_
  apply listQSum_congr
  intro state
  cases hevent : event state with
  | false =>
      simp only [hevent, Bool.false_eq_true, if_false, boolQIndicator]
      exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | true =>
      simp only [hevent, if_true, boolQIndicator]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)

private theorem filteredEventTerm_eqv_combinedNumerator
    (weight : EdgeLabelling → Q') (states : List EdgeLabelling)
    (support event : EdgeLabelling → Bool) :
    listQSum (fun physical =>
        if event physical then weight physical else 0)
        (states.filter support) ≈
      listQSum (fun physical =>
        if support physical && event physical then weight physical else 0)
        states := by
  refine Q'.eqv_trans _
    (listQSum (fun physical =>
      if support physical then
        (if event physical then weight physical else 0)
      else 0) states) _
    (Q'.eqv_symm
      (listQSum_mask_eq_filter_local
        (fun physical => if event physical then weight physical else 0)
        support states)) ?_
  apply listQSum_congr
  intro physical
  cases hsupport : support physical <;>
    cases hevent : event physical <;>
      simp [hsupport, hevent] <;>
        exact Q'.eqv_refl _

/-! ## 1. A constructive ambient coordinate for each slab face -/

def slabAmbientFaceId (extent faceId : Nat) : Nat :=
  listIndexOf (slabPlaquetteAt extent faceId)
    (boxPlaquettes (extent + 1))

theorem slabAmbientFaceId_physical
    {extent faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    slabAmbientFaceId extent faceId ∈
      physicalFaceEdges (extent + 1) := by
  unfold slabAmbientFaceId physicalFaceEdges plaquetteEdgeCount
  apply List.mem_range.mpr
  apply listIndexOf_lt_of_mem
  exact ((mem_boundaryCompleteSlabPlaquettes extent _).mp
    (slabPlaquetteAt_mem hface)).1

theorem boxPlaquetteAt_slabAmbientFaceId
    {extent faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    boxPlaquetteAt (extent + 1)
        (slabAmbientFaceId extent faceId) =
      slabPlaquetteAt extent faceId := by
  unfold boxPlaquetteAt slabAmbientFaceId
  exact getD_listIndexOf_of_mem fallbackPlaquette _ _
    (((mem_boundaryCompleteSlabPlaquettes extent _).mp
      (slabPlaquetteAt_mem hface)).1)

theorem slabToAmbientPhysical_slabAmbientFaceId
    {extent faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (physical : SlabLabelling) :
    slabToAmbientPhysical extent physical
        (slabAmbientFaceId extent faceId) =
      physical faceId := by
  unfold slabToAmbientPhysical
  have hlt : slabAmbientFaceId extent faceId <
      plaquetteEdgeCount (extent + 1) := by
    exact List.mem_range.mp (by
      simpa only [physicalFaceEdges] using
        slabAmbientFaceId_physical hface)
  rw [if_pos hlt, boxPlaquetteAt_slabAmbientFaceId hface]
  exact slabGeometricSpin_eq_of_enumerate
    (slabPlaquetteAt_mem_enumerate hface)

/-- Canonical-family occupancy of the chosen ambient face is literally
positivity of the corresponding corrected-slab spin. -/
theorem cutoffOneLiftedFamilyFaceEvent_slabToAmbient
    {extent faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (physical : SlabLabelling) :
    cutoffOneLiftedFamilyEvent (extent + 1)
        (familyContainsFaceB (slabAmbientFaceId extent faceId))
        (slabToAmbientPhysical extent physical) =
      slabPhysicalFacePositiveB faceId physical := by
  unfold cutoffOneLiftedFamilyEvent slabPhysicalFacePositiveB
  rw [familyContainsFaceB_eq_memberB_unionSupport
      (slabAmbientFaceId_physical hface),
    physicalCanonicalAmbientFamily_unionSupport]
  apply Bool.eq_iff_iff.mpr
  unfold excitedPlaquetteIds
  simp only [memberB_eq_true_iff, List.mem_filter,
    slabAmbientFaceId_physical hface, decide_eq_true_eq, true_and]
  rw [slabToAmbientPhysical_slabAmbientFaceId hface]
  exact Iff.rfl

/-! ## 2. Generic physical-event conditional-law compiler -/

/-- Any slab event with an exact canonical-family zero-extension decoder has
the same unnormalized mass as the corresponding ambient numerator restricted
to slab support. -/
theorem slabPhysicalEventMass_eqv_slabRestrictedNumerator
    (D : SlabPhysicalData)
    (slabEvent : SlabLabelling → Bool)
    (familyEvent : List (List Nat) → Bool)
    (hlift : ∀ physical,
      cutoffOneLiftedFamilyEvent (D.extent + 1) familyEvent
          (slabToAmbientPhysical D.extent physical) =
        slabEvent physical) :
    finiteWeightedEventMass
        D.physicalLabellings D.physicalTerm slabEvent ≈
      parametricKEventNumerator
        D.coupling D.cutoff (D.extent + 1)
        (fun physical => ambientSlabSupportedB D.extent physical &&
          cutoffOneLiftedFamilyEvent
            (D.extent + 1) familyEvent physical) := by
  let indicator : SlabLabelling → Q' := fun physical =>
    boolQIndicator (slabEvent physical)
  have hphysical :
      finiteWeightedEventMass
          D.physicalLabellings D.physicalTerm slabEvent ≈
        slabWeightedPhysicalSum
          D.coupling D.cutoff D.extent indicator := by
    unfold SlabPhysicalData.physicalLabellings
      SlabPhysicalData.physicalTerm slabWeightedPhysicalSum indicator
    exact finiteWeightedEventMass_eqv_indicatorSum _ _ _
  have hreindex := slabWeightedPhysicalSum_eq_ambientSupported
    D.coupling D.cutoff D.extent indicator
  have hsupported :
      ambientSlabSupportedWeightedSum
          D.coupling D.cutoff D.extent indicator ≈
        parametricKEventNumerator
          D.coupling D.cutoff (D.extent + 1)
          (fun physical => ambientSlabSupportedB D.extent physical &&
            cutoffOneLiftedFamilyEvent
              (D.extent + 1) familyEvent physical) := by
    let states := boundedEdgeLabellings D.cutoff
      (List.range (plaquetteEdgeCount (D.extent + 1)))
    let support := ambientSlabSupportedB D.extent
    let lifted := cutoffOneLiftedFamilyEvent
      (D.extent + 1) familyEvent
    let weight := parametricKPhysicalTerm
      D.coupling D.cutoff (D.extent + 1)
    have hpoint :
        listQSum
            (fun target =>
              indicator (ambientToSlabPhysical D.extent target) *
                weight target)
            (states.filter support) ≈
          listQSum
            (fun target => if lifted target then weight target else 0)
            (states.filter support) := by
      apply listQSum_congr_on_mem_local
      intro target htarget
      have hparts : target ∈ states ∧ support target = true :=
        List.mem_filter.mp htarget
      have hround :
          slabToAmbientPhysical D.extent
              (ambientToSlabPhysical D.extent target) = target :=
        slabToAmbientPhysical_ambientToSlab hparts.1 hparts.2
      have hevent :
          slabEvent (ambientToSlabPhysical D.extent target) =
            lifted target := by
        have hdecoded := hlift
          (ambientToSlabPhysical D.extent target)
        rw [hround] at hdecoded
        exact hdecoded.symm
      unfold indicator boolQIndicator
      rw [hevent]
      cases hlifted : lifted target with
      | false =>
          simp only [hlifted, Bool.false_eq_true, if_false]
          exact Q'.zero_mul_eqv _
      | true =>
          simp only [hlifted, if_true]
          exact Q'.one_mul_eqv _
    unfold ambientSlabSupportedWeightedSum
      ambientSlabSupportedLabellings
      parametricKEventNumerator parametricKEventTerm
    exact Q'.eqv_trans _ _ _ hpoint
      (filteredEventTerm_eqv_combinedNumerator
        weight states support lifted)
  exact Q'.eqv_trans _ _ _ hphysical
    (Q'.eqv_trans _ _ _ hreindex hsupported)

/-- Normalizing the preceding identity gives the exact physical corrected-
slab conditional probability. -/
theorem slabPhysicalEventProbability_eqv_physicalGivenSlab
    (D : SlabPhysicalData)
    (slabEvent : SlabLabelling → Bool)
    (familyEvent : List (List Nat) → Bool)
    (hlift : ∀ physical,
      cutoffOneLiftedFamilyEvent (D.extent + 1) familyEvent
          (slabToAmbientPhysical D.extent physical) =
        slabEvent physical) :
    finiteWeightedEventProbability
        D.physicalLabellings D.physicalTerm
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)
        slabEvent ≈
      couplingParametricKPhysicalGivenSlabProbability
        D.coupling D.coupling_nonnegative D.cutoff D.extent
        familyEvent := by
  unfold finiteWeightedEventProbability
    couplingParametricKPhysicalGivenSlabProbability
  exact Z4SpinSummedCrossVolumeCylinder.divPos_eqv_congr
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      D.coupling_nonnegative D.cutoff D.extent)
    (slabPhysicalEventMass_eqv_slabRestrictedNumerator
      D slabEvent familyEvent hlift)
    (slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
      D.coupling D.cutoff D.extent)

/-- The same event probability in the literal compatible support gas. -/
theorem slabPhysicalEventProbability_eqv_compatibleGivenSlab
    (D : SlabPhysicalData)
    (slabEvent : SlabLabelling → Bool)
    (familyEvent : List (List Nat) → Bool)
    (hlift : ∀ physical,
      cutoffOneLiftedFamilyEvent (D.extent + 1) familyEvent
          (slabToAmbientPhysical D.extent physical) =
        slabEvent physical) :
    finiteWeightedEventProbability
        D.physicalLabellings D.physicalTerm
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)
        slabEvent ≈
      couplingParametricKCompatibleGivenSlabProbability
        D.coupling D.coupling_nonnegative D.cutoff D.extent
        familyEvent :=
  Q'.eqv_trans _ _ _
    (slabPhysicalEventProbability_eqv_physicalGivenSlab
      D slabEvent familyEvent hlift)
    (couplingParametricKPhysicalGivenSlabProbability_eqv_compatible
      D.coupling D.coupling_nonnegative D.cutoff D.extent familyEvent)

/-! ## 3. Two-face connected covariance in the support law -/

def slabCompatibleFaceEvent
    (extent faceId : Nat) : List (List Nat) → Bool :=
  familyContainsFaceB (slabAmbientFaceId extent faceId)

def slabPhysicalFacePairEvent
    (rootFaceId targetFaceId : Nat) (physical : SlabLabelling) : Bool :=
  slabPhysicalFacePositiveB rootFaceId physical &&
    slabPhysicalFacePositiveB targetFaceId physical

def slabCompatibleFacePairEvent
    (extent rootFaceId targetFaceId : Nat)
    (family : List (List Nat)) : Bool :=
  slabCompatibleFaceEvent extent rootFaceId family &&
    slabCompatibleFaceEvent extent targetFaceId family

theorem cutoffOneLiftedFamilyFacePairEvent_slabToAmbient
    {extent rootFaceId targetFaceId : Nat}
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges extent)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (physical : SlabLabelling) :
    cutoffOneLiftedFamilyEvent (extent + 1)
        (slabCompatibleFacePairEvent extent rootFaceId targetFaceId)
        (slabToAmbientPhysical extent physical) =
      slabPhysicalFacePairEvent rootFaceId targetFaceId physical := by
  have hrootDecoded :=
    cutoffOneLiftedFamilyFaceEvent_slabToAmbient hroot physical
  have htargetDecoded :=
    cutoffOneLiftedFamilyFaceEvent_slabToAmbient htarget physical
  unfold cutoffOneLiftedFamilyEvent slabCompatibleFacePairEvent
    slabCompatibleFaceEvent slabPhysicalFacePairEvent at *
  rw [hrootDecoded, htargetDecoded]

def slabCompatibleFaceBooleanCovariance
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  couplingParametricKCompatibleGivenSlabProbability
      D.coupling D.coupling_nonnegative D.cutoff D.extent
      (slabCompatibleFacePairEvent
        D.extent rootFaceId targetFaceId) -
    couplingParametricKCompatibleGivenSlabProbability
        D.coupling D.coupling_nonnegative D.cutoff D.extent
        (slabCompatibleFaceEvent D.extent rootFaceId) *
      couplingParametricKCompatibleGivenSlabProbability
        D.coupling D.coupling_nonnegative D.cutoff D.extent
        (slabCompatibleFaceEvent D.extent targetFaceId)

theorem slabPhysicalFaceBooleanCovariance_eqv_compatible
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabPhysicalFaceBooleanCovariance D rootFaceId targetFaceId ≈
      slabCompatibleFaceBooleanCovariance
        D rootFaceId targetFaceId := by
  have hrootProbability :=
    slabPhysicalEventProbability_eqv_compatibleGivenSlab D
      (slabPhysicalFacePositiveB rootFaceId)
      (slabCompatibleFaceEvent D.extent rootFaceId)
      (cutoffOneLiftedFamilyFaceEvent_slabToAmbient hroot)
  have htargetProbability :=
    slabPhysicalEventProbability_eqv_compatibleGivenSlab D
      (slabPhysicalFacePositiveB targetFaceId)
      (slabCompatibleFaceEvent D.extent targetFaceId)
      (cutoffOneLiftedFamilyFaceEvent_slabToAmbient htarget)
  have hjointProbability :=
    slabPhysicalEventProbability_eqv_compatibleGivenSlab D
      (slabPhysicalFacePairEvent rootFaceId targetFaceId)
      (slabCompatibleFacePairEvent
        D.extent rootFaceId targetFaceId)
      (cutoffOneLiftedFamilyFacePairEvent_slabToAmbient hroot htarget)
  unfold slabPhysicalFaceBooleanCovariance
    slabCompatibleFaceBooleanCovariance
    finiteWeightedBooleanCovariance
  unfold slabPhysicalFacePairEvent at hjointProbability
  exact sub_eqv_both_local hjointProbability
    (mul_eqv_both_local hrootProbability htargetProbability)

/-- **Strict connected face covariance in the compatible support law.** -/
theorem slabCompatibleFaceBooleanCovariance_le_twoStepRate
    (cutoff half rootFaceId targetFaceId : Nat)
    (hroot : rootFaceId ∈
      slabPhysicalFaceEdges (centralExtent half))
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half))
    (hseparated : 2 ≤
      linfDist
        (slabPlaquetteAt (centralExtent half) rootFaceId)
        (slabPlaquetteAt (centralExtent half) targetFaceId)) :
    slabCompatibleFaceBooleanCovariance
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId ≤
      slabObservablePairedSupportTwoStepRate := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (slabPhysicalFaceBooleanCovariance_eqv_compatible
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId hroot htarget)))
    (slabPhysicalFaceBooleanCovariance_le_twoStepRate
      cutoff half rootFaceId targetFaceId htarget hseparated)

#print axioms slabAmbientFaceId
#print axioms slabAmbientFaceId_physical
#print axioms boxPlaquetteAt_slabAmbientFaceId
#print axioms slabToAmbientPhysical_slabAmbientFaceId
#print axioms cutoffOneLiftedFamilyFaceEvent_slabToAmbient
#print axioms slabPhysicalEventMass_eqv_slabRestrictedNumerator
#print axioms slabPhysicalEventProbability_eqv_physicalGivenSlab
#print axioms slabPhysicalEventProbability_eqv_compatibleGivenSlab
#print axioms slabCompatibleFaceEvent
#print axioms slabPhysicalFacePairEvent
#print axioms slabCompatibleFacePairEvent
#print axioms cutoffOneLiftedFamilyFacePairEvent_slabToAmbient
#print axioms slabCompatibleFaceBooleanCovariance
#print axioms slabPhysicalFaceBooleanCovariance_eqv_compatible
#print axioms slabCompatibleFaceBooleanCovariance_le_twoStepRate

end YMGap.Continuum.CompactDualSlabObservableFaceEventLaw
