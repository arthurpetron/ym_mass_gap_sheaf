/-
# The slab four-cell excess is ordinary Boolean covariance

This module instantiates the generic finite weighted Boolean-covariance
compiler on the literal expanded SU(2) slab carrier.  The two predicates are

  physical spin at the root face is positive,
  physical spin at the target face is positive.

The four generic event cells are identified exactly with the four typed slab
cell lists used by the paired-support switching argument.  Consequently the
strict normalized determinant bound is a conventional centered Boolean
covariance bound on the same finite physical law.

This does not yet identify the face-positive predicate with a strict
positive-time cylinder vector or its target copy with a two-step OS transfer
translate.

Constructive contract: finite attached carriers, Boolean filters, exact
rational setoid algebra, and positive division only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
import YMGap.Continuum.FiniteWeightedBooleanCovariance

namespace YMGap.Continuum.CompactDualSlabObservableBooleanCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

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

private theorem attach_filter_map_val
    {A : Type} (items : List A) (test : A → Bool) :
    (items.attach.filter (fun item => test item.1)).map Subtype.val =
      items.filter test := by
  change (items.attach.filter (test ∘ Subtype.val)).map Subtype.val = _
  rw [← List.filter_map, List.attach_map_subtype_val]

private theorem listQSum_attach_filter
    {A : Type} (items : List A) (weight : A → Q')
    (test : A → Bool) :
    listQSum (fun item : {value // value ∈ items} => weight item.1)
        (items.attach.filter (fun item => test item.1)) =
      listQSum weight (items.filter test) := by
  calc
    listQSum (fun item : {value // value ∈ items} => weight item.1)
        (items.attach.filter (fun item => test item.1)) =
      listQSum weight
        ((items.attach.filter (fun item => test item.1)).map Subtype.val) :=
          (listQSum_map _ _ _).symm
    _ = listQSum weight (items.filter test) :=
      congrArg _ (attach_filter_map_val items test)

private theorem filter_and_eq_filter_filter {A : Type}
    (first second : A → Bool) (ambient : List A) :
    ambient.filter (fun item => first item && second item) =
      (ambient.filter first).filter second := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (first item) (second item)

/-! ## 1. The literal finite face-event covariance -/

def slabObservableRawFacePositiveB
    (faceId : Nat)
    (source : SlabLabelling × SlabFusionWitnessAssignment) : Bool :=
  decide (0 < source.1 faceId)

def slabObservableFaceBooleanCovariance
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  finiteWeightedBooleanCovariance
    (slabExpandedFineSources D)
    (slabExpandedFineSourceWeight D)
    D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)
    (slabObservableRawFacePositiveB rootFaceId)
    (slabObservableRawFacePositiveB targetFaceId)

/-! ## 2. Exact identification of the four typed cells -/

theorem slabObservableRootTargetEntries_weight_eqv_TT
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum (slabObservablePositiveEntryWeight D)
        (slabObservableRootTargetEntries
          D rootFaceId targetFaceId) ≈
      finiteWeightedTT
        (slabExpandedFineSources D)
        (slabExpandedFineSourceWeight D)
        (slabObservableRawFacePositiveB rootFaceId)
        (slabObservableRawFacePositiveB targetFaceId) := by
  let states := slabExpandedFineSources D
  let weight := slabExpandedFineSourceWeight D
  let root : (SlabLabelling × SlabFusionWitnessAssignment) → Bool :=
    fun source => decide (0 < source.1 rootFaceId)
  let target : (SlabLabelling × SlabFusionWitnessAssignment) → Bool :=
    fun source => decide (0 < source.1 targetFaceId)
  change
    listQSum
        (fun entry : {value // value ∈ states.filter root} => weight entry.1)
        ((states.filter root).attach.filter
          (fun entry => target entry.1)) ≈
      listQSum weight
        (states.filter (fun state => root state && target state))
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq
      (listQSum_attach_filter (states.filter root) weight target))
    (Q'.eqv_of_eq
      (congrArg (listQSum weight)
        (filter_and_eq_filter_filter root target states).symm))

theorem slabObservableRootTargetComplementEntries_weight_eqv_TF
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum (slabObservablePositiveEntryWeight D)
        (slabObservableRootTargetComplementEntries
          D rootFaceId targetFaceId) ≈
      finiteWeightedTF
        (slabExpandedFineSources D)
        (slabExpandedFineSourceWeight D)
        (slabObservableRawFacePositiveB rootFaceId)
        (slabObservableRawFacePositiveB targetFaceId) := by
  let states := slabExpandedFineSources D
  let weight := slabExpandedFineSourceWeight D
  let root : (SlabLabelling × SlabFusionWitnessAssignment) → Bool :=
    fun source => decide (0 < source.1 rootFaceId)
  let target : (SlabLabelling × SlabFusionWitnessAssignment) → Bool :=
    fun source => decide (0 < source.1 targetFaceId)
  change
    listQSum
        (fun entry : {value // value ∈ states.filter root} => weight entry.1)
        ((states.filter root).attach.filter
          (fun entry => !(target entry.1))) ≈
      listQSum weight
        (states.filter (fun state => root state && !(target state)))
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq
      (listQSum_attach_filter
        (states.filter root) weight (fun state => !(target state))))
    (Q'.eqv_of_eq
      (congrArg (listQSum weight)
        (filter_and_eq_filter_filter
          root (fun state => !(target state)) states).symm))

theorem slabObservableRootComplementTargetEntries_weight_eqv_FT
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum (slabExpandedFineEntryWeight D)
        (slabObservableRootComplementTargetEntries
          D rootFaceId targetFaceId) ≈
      finiteWeightedFT
        (slabExpandedFineSources D)
        (slabExpandedFineSourceWeight D)
        (slabObservableRawFacePositiveB rootFaceId)
        (slabObservableRawFacePositiveB targetFaceId) := by
  let states := slabExpandedFineSources D
  let weight := slabExpandedFineSourceWeight D
  let root : (SlabLabelling × SlabFusionWitnessAssignment) → Bool :=
    fun source => decide (0 < source.1 rootFaceId)
  let target : (SlabLabelling × SlabFusionWitnessAssignment) → Bool :=
    fun source => decide (0 < source.1 targetFaceId)
  change
    listQSum (fun entry : {value // value ∈ states} => weight entry.1)
        (states.attach.filter
          (fun entry => !(root entry.1) && target entry.1)) ≈
      listQSum weight
        (states.filter (fun state => !(root state) && target state))
  exact Q'.eqv_of_eq
    (listQSum_attach_filter states weight
      (fun state => !(root state) && target state))

theorem slabObservableRootComplementTargetComplementEntries_weight_eqv_FF
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum (slabExpandedFineEntryWeight D)
        (slabObservableRootComplementTargetComplementEntries
          D rootFaceId targetFaceId) ≈
      finiteWeightedFF
        (slabExpandedFineSources D)
        (slabExpandedFineSourceWeight D)
        (slabObservableRawFacePositiveB rootFaceId)
        (slabObservableRawFacePositiveB targetFaceId) := by
  let states := slabExpandedFineSources D
  let weight := slabExpandedFineSourceWeight D
  let root : (SlabLabelling × SlabFusionWitnessAssignment) → Bool :=
    fun source => decide (0 < source.1 rootFaceId)
  let target : (SlabLabelling × SlabFusionWitnessAssignment) → Bool :=
    fun source => decide (0 < source.1 targetFaceId)
  change
    listQSum (fun entry : {value // value ∈ states} => weight entry.1)
        (states.attach.filter
          (fun entry => !(root entry.1) && !(target entry.1))) ≈
      listQSum weight
        (states.filter (fun state => !(root state) && !(target state)))
  exact Q'.eqv_of_eq
    (listQSum_attach_filter states weight
      (fun state => !(root state) && !(target state)))

/-! ## 3. Covariance identity and strict two-step bound -/

/-- The conventional finite-law Boolean covariance is exactly the typed
normalized four-cell excess controlled by paired-support peeling. -/
theorem slabObservableFaceBooleanCovariance_eqv_normalizedFourCellExcess
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    slabObservableFaceBooleanCovariance D rootFaceId targetFaceId ≈
      slabObservableNormalizedFourCellExcess
        D rootFaceId targetFaceId := by
  let states := slabExpandedFineSources D
  let weight := slabExpandedFineSourceWeight D
  let root := slabObservableRawFacePositiveB rootFaceId
  let target := slabObservableRawFacePositiveB targetFaceId
  have hgeneric :=
    finiteWeightedBooleanCovariance_eqv_normalizedFourCell
      states weight D.physicalPartition
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
      (slabExpandedFineSources_weight_total D) root target
  have htt := slabObservableRootTargetEntries_weight_eqv_TT
    D rootFaceId targetFaceId
  have htf := slabObservableRootTargetComplementEntries_weight_eqv_TF
    D rootFaceId targetFaceId
  have hft := slabObservableRootComplementTargetEntries_weight_eqv_FT
    D rootFaceId targetFaceId
  have hff :=
    slabObservableRootComplementTargetComplementEntries_weight_eqv_FF
      D rootFaceId targetFaceId
  have hrawNumerator :
      finiteWeightedFourCellCrossNumerator states weight root target ≈
        listQSum (slabObservablePositiveEntryWeight D)
              (slabObservableRootTargetEntries
                D rootFaceId targetFaceId) *
            listQSum (slabExpandedFineEntryWeight D)
              (slabObservableRootComplementTargetComplementEntries
                D rootFaceId targetFaceId) -
          listQSum (slabObservablePositiveEntryWeight D)
              (slabObservableRootTargetComplementEntries
                D rootFaceId targetFaceId) *
            listQSum (slabExpandedFineEntryWeight D)
              (slabObservableRootComplementTargetEntries
                D rootFaceId targetFaceId) := by
    unfold finiteWeightedFourCellCrossNumerator
    apply sub_eqv_both_local
    · exact mul_eqv_both_local (Q'.eqv_symm htt) (Q'.eqv_symm hff)
    · refine Q'.eqv_trans _
        (listQSum (slabExpandedFineEntryWeight D)
              (slabObservableRootComplementTargetEntries
                D rootFaceId targetFaceId) *
            listQSum (slabObservablePositiveEntryWeight D)
              (slabObservableRootTargetComplementEntries
                D rootFaceId targetFaceId)) _ ?_ ?_
      · exact mul_eqv_both_local (Q'.eqv_symm hft) (Q'.eqv_symm htf)
      · exact Q'.mul_comm_eqv _ _
  have hnormalized :
      finiteWeightedNormalizedFourCellCovariance
          states weight D.physicalPartition
          (slabParametricKPhysicalPartition_pos
            D.coupling_nonnegative D.cutoff D.extent)
          root target ≈
        slabObservableNormalizedFourCellExcess
          D rootFaceId targetFaceId := by
    unfold finiteWeightedNormalizedFourCellCovariance
      slabObservableNormalizedFourCellExcess
    exact divPos_numerator_eqv_local
      (Q'.mul_pos
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent))
      hrawNumerator
  exact Q'.eqv_trans _ _ _ hgeneric hnormalized

/-- **Strict ordinary Boolean covariance at two steps.**  At the fixed
production coupling, face-positive covariance is bounded above by the
cutoff- and slab-size-independent rational `4096/5625 < 1`. -/
theorem slabObservableFaceBooleanCovariance_le_twoStepRate
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half))
    (hseparated : 2 ≤
      linfDist
        (slabPlaquetteAt (centralExtent half) rootFaceId)
        (slabPlaquetteAt (centralExtent half) targetFaceId)) :
    slabObservableFaceBooleanCovariance
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId ≤
      slabObservablePairedSupportTwoStepRate := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (slabObservableFaceBooleanCovariance_eqv_normalizedFourCellExcess
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId))
    (slabObservableNormalizedFourCellExcess_le_twoStepRate
      cutoff half rootFaceId targetFaceId htarget hseparated)

#print axioms slabObservableRawFacePositiveB
#print axioms slabObservableFaceBooleanCovariance
#print axioms slabObservableRootTargetEntries_weight_eqv_TT
#print axioms slabObservableRootTargetComplementEntries_weight_eqv_TF
#print axioms slabObservableRootComplementTargetEntries_weight_eqv_FT
#print axioms slabObservableRootComplementTargetComplementEntries_weight_eqv_FF
#print axioms slabObservableFaceBooleanCovariance_eqv_normalizedFourCellExcess
#print axioms slabObservableFaceBooleanCovariance_le_twoStepRate

end YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
