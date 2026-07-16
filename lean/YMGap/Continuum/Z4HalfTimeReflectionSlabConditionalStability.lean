/-
# Two-sided normalized cutoff-one slab stability

The central connected-carrier tail contains the exact positive normalization
product used by the ambient and slab-conditioned probabilities.  Cancelling
that product gives a genuine finite-volume probability estimate.  Applying
the same estimate to the Boolean complement supplies the reverse direction
and hence an absolute modulus.

This theorem is deliberately stated for the cutoff-one canonical polymer gas.
It does not identify that gas with the arbitrary-cutoff spin-summed state.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierTail

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalStability

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalStabilityAlgebra
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

def centralSlabConditionalBoundaryEpsilon (half : Nat) : Q' :=
  Q'.ofNat 2 *
    (anchorEffectiveRatio ^ (half + 1) * Q'.ofNat 2)

theorem centralSlabConditionalBoundaryEpsilon_nonnegative (half : Nat) :
    (0 : Q') ≤ centralSlabConditionalBoundaryEpsilon half := by
  unfold centralSlabConditionalBoundaryEpsilon
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorEffectiveRatio
        anchorEffectiveRatio_nonnegative (half + 1)) (by decide))

theorem centralNormalizedSlabConnectedCylinderResidue_le
    {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    normalizedSlabConnectedCylinderResidue (centralExtent half)
        (centralSlabCanonicalRoots half hhalf) predicate ≤
      centralSlabConditionalBoundaryEpsilon half := by
  unfold normalizedSlabConnectedCylinderResidue
  apply Q'.divPos_le_of_le_mul
  exact centralSlabConnectedCylinderResidue_le_tail hhalf predicate

theorem centralAnchorAmbientProbability_sub_givenSlab_le
    {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    anchorEventProbability (centralAmbient half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) -
        anchorCanonicalGivenSlabProbability (centralExtent half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) ≤
      centralSlabConditionalBoundaryEpsilon half := by
  have halgebra := anchorAmbientProbability_sub_givenSlab_le_normalizedResidue
    (centralExtent half) (centralSlabCanonicalRoots half hhalf) predicate
  simpa [centralAmbient] using Q'.le_trans' _ _ _ halgebra
    (centralNormalizedSlabConnectedCylinderResidue_le hhalf predicate)

/-! ## Complement normalization for both exact laws -/

private theorem filter_and_eq_filter_filter {A : Type}
    (first second : A → Bool) (ambient : List A) :
    ambient.filter (fun item => first item && second item) =
      (ambient.filter first).filter second := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (first item) (second item)

theorem anchorEventNumerator_add_complement_eqv_partition
    (n : Nat) (event : List (List Nat) → Bool) :
    anchorEventNumerator n event +
        anchorEventNumerator n (fun family => !(event family)) ≈
      anchorCanonicalPartition n := by
  unfold anchorEventNumerator anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition
  exact Q'.eqv_symm
    (listQSum_filter_partition
      (canonicalSurfaceFamilyActivity anchorCoupling n) event
      (canonicalCompatibleAmbientFamilies n))

theorem anchorSlabRestrictedNumerator_add_complement_eqv_support
    (extent : Nat) (event : List (List Nat) → Bool) :
    anchorEventNumerator (extent + 1)
          (canonicalSlabRestrictedEvent extent event) +
        anchorEventNumerator (extent + 1)
          (canonicalSlabRestrictedEvent extent
            (fun family => !(event family))) ≈
      anchorEventNumerator (extent + 1)
        (canonicalFamilySlabSupportedB extent) := by
  unfold anchorEventNumerator canonicalSlabRestrictedEvent
  rw [filter_and_eq_filter_filter,
    filter_and_eq_filter_filter]
  exact Q'.eqv_symm
    (listQSum_filter_partition
      (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1)) event
      ((canonicalCompatibleAmbientFamilies (extent + 1)).filter
        (canonicalFamilySlabSupportedB extent)))

private theorem add_divPos_eqv_local
    (p p' q : Q') (hq : (0 : Q') < q) :
    Q'.divPos p q hq + Q'.divPos p' q hq ≈
      Q'.divPos (p + p') q hq :=
  Q'.eqv_symm (Q'.add_mul_eqv p p' (Q'.recipPos q hq))

theorem anchorEventProbability_add_complement_eqv_one
    (n : Nat) (event : List (List Nat) → Bool) :
    anchorEventProbability n event +
        anchorEventProbability n (fun family => !(event family)) ≈
      (1 : Q') := by
  have hsplit := anchorEventNumerator_add_complement_eqv_partition n event
  unfold anchorEventProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (anchorEventNumerator n event)
      (anchorEventNumerator n (fun family => !(event family)))
      (anchorCanonicalPartition n)
      (anchorCanonicalPartition_pos n)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos (anchorCanonicalPartition n)
        (anchorCanonicalPartition_pos n)) hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (anchorCanonicalPartition n) (anchorCanonicalPartition_pos n)

theorem anchorCanonicalGivenSlabProbability_add_complement_eqv_one
    (extent : Nat) (event : List (List Nat) → Bool) :
    anchorCanonicalGivenSlabProbability extent event +
        anchorCanonicalGivenSlabProbability extent
          (fun family => !(event family)) ≈
      (1 : Q') := by
  have hsplit :=
    anchorSlabRestrictedNumerator_add_complement_eqv_support extent event
  unfold anchorCanonicalGivenSlabProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (anchorEventNumerator (extent + 1)
        (canonicalSlabRestrictedEvent extent event))
      (anchorEventNumerator (extent + 1)
        (canonicalSlabRestrictedEvent extent
          (fun family => !(event family))))
      (anchorEventNumerator (extent + 1)
        (canonicalFamilySlabSupportedB extent))
      (canonicalSlabSupportNumerator_pos extent)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos
        (anchorEventNumerator (extent + 1)
          (canonicalFamilySlabSupportedB extent))
        (canonicalSlabSupportNumerator_pos extent)) hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (anchorEventNumerator (extent + 1)
      (canonicalFamilySlabSupportedB extent))
    (canonicalSlabSupportNumerator_pos extent)

/-! ## Reverse direction and absolute modulus -/

def complementSlabPredicate
    (predicate : List Bool → Bool) : List Bool → Bool :=
  fun bits => !(predicate bits)

private theorem left_eqv_one_sub_right {a complement : Q'}
    (hsum : a + complement ≈ (1 : Q')) :
    a ≈ (1 : Q') - complement := by
  refine Q'.eqv_trans _ (a + 0) _
    (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' a))) ?_
  refine Q'.eqv_trans _ (a + (complement + (-complement))) _
    (Q'.add_eqv_congr_left a 0 (complement + (-complement))
      (Q'.eqv_symm (Q'.add_neg_self_eqv complement))) ?_
  refine Q'.eqv_trans _ ((a + complement) + (-complement)) _
    (Q'.eqv_symm (Q'.add_assoc_eqv a complement (-complement))) ?_
  exact Q'.add_eqv_congr_right
    (a + complement) 1 (-complement) hsum

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem eventReverseSub_eqv_complementSub
    {a aComplement b bComplement : Q'}
    (ha : a + aComplement ≈ (1 : Q'))
    (hb : b + bComplement ≈ (1 : Q')) :
    a - b ≈ bComplement - aComplement := by
  refine Q'.eqv_trans _
    (((1 : Q') - aComplement) - ((1 : Q') - bComplement)) _
    (sub_eqv_both_local
      (left_eqv_one_sub_right ha)
      (left_eqv_one_sub_right hb)) ?_
  change
    ((1 + (-aComplement)) + (-(1 + (-bComplement)))) ≈
      (bComplement + (-aComplement))
  have hneg : (-(1 + (-bComplement))) ≈
      ((-1) + bComplement) := by
    refine Q'.eqv_trans _ ((-1) + (-(-bComplement))) _
      (Q'.neg_add_eqv 1 (-bComplement)) ?_
    exact Q'.add_eqv_congr_left (-1) (-(-bComplement)) bComplement
      (Q'.neg_neg_eqv bComplement)
  refine Q'.eqv_trans _
    ((1 + (-aComplement)) + ((-1) + bComplement)) _
    (Q'.add_eqv_congr_left (1 + (-aComplement)) _ _ hneg) ?_
  refine Q'.eqv_trans _
    ((1 + (-1)) + ((-aComplement) + bComplement)) _
    (Q'.add_swap_inner 1 (-aComplement) (-1) bComplement) ?_
  refine Q'.eqv_trans _
    (0 + ((-aComplement) + bComplement)) _
    (Q'.add_eqv_congr_right (1 + (-1)) 0
      ((-aComplement) + bComplement)
      (Q'.add_neg_self_eqv 1)) ?_
  refine Q'.eqv_trans _ ((-aComplement) + bComplement) _
    (Q'.eqv_of_eq (Q'.zero_add' ((-aComplement) + bComplement))) ?_
  exact Q'.add_comm_eqv (-aComplement) bComplement

theorem centralAnchorGivenSlab_sub_ambientProbability_le
    {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    anchorCanonicalGivenSlabProbability (centralExtent half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) -
        anchorEventProbability (centralAmbient half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) ≤
      centralSlabConditionalBoundaryEpsilon half := by
  let event := slabMarkedCylinderEvent
    (centralSlabCanonicalRoots half hhalf) predicate
  let complementEvent := slabMarkedCylinderEvent
    (centralSlabCanonicalRoots half hhalf)
      (complementSlabPredicate predicate)
  have hcomplement := centralAnchorAmbientProbability_sub_givenSlab_le
    hhalf (complementSlabPredicate predicate)
  have hpointwise : complementEvent =
      (fun family => !(event family)) := by
    funext family
    rfl
  have hambientSum :
      anchorEventProbability (centralAmbient half) event +
        anchorEventProbability (centralAmbient half) complementEvent ≈
      (1 : Q') := by
    rw [hpointwise]
    exact anchorEventProbability_add_complement_eqv_one
      (centralAmbient half) event
  have hslabSum :
      anchorCanonicalGivenSlabProbability (centralExtent half) event +
        anchorCanonicalGivenSlabProbability (centralExtent half)
          complementEvent ≈ (1 : Q') := by
    rw [hpointwise]
    exact anchorCanonicalGivenSlabProbability_add_complement_eqv_one
      (centralExtent half) event
  have hreorder :
      anchorCanonicalGivenSlabProbability (centralExtent half) event -
          anchorEventProbability (centralAmbient half) event ≈
        anchorEventProbability (centralAmbient half) complementEvent -
          anchorCanonicalGivenSlabProbability (centralExtent half)
            complementEvent :=
    eventReverseSub_eqv_complementSub hslabSum hambientSum
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) (by
    simpa [event, complementEvent, centralAmbient] using hcomplement)

private theorem sub_swap_eqv_neg_local (a b : Q') :
    b - a ≈ -(a - b) := by
  change (b + -a) ≈ (-(a + -b))
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv b (-a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-a) b (-(-b))
      (Q'.eqv_symm (Q'.neg_neg_eqv b))) ?_
  exact Q'.eqv_symm (Q'.neg_add_eqv a (-b))

/-- The complete normalized cutoff-one central slab comparison. -/
theorem centralAnchorAmbient_givenSlabProbability_abs_sub_le
    {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    Q'.abs
        (anchorEventProbability (centralAmbient half)
            (slabMarkedCylinderEvent
              (centralSlabCanonicalRoots half hhalf) predicate) -
          anchorCanonicalGivenSlabProbability (centralExtent half)
            (slabMarkedCylinderEvent
              (centralSlabCanonicalRoots half hhalf) predicate)) ≤
      centralSlabConditionalBoundaryEpsilon half := by
  apply Q'.abs_le
  · have hreverse := centralAnchorGivenSlab_sub_ambientProbability_le
      hhalf predicate
    have hneg := Q'.neg_le_neg hreverse
    exact Q'.le_trans' _ _ _ hneg
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (sub_swap_eqv_neg_local
            (anchorCanonicalGivenSlabProbability (centralExtent half)
              (slabMarkedCylinderEvent
                (centralSlabCanonicalRoots half hhalf) predicate))
            (anchorEventProbability (centralAmbient half)
              (slabMarkedCylinderEvent
                (centralSlabCanonicalRoots half hhalf) predicate)))))
  · exact centralAnchorAmbientProbability_sub_givenSlab_le
      hhalf predicate

#print axioms centralNormalizedSlabConnectedCylinderResidue_le
#print axioms centralAnchorAmbientProbability_sub_givenSlab_le
#print axioms anchorCanonicalGivenSlabProbability_add_complement_eqv_one
#print axioms centralAnchorGivenSlab_sub_ambientProbability_le
#print axioms centralAnchorAmbient_givenSlabProbability_abs_sub_le

end YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalStability
