/-
# Uniform two-sided finite-cutoff corrected-slab stability

The arbitrary-cutoff connected carrier tail contains exactly the product of
the compatible full partition and corrected-slab support numerator.  After
the positive normalization proved in the preceding algebra file, that product
cancels and leaves a volume-decaying probability modulus uniform in the
finite character cutoff and in every coupling below the derived anchor.

Boolean complementation supplies the reverse inequality.  The final theorem
then transports the two-sided estimate through the exact physical/support-gas
bridges, so it is stated for the literal finite physical laws as well.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityAlgebra
import YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierTail
import YMGap.Continuum.Z4CouplingParametricTargetCylinderStability

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStability

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CouplingParametricTargetCylinderStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierTail
open YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierTail
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityAlgebra
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Central connected-residue modulus -/

def centralCouplingSlabConditionalBoundaryEpsilon (half : Nat) : Q' :=
  Q'.ofNat 2 *
    (anchorDecoratedEffectiveRatio ^ (half + 1) * Q'.ofNat 2)

theorem centralCouplingSlabConditionalBoundaryEpsilon_nonnegative
    (half : Nat) :
    (0 : Q') ≤ centralCouplingSlabConditionalBoundaryEpsilon half := by
  unfold centralCouplingSlabConditionalBoundaryEpsilon
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative (half + 1))
      (by decide))

theorem centralCouplingNormalizedSlabConnectedCylinderResidue_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    couplingNormalizedSlabConnectedCylinderResidue
        coupling hcoupling cutoff (centralExtent half)
        (centralSlabCanonicalRoots half hhalf) predicate ≤
      centralCouplingSlabConditionalBoundaryEpsilon half := by
  unfold couplingNormalizedSlabConnectedCylinderResidue
    centralCouplingSlabConditionalBoundaryEpsilon
  apply Q'.divPos_le_of_le_mul
  simpa [centralAmbient] using
    (centralCouplingSpinSummedSlabConnectedCylinderResidue_le_tail
      hcoupling hle cutoff hhalf predicate)

theorem centralCouplingAmbientProbability_sub_givenSlab_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (centralAmbient half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) -
        couplingParametricKCompatibleGivenSlabProbability
          coupling hcoupling cutoff (centralExtent half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) ≤
      centralCouplingSlabConditionalBoundaryEpsilon half := by
  have halgebra :=
    couplingAmbientProbability_sub_givenSlab_le_normalizedResidue
      coupling hcoupling cutoff (centralExtent half)
      (centralSlabCanonicalRoots half hhalf) predicate
  exact Q'.le_trans' _ _ _ (by
    simpa [centralAmbient] using halgebra)
    (centralCouplingNormalizedSlabConnectedCylinderResidue_le
      hcoupling hle cutoff hhalf predicate)

/-! ## 2. Complement normalization of the conditional law -/

private theorem filter_and_eq_filter_filter {A : Type}
    (first second : A → Bool) (source : List A) :
    source.filter (fun item => first item && second item) =
      (source.filter first).filter second := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (first item) (second item)

theorem couplingSlabRestrictedNumerator_add_complement_eqv_support
    (coupling : Q') (cutoff extent : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (canonicalSlabRestrictedEvent extent event) +
        couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (canonicalSlabRestrictedEvent extent
            (fun family => !(event family))) ≈
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
        (canonicalFamilySlabSupportedB extent) := by
  unfold couplingParametricKCompatibleSupportEventNumerator
    canonicalSlabRestrictedEvent
  rw [filter_and_eq_filter_filter,
    filter_and_eq_filter_filter]
  exact Q'.eqv_symm
    (listQSum_filter_partition
      (couplingParametricKSupportFamilyActivity
        coupling cutoff (extent + 1)) event
      ((canonicalCompatibleAmbientFamilies (extent + 1)).filter
        (canonicalFamilySlabSupportedB extent)))

private theorem add_divPos_eqv_local
    (p p' q : Q') (hq : (0 : Q') < q) :
    Q'.divPos p q hq + Q'.divPos p' q hq ≈
      Q'.divPos (p + p') q hq :=
  Q'.eqv_symm (Q'.add_mul_eqv p p' (Q'.recipPos q hq))

theorem couplingParametricKCompatibleGivenSlabProbability_add_complement_eqv_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat) (event : List (List Nat) → Bool) :
    couplingParametricKCompatibleGivenSlabProbability
          coupling hcoupling cutoff extent event +
        couplingParametricKCompatibleGivenSlabProbability
          coupling hcoupling cutoff extent
          (fun family => !(event family)) ≈
      (1 : Q') := by
  have hsplit :=
    couplingSlabRestrictedNumerator_add_complement_eqv_support
      coupling cutoff extent event
  unfold couplingParametricKCompatibleGivenSlabProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
        (canonicalSlabRestrictedEvent extent event))
      (couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
        (canonicalSlabRestrictedEvent extent
          (fun family => !(event family))))
      (couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
        (canonicalFamilySlabSupportedB extent))
      (couplingParametricKCompatibleSlabSupportNumerator_pos
        hcoupling cutoff extent)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos
        (couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent))
        (couplingParametricKCompatibleSlabSupportNumerator_pos
          hcoupling cutoff extent)) hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff (extent + 1)
      (canonicalFamilySlabSupportedB extent))
    (couplingParametricKCompatibleSlabSupportNumerator_pos
      hcoupling cutoff extent)

/-! ## 3. Reverse compatible-law direction and absolute modulus -/

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

theorem centralCouplingGivenSlab_sub_ambientProbability_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleGivenSlabProbability
          coupling hcoupling cutoff (centralExtent half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) -
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (centralAmbient half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) ≤
      centralCouplingSlabConditionalBoundaryEpsilon half := by
  let event := slabMarkedCylinderEvent
    (centralSlabCanonicalRoots half hhalf) predicate
  let complementEvent := slabMarkedCylinderEvent
    (centralSlabCanonicalRoots half hhalf)
    (complementSlabPredicate predicate)
  have hcomplement := centralCouplingAmbientProbability_sub_givenSlab_le
    hcoupling hle cutoff hhalf (complementSlabPredicate predicate)
  have hpointwise : complementEvent =
      (fun family => !(event family)) := by
    funext family
    rfl
  have hambientSum :
      couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (centralAmbient half) event +
        couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (centralAmbient half)
            complementEvent ≈ (1 : Q') := by
    rw [hpointwise]
    exact
      couplingParametricKCompatibleEventProbability_add_complement_eqv_one
        hcoupling cutoff (centralAmbient half) event
  have hslabSum :
      couplingParametricKCompatibleGivenSlabProbability
            coupling hcoupling cutoff (centralExtent half) event +
        couplingParametricKCompatibleGivenSlabProbability
            coupling hcoupling cutoff (centralExtent half)
            complementEvent ≈ (1 : Q') := by
    rw [hpointwise]
    exact
      couplingParametricKCompatibleGivenSlabProbability_add_complement_eqv_one
        coupling hcoupling cutoff (centralExtent half) event
  have hreorder :
      couplingParametricKCompatibleGivenSlabProbability
            coupling hcoupling cutoff (centralExtent half) event -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (centralAmbient half) event ≈
        couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (centralAmbient half)
            complementEvent -
          couplingParametricKCompatibleGivenSlabProbability
            coupling hcoupling cutoff (centralExtent half)
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

theorem centralCouplingAmbient_givenSlabProbability_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (centralAmbient half)
            (slabMarkedCylinderEvent
              (centralSlabCanonicalRoots half hhalf) predicate) -
          couplingParametricKCompatibleGivenSlabProbability
            coupling hcoupling cutoff (centralExtent half)
            (slabMarkedCylinderEvent
              (centralSlabCanonicalRoots half hhalf) predicate)) ≤
      centralCouplingSlabConditionalBoundaryEpsilon half := by
  apply Q'.abs_le
  · have hreverse := centralCouplingGivenSlab_sub_ambientProbability_le
      hcoupling hle cutoff hhalf predicate
    have hneg := Q'.neg_le_neg hreverse
    exact Q'.le_trans' _ _ _ hneg
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (sub_swap_eqv_neg_local
            (couplingParametricKCompatibleGivenSlabProbability
              coupling hcoupling cutoff (centralExtent half)
              (slabMarkedCylinderEvent
                (centralSlabCanonicalRoots half hhalf) predicate))
            (couplingParametricKCompatibleSupportEventProbability
              coupling hcoupling cutoff (centralAmbient half)
              (slabMarkedCylinderEvent
                (centralSlabCanonicalRoots half hhalf) predicate)))))
  · exact centralCouplingAmbientProbability_sub_givenSlab_le
      hcoupling hle cutoff hhalf predicate

/-! ## 4. Literal physical-law statement -/

theorem centralCouplingPhysicalDifference_eqv_compatible
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    couplingKFamilyEventProbability coupling hcoupling cutoff
          (centralAmbient half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) -
        couplingParametricKPhysicalGivenSlabProbability
          coupling hcoupling cutoff (centralExtent half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) ≈
      couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (centralAmbient half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) -
        couplingParametricKCompatibleGivenSlabProbability
          coupling hcoupling cutoff (centralExtent half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalRoots half hhalf) predicate) :=
  sub_eqv_both_local
    (couplingKFamilyEventProbability_eqv_compatible
      coupling hcoupling cutoff (centralAmbient half)
      (slabMarkedCylinderEvent
        (centralSlabCanonicalRoots half hhalf) predicate))
    (couplingParametricKPhysicalGivenSlabProbability_eqv_compatible
      coupling hcoupling cutoff (centralExtent half)
      (slabMarkedCylinderEvent
        (centralSlabCanonicalRoots half hhalf) predicate))

/-- The uniform finite-cutoff two-sided law for the actual physical ambient
ensemble and the actual corrected-slab physical conditional ensemble. -/
theorem centralCouplingPhysicalAmbient_givenSlabProbability_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingKFamilyEventProbability coupling hcoupling cutoff
            (centralAmbient half)
            (slabMarkedCylinderEvent
              (centralSlabCanonicalRoots half hhalf) predicate) -
          couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff (centralExtent half)
            (slabMarkedCylinderEvent
              (centralSlabCanonicalRoots half hhalf) predicate)) ≤
      centralCouplingSlabConditionalBoundaryEpsilon half := by
  have hbridge := centralCouplingPhysicalDifference_eqv_compatible
    coupling hcoupling cutoff hhalf predicate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hbridge))
    (centralCouplingAmbient_givenSlabProbability_abs_sub_le
      hcoupling hle cutoff hhalf predicate)

#print axioms centralCouplingNormalizedSlabConnectedCylinderResidue_le
#print axioms centralCouplingAmbientProbability_sub_givenSlab_le
#print axioms couplingParametricKCompatibleGivenSlabProbability_add_complement_eqv_one
#print axioms centralCouplingGivenSlab_sub_ambientProbability_le
#print axioms centralCouplingAmbient_givenSlabProbability_abs_sub_le
#print axioms centralCouplingPhysicalDifference_eqv_compatible
#print axioms centralCouplingPhysicalAmbient_givenSlabProbability_abs_sub_le

end YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStability
