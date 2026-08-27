/-
# A uniform pinned-size tail for the face-event cylinder compiler

The complete strict-cylinder presentation of one occupied-face event has one
root for every canonical polymer containing that face, so its root list grows
with the finite box.  Here we truncate that list by polymer size and show that
the discarded event has a box-independent geometric probability bound.

On a corrected-compatible family, the full face event is the disjoint union
of the truncated cylinder event and its false-negative remainder.  Any such
remainder contains a face-pinned polymer whose size is at least the truncation
floor.  The existing pinned KP estimate therefore gives the explicit bound

  `2 * anchorEffectiveRatio ^ sizeFloor`.

This supplies the constructive observable-tail modulus needed before passing
the face event into the fixed-root thermodynamic strict-cylinder system.  It
does not yet prove the spatial transport/completeness statement identifying
the same truncated root chart in every larger centered box.
-/

import YMGap.Continuum.Z4CanonicalCylinderFunctional
import YMGap.Continuum.Z4CanonicalFaceEventCylinderCompiler

namespace YMGap.Continuum.Z4CanonicalFaceEventPinnedTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderFunctional
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFaceEventCylinderCompiler
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Size-truncated strict cylinders and the large-component event -/

/-- Canonical polymers pinned at `face` whose size is strictly below the
chosen truncation floor. -/
def canonicalPinnedBelowSizePolymers
    (n face sizeFloor : Nat) : List (List Nat) :=
  (canonicalPinnedLayerPolymers n face).filter
    (fun polymer => decide (polymer.length < sizeFloor))

theorem mem_canonicalPinnedBelowSizePolymers_iff
    {n face sizeFloor : Nat} {polymer : List Nat} :
    polymer ∈ canonicalPinnedBelowSizePolymers n face sizeFloor ↔
      polymer ∈ canonicalSurfacePolymers n ∧
        face ∈ polymer ∧ polymer.length < sizeFloor := by
  unfold canonicalPinnedBelowSizePolymers
  rw [List.mem_filter, mem_canonicalPinnedLayerPolymers_iff]
  simp only [decide_eq_true_eq, and_assoc]

def canonicalFaceTruncatedCylinderEvent
    (n face sizeFloor : Nat) : List (List Nat) → Bool :=
  sourceCylinderEvent
    (canonicalPinnedBelowSizePolymers n face sizeFloor)
    canonicalFaceCylinderPredicate

def canonicalFaceTruncatedStrictCylinderVector
    (base face sizeFloor : Nat) : StrictJointCylinderVector base where
  roots := canonicalPinnedBelowSizePolymers base face sizeFloor
  rootsCanonical := fun _polymer hpolymer =>
    (mem_canonicalPinnedBelowSizePolymers_iff.mp hpolymer).1
  coefficient := canonicalFaceCylinderCoefficient

/-- Mark the discarded part of the pinned layer. -/
def canonicalPinnedLargeMark
    (face sizeFloor : Nat) (polymer : List Nat) : Bool :=
  canonicalContainsFaceB face polymer &&
    decide (sizeFloor ≤ polymer.length)

def canonicalPinnedLargeFamilyEvent
    (face sizeFloor : Nat) (family : List (List Nat)) : Bool :=
  family.any (canonicalPinnedLargeMark face sizeFloor)

/-- The literal false-negative event of the truncated face cylinder. -/
def canonicalFaceTruncationRemainderEvent
    (n face sizeFloor : Nat) (family : List (List Nat)) : Bool :=
  familyContainsFaceB face family &&
    !(canonicalFaceTruncatedCylinderEvent n face sizeFloor family)

/-! ## 2. Exact compatible-family event decomposition -/

theorem canonicalFaceTruncatedCylinderEvent_implies_face
    {n face sizeFloor : Nat} {family : List (List Nat)}
    (htruncated :
      canonicalFaceTruncatedCylinderEvent n face sizeFloor family = true) :
    familyContainsFaceB face family = true := by
  unfold canonicalFaceTruncatedCylinderEvent sourceCylinderEvent cylinderEvent
    canonicalFaceCylinderPredicate familyOccurrenceFingerprint at htruncated
  obtain ⟨bit, hbit, hbitTrue⟩ := List.any_eq_true.mp htruncated
  obtain ⟨polymer, hpolymer, hcontains⟩ := List.mem_map.mp hbit
  have hoccurs : polymer ∈ family := by
    unfold familyContainsPolymerB at hcontains
    exact of_decide_eq_true (hcontains.trans hbitTrue)
  have hfacePolymer : face ∈ polymer :=
    (mem_canonicalPinnedBelowSizePolymers_iff.mp hpolymer).2.1
  exact (familyContainsFaceB_true_iff face family).2
    ⟨polymer, hoccurs, hfacePolymer⟩

theorem canonicalFaceTruncationRemainder_implies_large
    {n face sizeFloor : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n)
    (hremainder : canonicalFaceTruncationRemainderEvent
      n face sizeFloor family = true) :
    canonicalPinnedLargeFamilyEvent face sizeFloor family = true := by
  have hparts := (Bool.and_eq_true _ _).mp hremainder
  obtain ⟨polymer, hpolymerFamily, hfacePolymer⟩ :=
    (familyContainsFaceB_true_iff face family).1 hparts.1
  have hpolymerCanonical : polymer ∈ canonicalSurfacePolymers n :=
    compatibleAmbientFamily_member_ambient hfamily hpolymerFamily
  have hnotSmall : ¬ polymer.length < sizeFloor := by
    intro hsmall
    have hpolymerSmall : polymer ∈
        canonicalPinnedBelowSizePolymers n face sizeFloor :=
      mem_canonicalPinnedBelowSizePolymers_iff.mpr
        ⟨hpolymerCanonical, hfacePolymer, hsmall⟩
    have htruncated : canonicalFaceTruncatedCylinderEvent
        n face sizeFloor family = true := by
      unfold canonicalFaceTruncatedCylinderEvent sourceCylinderEvent
        cylinderEvent canonicalFaceCylinderPredicate
        familyOccurrenceFingerprint
      apply List.any_eq_true.mpr
      refine ⟨true, ?_, rfl⟩
      apply List.mem_map.mpr
      refine ⟨polymer, hpolymerSmall, ?_⟩
      unfold familyContainsPolymerB
      exact decide_eq_true hpolymerFamily
    rw [htruncated] at hparts
    cases hparts.2
  unfold canonicalPinnedLargeFamilyEvent
  apply List.any_eq_true.mpr
  refine ⟨polymer, hpolymerFamily, ?_⟩
  unfold canonicalPinnedLargeMark canonicalContainsFaceB
  apply (Bool.and_eq_true _ _).mpr
  exact ⟨decide_eq_true hfacePolymer, decide_eq_true (by omega)⟩

/-- On every corrected-compatible family, the full face event is exactly the
truncated cylinder plus its false-negative remainder. -/
theorem familyContainsFaceB_eq_truncated_or_remainder
    {n face sizeFloor : Nat} {family : List (List Nat)}
    (_hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    familyContainsFaceB face family =
      (canonicalFaceTruncatedCylinderEvent n face sizeFloor family ||
        canonicalFaceTruncationRemainderEvent
          n face sizeFloor family) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hface
    cases htruncated : canonicalFaceTruncatedCylinderEvent
        n face sizeFloor family with
    | false =>
        apply (Bool.or_eq_true _ _).mpr
        apply Or.inr
        unfold canonicalFaceTruncationRemainderEvent
        rw [htruncated]
        simpa only [Bool.not_false, Bool.and_true] using hface
    | true =>
        exact (Bool.or_eq_true _ _).mpr (Or.inl rfl)
  · intro hunion
    rcases (Bool.or_eq_true _ _).mp hunion with htruncated | hremainder
    · exact canonicalFaceTruncatedCylinderEvent_implies_face htruncated
    · exact (Bool.and_eq_true _ _).mp hremainder |>.1

theorem truncated_remainder_disjoint
    (n face sizeFloor : Nat) (family : List (List Nat))
    (htruncated : canonicalFaceTruncatedCylinderEvent
      n face sizeFloor family = true) :
    canonicalFaceTruncationRemainderEvent
      n face sizeFloor family = false := by
  unfold canonicalFaceTruncationRemainderEvent
  rw [htruncated]
  simp only [Bool.not_true, Bool.and_false]

/-! ## 3. The uniform activity tail for discarded pinned roots -/

def canonicalPinnedLargePolymers
    (n face sizeFloor : Nat) : List (List Nat) :=
  (canonicalSurfacePolymers n).filter
    (canonicalPinnedLargeMark face sizeFloor)

theorem mem_canonicalPinnedLargePolymers_iff
    {n face sizeFloor : Nat} {polymer : List Nat} :
    polymer ∈ canonicalPinnedLargePolymers n face sizeFloor ↔
      polymer ∈ canonicalSurfacePolymers n ∧
        face ∈ polymer ∧ sizeFloor ≤ polymer.length := by
  unfold canonicalPinnedLargePolymers canonicalPinnedLargeMark
    canonicalContainsFaceB
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, decide_eq_true_eq]

def canonicalPinnedLargeSizeLayers
    (n face sizeFloor : Nat) : List (List Nat) :=
  (List.range ((physicalFaceEdges n).length + 1)).flatMap (fun offset =>
    canonicalPinnedSizePolymers n face (sizeFloor + offset))

private theorem length_le_of_mem_sublists_local {A : Type} :
    ∀ (ambient support : List A), support ∈ sublists ambient →
      support.length ≤ ambient.length
  | [], support, hsupport => by
      have heq : support = [] := List.mem_singleton.mp hsupport
      rw [heq]
      exact Nat.le_refl 0
  | head :: tail, support, hsupport => by
      rw [sublists_cons'] at hsupport
      rcases List.mem_append.mp hsupport with htail | hhead
      · have ih := length_le_of_mem_sublists_local tail support htail
        simp only [List.length_cons]
        omega
      · obtain ⟨rest, hrest, heq⟩ := List.mem_map.mp hhead
        rw [← heq]
        have ih := length_le_of_mem_sublists_local tail rest hrest
        simp only [List.length_cons]
        omega

theorem canonicalPinnedLargePolymer_mem_sizeLayers
    {n face sizeFloor : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈
      canonicalPinnedLargePolymers n face sizeFloor) :
    polymer ∈ canonicalPinnedLargeSizeLayers n face sizeFloor := by
  have hfacts := mem_canonicalPinnedLargePolymers_iff.mp hpolymer
  have hlength : polymer.length ≤ (physicalFaceEdges n).length :=
    length_le_of_mem_sublists_local (physicalFaceEdges n) polymer
      (canonicalSurfacePolymer_mem_faceSupports hfacts.1)
  unfold canonicalPinnedLargeSizeLayers
  apply List.mem_flatMap.mpr
  refine ⟨polymer.length - sizeFloor, List.mem_range.mpr ?_, ?_⟩
  · omega
  · apply mem_canonicalPinnedSizePolymers_iff.mpr
    exact ⟨hfacts.1, hfacts.2.1, by omega⟩

private theorem listQSum_range_eqv_finSum_local (value : Nat → Q') :
    ∀ cutoff : Nat,
      listQSum value (List.range cutoff) ≈ finSum value cutoff
  | 0 => Q'.eqv_refl 0
  | cutoff + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _ _ _
        (listQSum_append value (List.range cutoff) [cutoff])
        (Q'.add_eqv_congr'
          (listQSum_range_eqv_finSum_local value cutoff)
          (Q'.eqv_of_eq (Q'.add_zero' (value cutoff))))

theorem canonicalPinnedLargeSizeLayers_activity_eqv
    (n face sizeFloor : Nat) :
    listQSum (canonicalSurfaceActivity anchorCoupling n)
        (canonicalPinnedLargeSizeLayers n face sizeFloor) ≈
      canonicalPinnedShiftedActivitySum n face sizeFloor
        ((physicalFaceEdges n).length + 1) := by
  unfold canonicalPinnedLargeSizeLayers canonicalPinnedShiftedActivitySum
  exact Q'.eqv_trans _ _ _
    (listQSum_flatMap (canonicalSurfaceActivity anchorCoupling n)
      (fun offset =>
        canonicalPinnedSizePolymers n face (sizeFloor + offset))
      (List.range ((physicalFaceEdges n).length + 1)))
    (listQSum_range_eqv_finSum_local
      (fun offset =>
        canonicalPinnedSizeActivitySum n face (sizeFloor + offset))
      ((physicalFaceEdges n).length + 1))

def canonicalPinnedLargeActivity
    (n face sizeFloor : Nat) : Q' :=
  markedActivitySum (canonicalSurfaceActivity anchorCoupling n)
    (canonicalPinnedLargeMark face sizeFloor)
    (canonicalSurfacePolymers n)

theorem canonicalPinnedLargeActivity_le_shifted
    (n face sizeFloor : Nat) :
    canonicalPinnedLargeActivity n face sizeFloor ≤
      canonicalPinnedShiftedActivitySum n face sizeFloor
        ((physicalFaceEdges n).length + 1) := by
  have hinjection :
      listQSum (canonicalSurfaceActivity anchorCoupling n)
          (canonicalPinnedLargePolymers n face sizeFloor) ≤
        listQSum (canonicalSurfaceActivity anchorCoupling n)
          (canonicalPinnedLargeSizeLayers n face sizeFloor) := by
    apply listQSum_le_of_injective
      (canonicalPinnedLargePolymers n face sizeFloor)
      (canonicalPinnedLargeSizeLayers n face sizeFloor)
      (canonicalSurfaceActivity anchorCoupling n)
      (canonicalSurfaceActivity anchorCoupling n)
      (fun polymer => polymer)
    · unfold canonicalPinnedLargePolymers
      exact List.filter_sublist.nodup (canonicalSurfacePolymers_nodup n)
    · intro polymer hpolymer
      exact canonicalPinnedLargePolymer_mem_sizeLayers hpolymer
    · intro left _ right _ heq
      exact heq
    · intro polymer _
      exact Q'.le_refl' _
    · intro polymer _
      exact canonicalSurfacePolymer_activity_nonnegative n polymer
  change listQSum (canonicalSurfaceActivity anchorCoupling n)
      (canonicalPinnedLargePolymers n face sizeFloor) ≤ _
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_of_eqv
      (canonicalPinnedLargeSizeLayers_activity_eqv n face sizeFloor))

/-- The discarded single-polymer activity is bounded geometrically,
uniformly in the finite box and pinned face. -/
theorem canonicalPinnedLargeActivity_le_tail
    (n face sizeFloor : Nat) :
    canonicalPinnedLargeActivity n face sizeFloor ≤
      Q'.ofNat 2 * anchorEffectiveRatio ^ sizeFloor := by
  exact Q'.le_trans' _ _ _
    (canonicalPinnedLargeActivity_le_shifted n face sizeFloor)
    (Q'.le_trans' _ _ _
      (canonicalPinnedShiftedActivitySum_le_KPSum n face sizeFloor
        ((physicalFaceEdges n).length + 1))
      (canonicalPinnedShiftedKPSum_le_tail n face sizeFloor
        ((physicalFaceEdges n).length + 1)))

/-! ## 4. Normalized probability approximation -/

private theorem anchorEventProbability_mono_on_compatible
    (n : Nat) (first second : List (List Nat) → Bool)
    (himp : ∀ family,
      family ∈ canonicalCompatibleAmbientFamilies n →
      first family = true → second family = true) :
    anchorEventProbability n first ≤ anchorEventProbability n second := by
  have hnumerator : anchorEventNumerator n first ≤
      anchorEventNumerator n second := by
    unfold anchorEventNumerator
    apply listQSum_le_of_injective
      ((canonicalCompatibleAmbientFamilies n).filter first)
      ((canonicalCompatibleAmbientFamilies n).filter second)
      (canonicalSurfaceFamilyActivity anchorCoupling n)
      (canonicalSurfaceFamilyActivity anchorCoupling n)
      (fun family => family)
    · exact List.filter_sublist.nodup
        (canonicalCompatibleAmbientFamilies_nodup n)
    · intro family hfamily
      have hparts := List.mem_filter.mp hfamily
      exact List.mem_filter.mpr
        ⟨hparts.1, himp family hparts.1 hparts.2⟩
    · intro left _ right _ heq
      exact heq
    · intro family _
      exact Q'.le_refl' _
    · intro family _
      exact canonicalSurfaceFamilyActivity_nonnegative n family
  unfold anchorEventProbability Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hnumerator
    (Q'.le_of_lt
      (Q'.recipPos_pos (anchorCanonicalPartition n)
        (anchorCanonicalPartition_pos n)))

private theorem anchorEventProbability_eqv_on_compatible
    (n : Nat) (first second : List (List Nat) → Bool)
    (hevent : ∀ family,
      family ∈ canonicalCompatibleAmbientFamilies n →
      first family = second family) :
    anchorEventProbability n first ≈ anchorEventProbability n second := by
  have hfilter :
      (canonicalCompatibleAmbientFamilies n).filter first =
        (canonicalCompatibleAmbientFamilies n).filter second := by
    apply List.filter_congr
    intro family hfamily
    exact hevent family hfamily
  unfold anchorEventProbability anchorEventNumerator
  rw [hfilter]
  exact Q'.eqv_refl _

theorem anchorPinnedLargeFamilyEventProbability_le_activity
    (n face sizeFloor : Nat) :
    anchorEventProbability n
        (canonicalPinnedLargeFamilyEvent face sizeFloor) ≤
      canonicalPinnedLargeActivity n face sizeFloor := by
  have hnumerator := markedEventNumerator_le_activitySum_mul_partition
    (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity anchorCoupling n)
    (canonicalSurfacePolymer_activity_nonnegative n)
    (canonicalPinnedLargeMark face sizeFloor)
    (canonicalSurfacePolymers n)
  apply Q'.divPos_le_of_le_mul
  have hnumEq := canonicalPolymerEventNumerator_eqv_anchor n
    (canonicalPinnedLargeFamilyEvent face sizeFloor)
  have hpartitionEq := anchorCanonicalPartition_eqv_generic n
  have hrightEq :
      canonicalPinnedLargeActivity n face sizeFloor *
          canonicalPolymerPartition anchorCoupling n
            (canonicalSurfacePolymers n) ≈
        canonicalPinnedLargeActivity n face sizeFloor *
          anchorCanonicalPartition n :=
    Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hpartitionEq)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hnumEq)
    (Q'.le_trans' _ _ _ hnumerator (Q'.le_of_eqv hrightEq))

/-- Uniform probability tail for the large pinned component omitted by the
truncated face cylinder. -/
theorem anchorPinnedLargeFamilyEventProbability_le_tail
    (n face sizeFloor : Nat) :
    anchorEventProbability n
        (canonicalPinnedLargeFamilyEvent face sizeFloor) ≤
      Q'.ofNat 2 * anchorEffectiveRatio ^ sizeFloor := by
  exact Q'.le_trans' _ _ _
    (anchorPinnedLargeFamilyEventProbability_le_activity n face sizeFloor)
    (canonicalPinnedLargeActivity_le_tail n face sizeFloor)

theorem anchorFaceTruncationRemainderProbability_le_tail
    (n face sizeFloor : Nat) :
    anchorEventProbability n
        (canonicalFaceTruncationRemainderEvent n face sizeFloor) ≤
      Q'.ofNat 2 * anchorEffectiveRatio ^ sizeFloor := by
  exact Q'.le_trans' _ _ _
    (anchorEventProbability_mono_on_compatible n
      (canonicalFaceTruncationRemainderEvent n face sizeFloor)
      (canonicalPinnedLargeFamilyEvent face sizeFloor)
      (fun _family hfamily hremainder =>
        canonicalFaceTruncationRemainder_implies_large
          hfamily hremainder))
    (anchorPinnedLargeFamilyEventProbability_le_tail n face sizeFloor)

/-- The truncated cylinder probability lies below the full face probability. -/
theorem anchorFaceTruncatedCylinderProbability_le_full
    (n face sizeFloor : Nat) :
    anchorEventProbability n
        (canonicalFaceTruncatedCylinderEvent n face sizeFloor) ≤
      anchorEventProbability n (familyContainsFaceB face) := by
  exact anchorEventProbability_mono_on_compatible n _ _
    (fun _family _hfamily htruncated =>
      canonicalFaceTruncatedCylinderEvent_implies_face htruncated)

/-- The complete face probability differs from the size-truncated strict
cylinder by at most the explicit uniform pinned tail. -/
theorem anchorFaceProbability_le_truncated_add_tail
    (n face sizeFloor : Nat) :
    anchorEventProbability n (familyContainsFaceB face) ≤
      anchorEventProbability n
          (canonicalFaceTruncatedCylinderEvent n face sizeFloor) +
        Q'.ofNat 2 * anchorEffectiveRatio ^ sizeFloor := by
  let truncated := canonicalFaceTruncatedCylinderEvent n face sizeFloor
  let remainder := canonicalFaceTruncationRemainderEvent n face sizeFloor
  have hevent : anchorEventProbability n (familyContainsFaceB face) ≈
      anchorEventProbability n
        (fun family => truncated family || remainder family) :=
    anchorEventProbability_eqv_on_compatible n _ _
      (fun _family hfamily =>
        familyContainsFaceB_eq_truncated_or_remainder hfamily)
  have hadd : anchorEventProbability n
        (fun family => truncated family || remainder family) ≈
      anchorEventProbability n truncated +
        anchorEventProbability n remainder :=
    anchorEventProbability_union_eqv_add n truncated remainder
      (truncated_remainder_disjoint n face sizeFloor)
  have hdecomposition :
      anchorEventProbability n (familyContainsFaceB face) ≈
        anchorEventProbability n truncated +
          anchorEventProbability n remainder :=
    Q'.eqv_trans _ _ _ hevent hadd
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdecomposition)
    (Q'.add_le_add_left _ _ _
      (anchorFaceTruncationRemainderProbability_le_tail
        n face sizeFloor))

#print axioms mem_canonicalPinnedBelowSizePolymers_iff
#print axioms canonicalFaceTruncationRemainder_implies_large
#print axioms familyContainsFaceB_eq_truncated_or_remainder
#print axioms canonicalPinnedLargePolymer_mem_sizeLayers
#print axioms canonicalPinnedLargeSizeLayers_activity_eqv
#print axioms canonicalPinnedLargeActivity_le_tail
#print axioms anchorPinnedLargeFamilyEventProbability_le_tail
#print axioms anchorFaceTruncationRemainderProbability_le_tail
#print axioms anchorFaceTruncatedCylinderProbability_le_full
#print axioms anchorFaceProbability_le_truncated_add_tail

end YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
