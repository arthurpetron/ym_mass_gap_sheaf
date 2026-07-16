/-
# Cross-volume transport of a canonical local occurrence observable

For a canonical polymer in a smaller box, occurrence of that polymer is
transported exactly to occurrence of its geometric image in a larger box.
This module proves that the embedded event numerator is the smaller-box event
numerator, not merely an unrelated subensemble sum.  Consequently the general
partition-ratio split becomes an exact volume-to-volume identity for a concrete
local observable.

The remaining term is still the connected boundary influence.  No decay is
asserted here.
-/

import YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
import YMGap.Continuum.Z4CanonicalPolymerPartitionRatio

namespace YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Occurrence is invariant under canonical family transport -/

theorem familyContainsPolymerB_embedded_transport
    {n m : Nat} (hnm : n ≤ m) {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    familyContainsPolymerB polymer family =
      familyContainsPolymerB (transportPolymer n m polymer)
        (embeddedTransportFamily n m family) := by
  unfold familyContainsPolymerB
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hsource
    have hmem : polymer ∈ family := of_decide_eq_true hsource
    apply decide_eq_true
    exact (mem_embeddedTransportFamily_iff hnm hfamily
      (transportPolymer n m polymer)).2 ⟨polymer, hmem, rfl⟩
  · intro htarget
    have hmem : transportPolymer n m polymer ∈
        embeddedTransportFamily n m family := of_decide_eq_true htarget
    obtain ⟨source, hsource, heq⟩ :=
      (mem_embeddedTransportFamily_iff hnm hfamily
        (transportPolymer n m polymer)).1 hmem
    have hsourceAmbient :=
      compatibleAmbientFamily_member_ambient hfamily hsource
    have hequal : polymer = source :=
      transportPolymer_injective_on_canonical hnm
        hpolymer hsourceAmbient heq
    apply decide_eq_true
    rw [hequal]
    exact hsource

def sourceOccurrenceEvent (polymer : List Nat) :
    List (List Nat) → Bool :=
  familyContainsPolymerB polymer

def targetOccurrenceEvent (n m : Nat) (polymer : List Nat) :
    List (List Nat) → Bool :=
  familyContainsPolymerB (transportPolymer n m polymer)

def embeddedSourceOccurrenceFamilies
    (n m : Nat) (polymer : List Nat) : List (List (List Nat)) :=
  ((canonicalCompatibleAmbientFamilies n).filter
      (sourceOccurrenceEvent polymer)).map
    (embeddedTransportFamily n m)

def embeddedTargetOccurrenceFamilies
    (n m : Nat) (polymer : List Nat) : List (List (List Nat)) :=
  ((canonicalCompatibleAmbientFamilies m).filter
      (targetOccurrenceEvent n m polymer)).filter
    (embeddedFamilyB n m)

theorem embeddedSourceOccurrenceFamilies_eq_filter
    {n m : Nat} (hnm : n ≤ m) {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    embeddedSourceOccurrenceFamilies n m polymer =
      (embeddedCompatibleFamilies n m).filter
        (targetOccurrenceEvent n m polymer) := by
  unfold embeddedSourceOccurrenceFamilies embeddedCompatibleFamilies
  rw [List.filter_map]
  apply congrArg (List.map (embeddedTransportFamily n m))
  apply List.filter_congr
  intro family hfamily
  unfold sourceOccurrenceEvent targetOccurrenceEvent
  exact familyContainsPolymerB_embedded_transport
    hnm hpolymer hfamily

theorem embeddedTargetOccurrenceFamilies_eq_filter
    (n m : Nat) (polymer : List Nat) :
    embeddedTargetOccurrenceFamilies n m polymer =
      (embeddedTargetFamilies n m).filter
        (targetOccurrenceEvent n m polymer) := by
  unfold embeddedTargetOccurrenceFamilies embeddedTargetFamilies
    embeddedFamilyB
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro family _
  cases decide (family ∈ embeddedCompatibleFamilies n m) <;>
    cases targetOccurrenceEvent n m polymer family <;> rfl

theorem embeddedSourceOccurrenceFamilies_perm_target
    {n m : Nat} (hnm : n ≤ m) {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    (embeddedSourceOccurrenceFamilies n m polymer).Perm
      (embeddedTargetOccurrenceFamilies n m polymer) := by
  rw [embeddedSourceOccurrenceFamilies_eq_filter hnm hpolymer,
    embeddedTargetOccurrenceFamilies_eq_filter]
  exact (embeddedCompatibleFamilies_perm_target hnm).filter _

/-! ## 2. Exact transport of the event numerator -/

private theorem listQSum_map_eqv_local {A B : Type}
    (sourceWeight : A → Q') (targetWeight : B → Q')
    (reindex : A → B) :
    ∀ xs : List A,
      (∀ item, item ∈ xs →
        sourceWeight item ≈ targetWeight (reindex item)) →
      listQSum sourceWeight xs ≈
        listQSum targetWeight (xs.map reindex)
  | [], _ => Q'.eqv_refl _
  | head :: tail, h =>
      Q'.add_eqv_congr'
        (h head List.mem_cons_self)
        (listQSum_map_eqv_local sourceWeight targetWeight reindex tail
          (fun item hitem =>
            h item (List.mem_cons_of_mem head hitem)))

theorem anchorOccurrenceNumerator_eqv_embedded
    {n m : Nat} (hnm : n ≤ m) {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    anchorEventNumerator n (sourceOccurrenceEvent polymer) ≈
      embeddedTargetEventNumerator n m
        (targetOccurrenceEvent n m polymer) := by
  have hmap :
      anchorEventNumerator n (sourceOccurrenceEvent polymer) ≈
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
          (embeddedSourceOccurrenceFamilies n m polymer) := by
    unfold anchorEventNumerator embeddedSourceOccurrenceFamilies
    apply listQSum_map_eqv_local
    intro family hfamily
    have hcompatible := (List.mem_filter.mp hfamily).1
    exact compatibleFamilyActivity_embedded_transport
      anchorCoupling hnm hcompatible
  have hperm := listQSum_perm
    (canonicalSurfaceFamilyActivity anchorCoupling m)
    (embeddedSourceOccurrenceFamilies_perm_target hnm hpolymer)
  refine Q'.eqv_trans _ _ _ hmap ?_
  change listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
      (embeddedSourceOccurrenceFamilies n m polymer) ≈
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
      (embeddedTargetOccurrenceFamilies n m polymer)
  exact hperm

/-! ## 3. The concrete volume-to-volume cross difference -/

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

/-- Exact numerator of the difference between the larger- and smaller-box
occurrence probabilities.  The only residual terms are the genuinely new
boundary ensemble and its occurrence subensemble. -/
theorem anchorOccurrenceCrossDifference_eqv_boundary
    {n m : Nat} (hnm : n ≤ m) {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    anchorEventNumerator m (targetOccurrenceEvent n m polymer) *
          anchorCanonicalPartition n -
        anchorEventNumerator n (sourceOccurrenceEvent polymer) *
          anchorCanonicalPartition m ≈
      boundaryTargetEventNumerator n m
            (targetOccurrenceEvent n m polymer) *
          anchorCanonicalPartition n -
        anchorEventNumerator n (sourceOccurrenceEvent polymer) *
          boundaryAnchorPartition n m := by
  have hcore := normalizedEventCrossDifference_eqv_boundary
    hnm (targetOccurrenceEvent n m polymer)
  have hpartition := anchorCanonicalPartition_eqv_embedded hnm
  have hevent := anchorOccurrenceNumerator_eqv_embedded hnm hpolymer
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_trans _ _ _ hcore ?_)
  · exact sub_eqv_both
      (mul_eqv_both (Q'.eqv_refl _) hpartition)
      (mul_eqv_both hevent (Q'.eqv_refl _))
  · exact sub_eqv_both
      (mul_eqv_both (Q'.eqv_refl _)
        (Q'.eqv_symm hpartition))
      (mul_eqv_both (Q'.eqv_symm hevent) (Q'.eqv_refl _))

end YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence.familyContainsPolymerB_embedded_transport
#print axioms YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence.embeddedSourceOccurrenceFamilies_perm_target
#print axioms YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence.anchorOccurrenceNumerator_eqv_embedded
#print axioms YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence.anchorOccurrenceCrossDifference_eqv_boundary
