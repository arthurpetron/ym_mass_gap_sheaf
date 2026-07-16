/-
# Exact transport and constructive pivots for finite local cylinder events

A finite local cylinder event is an arbitrary Boolean function of the
occurrence bits of a finite list of canonical polymers.  This module proves
that its embedded numerator transports exactly between boxes and reduces its
cross-volume numerator to the same four boundary cells as a singleton event.

It also applies the finite Boolean pivot construction to two occurrence
fingerprints.  When the cylinder event differs between the replicas, the
selected coordinate is a concrete marked polymer whose occurrence-bit swap
changes the event.  Turning that pivot into a globally injective component
switch is the next layer.
-/

import YMGap.Continuum.FiniteBooleanEventPivot
import YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance

namespace YMGap.Continuum.Z4CanonicalCylinderEventTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteBooleanEventPivot
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite occurrence fingerprints -/

/-- Occurrence bits of the marked polymers in their given order. -/
def familyOccurrenceFingerprint (roots : List (List Nat))
    (family : List (List Nat)) : List Bool :=
  roots.map (fun root => familyContainsPolymerB root family)

@[simp] theorem familyOccurrenceFingerprint_length
    (roots family : List (List Nat)) :
    (familyOccurrenceFingerprint roots family).length = roots.length := by
  simp only [familyOccurrenceFingerprint, List.length_map]

def transportedCylinderRoots (n m : Nat)
    (roots : List (List Nat)) : List (List Nat) :=
  roots.map (transportPolymer n m)

/-- Every coordinate of a finite occurrence fingerprint is invariant under
canonical family transport. -/
theorem familyOccurrenceFingerprint_embedded_transport
    {n m : Nat} (hnm : n ≤ m) :
    ∀ {roots : List (List Nat)},
      (∀ root, root ∈ roots → root ∈ canonicalSurfacePolymers n) →
      ∀ {family : List (List Nat)},
        family ∈ canonicalCompatibleAmbientFamilies n →
        familyOccurrenceFingerprint roots family =
          familyOccurrenceFingerprint (transportedCylinderRoots n m roots)
            (embeddedTransportFamily n m family)
  | [], _, family, hfamily => by
      rfl
  | root :: roots, hroots, family, hfamily => by
      have hroot : root ∈ canonicalSurfacePolymers n :=
        hroots root List.mem_cons_self
      have htail : ∀ tailRoot, tailRoot ∈ roots →
          tailRoot ∈ canonicalSurfacePolymers n :=
        fun tailRoot htailRoot =>
          hroots tailRoot (List.mem_cons_of_mem root htailRoot)
      simp only [familyOccurrenceFingerprint, transportedCylinderRoots,
        List.map_cons]
      rw [familyContainsPolymerB_embedded_transport hnm hroot hfamily]
      exact congrArg
        (List.cons
          (familyContainsPolymerB (transportPolymer n m root)
            (embeddedTransportFamily n m family)))
        (familyOccurrenceFingerprint_embedded_transport hnm htail hfamily)

/-- Arbitrary Boolean function of a finite occurrence fingerprint. -/
def cylinderEvent (roots : List (List Nat))
    (predicate : List Bool → Bool) (family : List (List Nat)) : Bool :=
  predicate (familyOccurrenceFingerprint roots family)

def sourceCylinderEvent (roots : List (List Nat))
    (predicate : List Bool → Bool) : List (List Nat) → Bool :=
  cylinderEvent roots predicate

def targetCylinderEvent (n m : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) : List (List Nat) → Bool :=
  cylinderEvent (transportedCylinderRoots n m roots) predicate

theorem cylinderEvent_embedded_transport
    {n m : Nat} (hnm : n ≤ m) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers n)
    (predicate : List Bool → Bool) {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    sourceCylinderEvent roots predicate family =
      targetCylinderEvent n m roots predicate
        (embeddedTransportFamily n m family) := by
  unfold sourceCylinderEvent targetCylinderEvent cylinderEvent
  rw [familyOccurrenceFingerprint_embedded_transport hnm hroots hfamily]

/-! ## 2. Exact embedded event transport -/

def embeddedSourceCylinderFamilies (n m : Nat)
    (roots : List (List Nat)) (predicate : List Bool → Bool) :
    List (List (List Nat)) :=
  ((canonicalCompatibleAmbientFamilies n).filter
      (sourceCylinderEvent roots predicate)).map
    (embeddedTransportFamily n m)

def embeddedTargetCylinderFamilies (n m : Nat)
    (roots : List (List Nat)) (predicate : List Bool → Bool) :
    List (List (List Nat)) :=
  ((canonicalCompatibleAmbientFamilies m).filter
      (targetCylinderEvent n m roots predicate)).filter
    (embeddedFamilyB n m)

theorem embeddedSourceCylinderFamilies_eq_filter
    {n m : Nat} (hnm : n ≤ m) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers n)
    (predicate : List Bool → Bool) :
    embeddedSourceCylinderFamilies n m roots predicate =
      (embeddedCompatibleFamilies n m).filter
        (targetCylinderEvent n m roots predicate) := by
  unfold embeddedSourceCylinderFamilies embeddedCompatibleFamilies
  rw [List.filter_map]
  apply congrArg (List.map (embeddedTransportFamily n m))
  apply List.filter_congr
  intro family hfamily
  exact cylinderEvent_embedded_transport hnm hroots predicate hfamily

theorem embeddedTargetCylinderFamilies_eq_filter
    (n m : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) :
    embeddedTargetCylinderFamilies n m roots predicate =
      (embeddedTargetFamilies n m).filter
        (targetCylinderEvent n m roots predicate) := by
  unfold embeddedTargetCylinderFamilies embeddedTargetFamilies embeddedFamilyB
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro family _
  cases decide (family ∈ embeddedCompatibleFamilies n m) <;>
    cases targetCylinderEvent n m roots predicate family <;> rfl

theorem embeddedSourceCylinderFamilies_perm_target
    {n m : Nat} (hnm : n ≤ m) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers n)
    (predicate : List Bool → Bool) :
    (embeddedSourceCylinderFamilies n m roots predicate).Perm
      (embeddedTargetCylinderFamilies n m roots predicate) := by
  rw [embeddedSourceCylinderFamilies_eq_filter hnm hroots predicate,
    embeddedTargetCylinderFamilies_eq_filter]
  exact (embeddedCompatibleFamilies_perm_target hnm).filter _

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

/-- The smaller-box numerator of any finite cylinder event is exactly its
embedded larger-box numerator. -/
theorem anchorCylinderNumerator_eqv_embedded
    {n m : Nat} (hnm : n ≤ m) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers n)
    (predicate : List Bool → Bool) :
    anchorEventNumerator n (sourceCylinderEvent roots predicate) ≈
      embeddedTargetEventNumerator n m
        (targetCylinderEvent n m roots predicate) := by
  have hmap :
      anchorEventNumerator n (sourceCylinderEvent roots predicate) ≈
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
          (embeddedSourceCylinderFamilies n m roots predicate) := by
    unfold anchorEventNumerator embeddedSourceCylinderFamilies
    apply listQSum_map_eqv_local
    intro family hfamily
    have hcompatible := (List.mem_filter.mp hfamily).1
    exact compatibleFamilyActivity_embedded_transport
      anchorCoupling hnm hcompatible
  have hperm := listQSum_perm
    (canonicalSurfaceFamilyActivity anchorCoupling m)
    (embeddedSourceCylinderFamilies_perm_target hnm hroots predicate)
  refine Q'.eqv_trans _ _ _ hmap ?_
  change listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
      (embeddedSourceCylinderFamilies n m roots predicate) ≈
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
      (embeddedTargetCylinderFamilies n m roots predicate)
  exact hperm

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

/-- Exact four-cell boundary determinant for an arbitrary finite local
cylinder event. -/
theorem anchorCylinderCrossDifference_eqv_eventComplementCells
    {n m : Nat} (hnm : n ≤ m) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers n)
    (predicate : List Bool → Bool) :
    anchorEventNumerator m (targetCylinderEvent n m roots predicate) *
          anchorCanonicalPartition n -
        anchorEventNumerator n (sourceCylinderEvent roots predicate) *
          anchorCanonicalPartition m ≈
      boundaryTargetEventNumerator n m
            (targetCylinderEvent n m roots predicate) *
          embeddedTargetEventComplementNumerator n m
            (targetCylinderEvent n m roots predicate) -
        embeddedTargetEventNumerator n m
            (targetCylinderEvent n m roots predicate) *
          boundaryTargetEventComplementNumerator n m
            (targetCylinderEvent n m roots predicate) := by
  have hpartition := anchorCanonicalPartition_eqv_embedded hnm
  have hevent := anchorCylinderNumerator_eqv_embedded
    hnm hroots predicate
  refine Q'.eqv_trans _
    (anchorEventNumerator m (targetCylinderEvent n m roots predicate) *
          embeddedAnchorPartition n m -
      embeddedTargetEventNumerator n m
          (targetCylinderEvent n m roots predicate) *
        anchorCanonicalPartition m) _ ?_ ?_
  · exact sub_eqv_both
      (mul_eqv_both (Q'.eqv_refl _) hpartition)
      (mul_eqv_both hevent (Q'.eqv_refl _))
  refine Q'.eqv_trans _
    (boundaryTargetEventNumerator n m
          (targetCylinderEvent n m roots predicate) *
        embeddedAnchorPartition n m -
      embeddedTargetEventNumerator n m
          (targetCylinderEvent n m roots predicate) *
        boundaryAnchorPartition n m) _ ?_ ?_
  · exact normalizedEventCrossDifference_eqv_boundary hnm
      (targetCylinderEvent n m roots predicate)
  · exact boundaryCrossDifference_eqv_eventComplementCells hnm
      (targetCylinderEvent n m roots predicate)

/-! ## 3. Constructive marked-root pivot -/

def cylinderEventBlendState (roots : List (List Nat))
    (predicate : List Bool → Bool)
    (left right : List (List Nat)) (index : Nat) : Bool :=
  coordinateEventState predicate
    (familyOccurrenceFingerprint roots left)
    (familyOccurrenceFingerprint roots right) index

/-- If a cylinder event is true on `left` and false on `right`, retain a
concrete coordinate whose one-step occurrence-bit replacement changes it. -/
def cylinderEventPivot (roots : List (List Nat))
    (predicate : List Bool → Bool)
    (left right : List (List Nat))
    (hleft : cylinderEvent roots predicate left = true)
    (hright : cylinderEvent roots predicate right = false) :
    TrueToFalseTransition
      (cylinderEventBlendState roots predicate left right) roots.length := by
  have hlength :
      (familyOccurrenceFingerprint roots left).length =
        (familyOccurrenceFingerprint roots right).length := by
    simp only [familyOccurrenceFingerprint_length]
  have hpivot := coordinateEventPivot predicate
    (familyOccurrenceFingerprint roots left)
    (familyOccurrenceFingerprint roots right)
    hlength hleft hright
  simpa only [cylinderEventBlendState,
    familyOccurrenceFingerprint_length] using hpivot

def cylinderEventPivotRoot (roots : List (List Nat))
    (predicate : List Bool → Bool)
    (left right : List (List Nat))
    (hleft : cylinderEvent roots predicate left = true)
    (hright : cylinderEvent roots predicate right = false) : List Nat :=
  roots.get ⟨(cylinderEventPivot roots predicate left right hleft hright).index,
    (cylinderEventPivot roots predicate left right hleft hright).index_lt⟩

theorem cylinderEventPivotRoot_mem (roots : List (List Nat))
    (predicate : List Bool → Bool)
    (left right : List (List Nat))
    (hleft : cylinderEvent roots predicate left = true)
    (hright : cylinderEvent roots predicate right = false) :
    cylinderEventPivotRoot roots predicate left right hleft hright ∈ roots := by
  unfold cylinderEventPivotRoot
  exact List.get_mem roots _

theorem cylinderEventPivot_spec (roots : List (List Nat))
    (predicate : List Bool → Bool)
    (left right : List (List Nat))
    (hleft : cylinderEvent roots predicate left = true)
    (hright : cylinderEvent roots predicate right = false) :
    let pivot := cylinderEventPivot roots predicate left right hleft hright
    predicate (coordinateBlend
        (familyOccurrenceFingerprint roots left)
        (familyOccurrenceFingerprint roots right) pivot.index) = true ∧
      predicate (coordinateBlend
        (familyOccurrenceFingerprint roots left)
        (familyOccurrenceFingerprint roots right) (pivot.index + 1)) = false := by
  intro pivot
  exact ⟨pivot.before_true, pivot.after_false⟩

end YMGap.Continuum.Z4CanonicalCylinderEventTransport

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalCylinderEventTransport.familyOccurrenceFingerprint_embedded_transport
#print axioms YMGap.Continuum.Z4CanonicalCylinderEventTransport.anchorCylinderNumerator_eqv_embedded
#print axioms YMGap.Continuum.Z4CanonicalCylinderEventTransport.anchorCylinderCrossDifference_eqv_eventComplementCells
#print axioms YMGap.Continuum.Z4CanonicalCylinderEventTransport.cylinderEventPivot
#print axioms YMGap.Continuum.Z4CanonicalCylinderEventTransport.cylinderEventPivotRoot_mem
