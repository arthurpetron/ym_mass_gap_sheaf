/-
# Four-cell form of the canonical boundary covariance

The embedded/boundary split and an arbitrary Boolean event give four positive
cells.  The normalized cross difference loses its common event/event product
and is exactly

  boundary-event * embedded-complement
    - embedded-event * boundary-complement.

This is the finite two-replica switching target: configurations not connected
from the event to the boundary should pair between these two products.  The
identity is exact and subtraction-free in its companion form; no switching
bound is assumed here.
-/

import YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence

namespace YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## 1. The two complementary cells -/

def embeddedTargetEventComplementNumerator (n m : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
    ((embeddedTargetFamilies n m).filter
      (fun family => !(event family)))

def boundaryTargetEventComplementNumerator (n m : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
    ((boundaryTargetFamilies n m).filter
      (fun family => !(event family)))

private theorem listQSum_filter_partition {A : Type}
    (weight : A → Q') (test : A → Bool) :
    ∀ xs : List A,
      listQSum weight xs ≈
        listQSum weight (xs.filter test) +
          listQSum weight (xs.filter (fun item => !(test item)))
  | [] => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | head :: tail => by
      have ih := listQSum_filter_partition weight test tail
      cases hhead : test head with
      | false =>
          simp only [listQSum, List.filter_cons, hhead,
            Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (weight head) _ _ ih) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.add_comm_eqv (weight head)
                (listQSum weight (tail.filter test)))) ?_
          exact Q'.add_assoc_eqv _ _ _
      | true =>
          simp only [listQSum, List.filter_cons, hhead, ↓reduceIte,
            Bool.not_true, Bool.false_eq_true]
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (weight head) _ _ ih) ?_
          exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem filters_commute {A : Type}
    (first second : A → Bool) (xs : List A) :
    (xs.filter first).filter second =
      (xs.filter second).filter first := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (second item) (first item)

theorem embeddedTargetEventNumerator_eqv_filter
    (n m : Nat) (event : List (List Nat) → Bool) :
    embeddedTargetEventNumerator n m event ≈
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
        ((embeddedTargetFamilies n m).filter event) := by
  unfold embeddedTargetEventNumerator embeddedTargetFamilies
    embeddedFamilyB
  rw [filters_commute]
  exact Q'.eqv_refl _

theorem boundaryTargetEventNumerator_eqv_filter
    (n m : Nat) (event : List (List Nat) → Bool) :
    boundaryTargetEventNumerator n m event ≈
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
        ((boundaryTargetFamilies n m).filter event) := by
  unfold boundaryTargetEventNumerator boundaryTargetFamilies
    embeddedFamilyB
  rw [filters_commute]
  exact Q'.eqv_refl _

theorem embeddedAnchorPartition_eqv_event_add_complement
    {n m : Nat} (hnm : n ≤ m)
    (event : List (List Nat) → Bool) :
    embeddedAnchorPartition n m ≈
      embeddedTargetEventNumerator n m event +
        embeddedTargetEventComplementNumerator n m event := by
  have hperm := listQSum_perm
    (canonicalSurfaceFamilyActivity anchorCoupling m)
    (embeddedCompatibleFamilies_perm_target hnm)
  have hsplit := listQSum_filter_partition
    (canonicalSurfaceFamilyActivity anchorCoupling m) event
    (embeddedTargetFamilies n m)
  refine Q'.eqv_trans _ _ _ hperm (Q'.eqv_trans _ _ _ hsplit ?_)
  exact Q'.add_eqv_congr'
    (Q'.eqv_symm
      (embeddedTargetEventNumerator_eqv_filter n m event))
    (Q'.eqv_refl _)

theorem boundaryAnchorPartition_eqv_event_add_complement
    (n m : Nat) (event : List (List Nat) → Bool) :
    boundaryAnchorPartition n m ≈
      boundaryTargetEventNumerator n m event +
        boundaryTargetEventComplementNumerator n m event := by
  unfold boundaryAnchorPartition
  have hsplit := listQSum_filter_partition
    (canonicalSurfaceFamilyActivity anchorCoupling m) event
    (boundaryTargetFamilies n m)
  refine Q'.eqv_trans _ _ _ hsplit ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_symm
      (boundaryTargetEventNumerator_eqv_filter n m event))
    (Q'.eqv_refl _)

/-! ## 2. Exact cell cancellation -/

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

/-- Pure four-cell cancellation. -/
theorem eventBoundaryCrossDifference_cells
    (eventEmbedded eventBoundary embeddedComplement boundaryComplement : Q') :
    eventBoundary * (eventEmbedded + embeddedComplement) -
        eventEmbedded * (eventBoundary + boundaryComplement) ≈
      eventBoundary * embeddedComplement -
        eventEmbedded * boundaryComplement := by
  refine Q'.eqv_trans _
    ((eventEmbedded + embeddedComplement) * eventBoundary -
      eventEmbedded * (eventBoundary + boundaryComplement)) _ ?_ ?_
  · exact sub_eqv_both
      (Q'.mul_comm_eqv eventBoundary
        (eventEmbedded + embeddedComplement))
      (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (embeddedComplement * eventBoundary -
      eventEmbedded * boundaryComplement) _
    (crossDifference_split eventEmbedded embeddedComplement
      eventBoundary boundaryComplement) ?_
  exact sub_eqv_both
    (Q'.mul_comm_eqv embeddedComplement eventBoundary)
    (Q'.eqv_refl _)

/-- Subtraction-free four-cell polynomial identity. -/
theorem eventBoundarySwitching_cells
    (eventEmbedded eventBoundary embeddedComplement boundaryComplement : Q') :
    eventBoundary * (eventEmbedded + embeddedComplement) +
        eventEmbedded * boundaryComplement ≈
      eventEmbedded * (eventBoundary + boundaryComplement) +
        eventBoundary * embeddedComplement := by
  ring_qeqv

/-- The canonical embedded/boundary determinant in its exact opposite-cell
form. -/
theorem boundaryCrossDifference_eqv_eventComplementCells
    {n m : Nat} (hnm : n ≤ m)
    (event : List (List Nat) → Bool) :
    boundaryTargetEventNumerator n m event *
          embeddedAnchorPartition n m -
        embeddedTargetEventNumerator n m event *
          boundaryAnchorPartition n m ≈
      boundaryTargetEventNumerator n m event *
          embeddedTargetEventComplementNumerator n m event -
        embeddedTargetEventNumerator n m event *
          boundaryTargetEventComplementNumerator n m event := by
  have hembedded :=
    embeddedAnchorPartition_eqv_event_add_complement hnm event
  have hboundary :=
    boundaryAnchorPartition_eqv_event_add_complement n m event
  refine Q'.eqv_trans _ _ _
    (sub_eqv_both
      (mul_eqv_both (Q'.eqv_refl _) hembedded)
      (mul_eqv_both (Q'.eqv_refl _) hboundary)) ?_
  exact eventBoundaryCrossDifference_cells
    (embeddedTargetEventNumerator n m event)
    (boundaryTargetEventNumerator n m event)
    (embeddedTargetEventComplementNumerator n m event)
    (boundaryTargetEventComplementNumerator n m event)

/-- Subtraction-free companion form, suitable for a weight-preserving
component-switching injection. -/
theorem boundaryCrossDifference_switching_identity
    {n m : Nat} (hnm : n ≤ m)
    (event : List (List Nat) → Bool) :
    boundaryTargetEventNumerator n m event *
          embeddedAnchorPartition n m +
        embeddedTargetEventNumerator n m event *
          boundaryTargetEventComplementNumerator n m event ≈
      embeddedTargetEventNumerator n m event *
          boundaryAnchorPartition n m +
        boundaryTargetEventNumerator n m event *
          embeddedTargetEventComplementNumerator n m event := by
  have hembedded :=
    embeddedAnchorPartition_eqv_event_add_complement hnm event
  have hboundary :=
    boundaryAnchorPartition_eqv_event_add_complement n m event
  refine Q'.eqv_trans _
    (boundaryTargetEventNumerator n m event *
          (embeddedTargetEventNumerator n m event +
            embeddedTargetEventComplementNumerator n m event) +
      embeddedTargetEventNumerator n m event *
        boundaryTargetEventComplementNumerator n m event) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (mul_eqv_both (Q'.eqv_refl _) hembedded)
      (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (embeddedTargetEventNumerator n m event *
          (boundaryTargetEventNumerator n m event +
            boundaryTargetEventComplementNumerator n m event) +
      boundaryTargetEventNumerator n m event *
        embeddedTargetEventComplementNumerator n m event) _ ?_ ?_
  · exact eventBoundarySwitching_cells
      (embeddedTargetEventNumerator n m event)
      (boundaryTargetEventNumerator n m event)
      (embeddedTargetEventComplementNumerator n m event)
      (boundaryTargetEventComplementNumerator n m event)
  · exact Q'.add_eqv_congr'
      (mul_eqv_both (Q'.eqv_refl _) (Q'.eqv_symm hboundary))
      (Q'.eqv_refl _)

/-! ## 3. Concrete local-occurrence specialization -/

/-- The exact larger-minus-smaller occurrence-probability numerator is the
opposite-cell determinant to which disagreement-component switching applies. -/
theorem anchorOccurrenceCrossDifference_eqv_eventComplementCells
    {n m : Nat} (hnm : n ≤ m) {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    anchorEventNumerator m (targetOccurrenceEvent n m polymer) *
          anchorCanonicalPartition n -
        anchorEventNumerator n (sourceOccurrenceEvent polymer) *
          anchorCanonicalPartition m ≈
      boundaryTargetEventNumerator n m
            (targetOccurrenceEvent n m polymer) *
          embeddedTargetEventComplementNumerator n m
            (targetOccurrenceEvent n m polymer) -
        embeddedTargetEventNumerator n m
            (targetOccurrenceEvent n m polymer) *
          boundaryTargetEventComplementNumerator n m
            (targetOccurrenceEvent n m polymer) := by
  have hpartition := anchorCanonicalPartition_eqv_embedded hnm
  have hevent := anchorOccurrenceNumerator_eqv_embedded hnm hpolymer
  refine Q'.eqv_trans _
    (anchorEventNumerator m (targetOccurrenceEvent n m polymer) *
          embeddedAnchorPartition n m -
      embeddedTargetEventNumerator n m
          (targetOccurrenceEvent n m polymer) *
        anchorCanonicalPartition m) _ ?_ ?_
  · exact sub_eqv_both
      (mul_eqv_both (Q'.eqv_refl _) hpartition)
      (mul_eqv_both hevent (Q'.eqv_refl _))
  refine Q'.eqv_trans _
    (boundaryTargetEventNumerator n m
          (targetOccurrenceEvent n m polymer) *
        embeddedAnchorPartition n m -
      embeddedTargetEventNumerator n m
          (targetOccurrenceEvent n m polymer) *
        boundaryAnchorPartition n m) _ ?_ ?_
  · exact normalizedEventCrossDifference_eqv_boundary hnm
      (targetOccurrenceEvent n m polymer)
  · exact boundaryCrossDifference_eqv_eventComplementCells hnm
      (targetOccurrenceEvent n m polymer)

end YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance.embeddedAnchorPartition_eqv_event_add_complement
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance.boundaryAnchorPartition_eqv_event_add_complement
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance.eventBoundaryCrossDifference_cells
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance.eventBoundarySwitching_cells
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance.boundaryCrossDifference_eqv_eventComplementCells
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance.boundaryCrossDifference_switching_identity
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance.anchorOccurrenceCrossDifference_eqv_eventComplementCells
