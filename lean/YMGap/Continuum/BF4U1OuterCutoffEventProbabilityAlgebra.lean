/-
# Boolean-event algebra for the canonical BF4 U(1) outer-cutoff law

The outer-cutoff tail modules construct a normalized rational probability for
every Boolean event on the finite canonical U(1) slab.  This file records the
finite-stage probability algebra needed by the constructive-real limit:

* every event probability lies in `[0,1]`;
* an event and its Boolean complement have numerators summing to the
  partition;
* consequently their normalized probabilities sum to one.

All statements are exact at every charge cutoff.  They use finite lists and
`Q'` arithmetic only.  No continuum, spacing, or infinite-volume limit is
asserted here.
-/

import YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail

namespace YMGap.Continuum.BF4U1OuterCutoffEventProbabilityAlgebra

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4U1OuterCutoffNesting
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Masked sums and complements -/

private theorem listQSum_mask_eq_filter_local
    {A : Type} (weight : A → Q') (event : A → Bool) :
    ∀ source : List A,
      listQSum
          (fun item =>
            if event item then weight item else 0)
          source ≈
        listQSum weight (source.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head
      · simp only [listQSum, hevent, Bool.false_eq_true,
          ↓reduceIte, List.filter_cons]
        exact Q'.eqv_trans _
          (0 + listQSum weight (tail.filter event)) _
          (Q'.add_eqv_congr_left 0 _
            (listQSum weight (tail.filter event))
            (listQSum_mask_eq_filter_local
              weight event tail))
          (QPoly.q_zero_add_eqv
            (listQSum weight (tail.filter event)))
      · simp only [listQSum, hevent, ↓reduceIte,
          List.filter_cons]
        exact Q'.add_eqv_congr_left
          (weight head)
          (listQSum
            (fun item =>
              if event item then weight item else 0)
            tail)
          (listQSum weight (tail.filter event))
          (listQSum_mask_eq_filter_local
            weight event tail)

/-- The event numerator and its Boolean complement partition the complete
finite U(1) slab mass exactly. -/
theorem canonicalU1SlabEventNumerator_add_complement_eqv_partition
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (event : ChargeLabelling → Bool) :
    canonicalU1SlabEventNumerator
          w hw half K event +
        canonicalU1SlabEventNumerator
          w hw half K (fun state => !(event state)) ≈
      (canonicalU1Slab w hw half K).partition := by
  unfold canonicalU1SlabEventNumerator
    U1SlabData.partition
  let D := canonicalU1Slab w hw half K
  have hevent :=
    listQSum_mask_eq_filter_local
      D.physicalTerm event D.states
  have hcomplement :=
    listQSum_mask_eq_filter_local
      D.physicalTerm
      (fun state => !(event state)) D.states
  have hpartition :=
    listQSum_filter_partition
      D.physicalTerm event D.states
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hevent hcomplement)
    (Q'.eqv_symm hpartition)

/-! ## 2. Interval bounds -/

/-- Every canonical normalized Boolean-event probability is nonnegative. -/
theorem canonicalU1SlabEventProbability_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (event : ChargeLabelling → Bool) :
    (0 : Q') ≤
      canonicalU1SlabEventProbability
        w hw half K event := by
  unfold canonicalU1SlabEventProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (canonicalU1SlabEventNumerator_nonnegative
      w hw half K event)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (canonicalU1Slab w hw half K).partition_pos))

/-- Every canonical normalized Boolean-event probability is at most one. -/
theorem canonicalU1SlabEventProbability_le_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (event : ChargeLabelling → Bool) :
    canonicalU1SlabEventProbability
        w hw half K event ≤ (1 : Q') := by
  unfold canonicalU1SlabEventProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (canonicalU1SlabEventNumerator_le_partition
      w hw half K event)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (canonicalU1Slab w hw half K).partition))

/-! ## 3. Event monotonicity -/

private theorem listQSum_event_mono_local
    {A : Type} (weight : A → Q')
    (hweight : ∀ item, (0 : Q') ≤ weight item)
    (first second : A → Bool)
    (himp : ∀ item, first item = true → second item = true) :
    ∀ source : List A,
      listQSum
          (fun item =>
            if first item then weight item else 0)
          source ≤
        listQSum
          (fun item =>
            if second item then weight item else 0)
          source
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have htail :=
        listQSum_event_mono_local
          weight hweight first second himp tail
      cases hfirst : first head
      · cases hsecond : second head
        · simp only [listQSum, hfirst, hsecond,
            Bool.false_eq_true, ↓reduceIte]
          exact Q'.add_le_add
            (Q'.le_refl' 0) htail
        · simp only [listQSum, hfirst, hsecond,
            Bool.false_eq_true, ↓reduceIte]
          exact Q'.add_le_add (hweight head) htail
      · have hsecond : second head = true :=
          himp head hfirst
        simp only [listQSum, hfirst, hsecond,
          ↓reduceIte]
        exact Q'.add_le_add
          (Q'.le_refl' (weight head)) htail

/-- Boolean-event inclusion is monotone under the canonical finite
probability law. -/
theorem canonicalU1SlabEventProbability_mono
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (first second : ChargeLabelling → Bool)
    (himp :
      ∀ state, first state = true → second state = true) :
    canonicalU1SlabEventProbability
        w hw half K first ≤
      canonicalU1SlabEventProbability
        w hw half K second := by
  unfold canonicalU1SlabEventProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (by
      unfold canonicalU1SlabEventNumerator
      exact listQSum_event_mono_local
        (canonicalU1Slab w hw half K).physicalTerm
        (canonicalU1Slab w hw half K).physicalTerm_nonnegative
        first second himp
        (canonicalU1Slab w hw half K).states)
    (Q'.ge_of_eqv
      (Q'.divPos_mul_eqv
        (canonicalU1SlabEventNumerator
          w hw half K second)
        (canonicalU1Slab w hw half K).partition
        (canonicalU1Slab w hw half K).partition_pos))

/-! ## 4. Exact normalized complementarity -/

private theorem add_divPos_eqv_local
    (p q d : Q') (hd : (0 : Q') < d) :
    Q'.divPos p d hd + Q'.divPos q d hd ≈
      Q'.divPos (p + q) d hd :=
  Q'.eqv_symm
    (Q'.add_mul_eqv p q (Q'.recipPos d hd))

/-- At every finite outer cutoff, an event and its Boolean complement have
normalized probabilities summing exactly to one. -/
theorem canonicalU1SlabEventProbability_add_complement_eqv_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (event : ChargeLabelling → Bool) :
    canonicalU1SlabEventProbability
          w hw half K event +
        canonicalU1SlabEventProbability
          w hw half K (fun state => !(event state)) ≈
      (1 : Q') := by
  have hsplit :=
    canonicalU1SlabEventNumerator_add_complement_eqv_partition
      w hw half K event
  unfold canonicalU1SlabEventProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (canonicalU1SlabEventNumerator
        w hw half K event)
      (canonicalU1SlabEventNumerator
        w hw half K (fun state => !(event state)))
      (canonicalU1Slab w hw half K).partition
      (canonicalU1Slab w hw half K).partition_pos) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos
        (canonicalU1Slab w hw half K).partition
        (canonicalU1Slab w hw half K).partition_pos)
      hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (canonicalU1Slab w hw half K).partition
    (canonicalU1Slab w hw half K).partition_pos

#print axioms canonicalU1SlabEventNumerator_add_complement_eqv_partition
#print axioms canonicalU1SlabEventProbability_nonnegative
#print axioms canonicalU1SlabEventProbability_le_one
#print axioms canonicalU1SlabEventProbability_mono
#print axioms canonicalU1SlabEventProbability_add_complement_eqv_one

end YMGap.Continuum.BF4U1OuterCutoffEventProbabilityAlgebra
