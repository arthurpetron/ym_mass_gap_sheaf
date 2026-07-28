/-
# Probability algebra for the fixed-anchor physical SU(2) cutoff limit

This module proves the finite Boolean-event algebra for the exact normalized
fixed-anchor physical SU(2) cutoff law and transports it pointwise to the
Bishop-real limit:

* event inclusion is monotone;
* an event and its Boolean complement sum exactly to one;
* every limiting probability lies in the constructive unit interval; and
* inclusion and complement normalization survive the cutoff limit.

All proofs use finite lists, exact `Q'` arithmetic, and the transitive
eventual order `CReal.leEv`.  The result is fixed-anchor and fixed-volume; it
does not assert a spacing or infinite-volume limit.

## Axiom gate

No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, choice,
functional extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.SU2PhysicalOuterCutoffAnchorCRealLimit
import YMGap.Constructive.CRealComplete
import YMGap.Constructive.SumOfSquares

namespace
  YMGap.Continuum.SU2PhysicalOuterCutoffAnchorCRealProbabilityAlgebra

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffAnchorCRealLimit
open YMGap.Continuum.SU2PhysicalOuterCutoffNormalizedEventTail
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite-stage event algebra -/

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

/-- At every finite cutoff, the event numerator and Boolean-complement
numerator partition the complete physical SU(2) mass exactly. -/
theorem anchorPhysicalCutoffEventNumerator_add_complement_eqv_partition
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) :
    parametricKEventNumerator anchorCoupling
          cutoff volume event +
        parametricKEventNumerator anchorCoupling
          cutoff volume (fun state => !(event state)) ≈
      parametricKPhysicalPartition anchorCoupling
        cutoff volume := by
  unfold parametricKEventNumerator parametricKEventTerm
    parametricKPhysicalPartition
  let states :=
    boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount volume))
  let weight :=
    parametricKPhysicalTerm anchorCoupling cutoff volume
  have hevent :=
    listQSum_mask_eq_filter_local weight event states
  have hcomplement :=
    listQSum_mask_eq_filter_local weight
      (fun state => !(event state)) states
  have hpartition :=
    listQSum_filter_partition weight event states
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hevent hcomplement)
    (Q'.eqv_symm hpartition)

private theorem listQSum_event_mono_local
    {A : Type} (weight : A → Q')
    (hweight : ∀ item, (0 : Q') ≤ weight item)
    (first second : A → Bool)
    (himp :
      ∀ item, first item = true → second item = true) :
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

/-- Boolean-event inclusion is monotone for every exact finite-cutoff
normalized physical SU(2) probability. -/
theorem anchorPhysicalCutoffEventProbability_mono
    (cutoff volume : Nat)
    (first second : EdgeLabelling → Bool)
    (himp :
      ∀ state, first state = true → second state = true) :
    anchorPhysicalCutoffEventProbability
        cutoff volume first ≤
      anchorPhysicalCutoffEventProbability
        cutoff volume second := by
  have hnumerator :
      parametricKEventNumerator anchorCoupling
          cutoff volume first ≤
        parametricKEventNumerator anchorCoupling
          cutoff volume second := by
    unfold parametricKEventNumerator parametricKEventTerm
    exact listQSum_event_mono_local
      (parametricKPhysicalTerm
        anchorCoupling cutoff volume)
      (parametricKPhysicalTerm_nonnegative
        (w := anchorCoupling) (by decide)
        cutoff volume)
      first second himp
      (boundedEdgeLabellings cutoff
        (List.range (plaquetteEdgeCount volume)))
  unfold anchorPhysicalCutoffEventProbability Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right
    _ _ _
    hnumerator
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (couplingKPhysicalPartition_pos
          (coupling := anchorCoupling)
          (by decide) cutoff volume)))

private theorem add_divPos_eqv_local
    (p q d : Q') (hd : (0 : Q') < d) :
    Q'.divPos p d hd + Q'.divPos q d hd ≈
      Q'.divPos (p + q) d hd :=
  Q'.eqv_symm
    (Q'.add_mul_eqv p q (Q'.recipPos d hd))

/-- At every finite cutoff, a normalized event and its Boolean complement
sum exactly to one. -/
theorem anchorPhysicalCutoffEventProbability_add_complement_eqv_one
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) :
    anchorPhysicalCutoffEventProbability
          cutoff volume event +
        anchorPhysicalCutoffEventProbability
          cutoff volume (fun state => !(event state)) ≈
      (1 : Q') := by
  have hsplit :=
    anchorPhysicalCutoffEventNumerator_add_complement_eqv_partition
      cutoff volume event
  unfold anchorPhysicalCutoffEventProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (parametricKEventNumerator anchorCoupling
        cutoff volume event)
      (parametricKEventNumerator anchorCoupling
        cutoff volume (fun state => !(event state)))
      (parametricKPhysicalPartition anchorCoupling
        cutoff volume)
      (couplingKPhysicalPartition_pos
        (coupling := anchorCoupling)
        (by decide) cutoff volume)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos
        (parametricKPhysicalPartition anchorCoupling
          cutoff volume)
        (couplingKPhysicalPartition_pos
          (coupling := anchorCoupling)
          (by decide) cutoff volume))
      hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (parametricKPhysicalPartition anchorCoupling
      cutoff volume)
    (couplingKPhysicalPartition_pos
      (coupling := anchorCoupling)
      (by decide) cutoff volume)

/-! ## 2. Constructive unit interval and event monotonicity -/

/-- Every fixed-volume SU(2) event limit is nonnegative in the transitive
constructive-real order. -/
theorem anchorPhysicalCutoffEventProbabilityLimit_nonnegative
    (volume : Nat) (event : EdgeLabelling → Bool) :
    CReal.leEv CReal.czero
      (anchorPhysicalCutoffEventProbabilityLimit
        volume event) := by
  apply CReal.leEv_ofQ'_of_approx_ge
  intro cutoff
  exact anchorPhysicalCutoffEventProbability_nonnegative
    cutoff volume event

/-- Every fixed-volume SU(2) event limit is at most one in the transitive
constructive-real order. -/
theorem anchorPhysicalCutoffEventProbabilityLimit_le_one
    (volume : Nat) (event : EdgeLabelling → Bool) :
    CReal.leEv
      (anchorPhysicalCutoffEventProbabilityLimit
        volume event)
      CReal.cone := by
  apply CReal.leEv_le_ofQ'_of_approx_le
  intro cutoff
  exact anchorPhysicalCutoffEventProbability_le_one
    cutoff volume event

/-- Unit-interval package for the fixed-volume limiting event law. -/
theorem anchorPhysicalCutoffEventProbabilityLimit_mem_unitInterval
    (volume : Nat) (event : EdgeLabelling → Bool) :
    CReal.leEv CReal.czero
        (anchorPhysicalCutoffEventProbabilityLimit
          volume event) ∧
      CReal.leEv
        (anchorPhysicalCutoffEventProbabilityLimit
          volume event)
        CReal.cone :=
  ⟨anchorPhysicalCutoffEventProbabilityLimit_nonnegative
      volume event,
    anchorPhysicalCutoffEventProbabilityLimit_le_one
      volume event⟩

/-- Boolean-event inclusion remains monotone after removing the physical
SU(2) representation cutoff. -/
theorem anchorPhysicalCutoffEventProbabilityLimit_mono
    (volume : Nat)
    (first second : EdgeLabelling → Bool)
    (himp :
      ∀ state, first state = true → second state = true) :
    CReal.leEv
      (anchorPhysicalCutoffEventProbabilityLimit
        volume first)
      (anchorPhysicalCutoffEventProbabilityLimit
        volume second) := by
  intro ε hε
  refine ⟨0, fun cutoff _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (anchorPhysicalCutoffEventProbability_mono
      cutoff volume first second himp)
    (Q'.add_le_self_of_nonneg
      (anchorPhysicalCutoffEventProbability
        cutoff volume second)
      ε (Q'.le_of_lt hε))

/-! ## 3. Constructive complement normalization -/

/-- The limiting probability of an event plus the limiting probability of
its Boolean complement is constructively equivalent to one. -/
theorem
    anchorPhysicalCutoffEventProbabilityLimit_add_complement_equiv_one
    (volume : Nat) (event : EdgeLabelling → Bool) :
    CReal.Equiv
      (CReal.add
        (anchorPhysicalCutoffEventProbabilityLimit
          volume event)
        (anchorPhysicalCutoffEventProbabilityLimit
          volume (fun state => !(event state))))
      CReal.cone := by
  apply Equiv_of_approx_eqv
  intro cutoff
  exact anchorPhysicalCutoffEventProbability_add_complement_eqv_one
    cutoff volume event

#print axioms
  anchorPhysicalCutoffEventNumerator_add_complement_eqv_partition
#print axioms anchorPhysicalCutoffEventProbability_mono
#print axioms anchorPhysicalCutoffEventProbability_add_complement_eqv_one
#print axioms anchorPhysicalCutoffEventProbabilityLimit_nonnegative
#print axioms anchorPhysicalCutoffEventProbabilityLimit_le_one
#print axioms anchorPhysicalCutoffEventProbabilityLimit_mem_unitInterval
#print axioms anchorPhysicalCutoffEventProbabilityLimit_mono
#print axioms
  anchorPhysicalCutoffEventProbabilityLimit_add_complement_equiv_one

end
  YMGap.Continuum.SU2PhysicalOuterCutoffAnchorCRealProbabilityAlgebra
