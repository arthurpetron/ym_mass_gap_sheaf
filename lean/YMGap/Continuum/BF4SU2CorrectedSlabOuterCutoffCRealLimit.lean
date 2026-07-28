/-
# Bishop limit of corrected-slab SU(2) cutoff events

At the fixed strong-coupling anchor, one corrected reflection-slab extent,
and one Boolean predicate of its physical face labels, the exact normalized
Peter--Weyl cutoff probabilities form a Bishop-Cauchy sequence.

This module uses the existing executable modulus and two-sided estimate from
`BF4SU2CorrectedSlabOuterCutoffTail` without changing that analytic module.
It constructs the resulting `CReal`, proves convergence and uniqueness, and
transports the finite unit-interval and Boolean-complement identities to the
limit.

The result is fixed at `anchorCoupling` and at one finite corrected-slab
extent.  It is not a spacing, continuum, or infinite-volume limit.

## Axiom gate

No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, choice,
functional extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealComplete
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffCRealLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact sequence and canonical Bishop limit -/

/-- Exact normalized corrected-slab cutoff probability lifted to a constant
constructive real at each representation cutoff. -/
def slabAnchorCutoffEventProbabilitySeq
    (extent : Nat) (event : EdgeLabelling → Bool) :
    Nat → CReal :=
  fun cutoff =>
    CReal.ofQ'
      (slabAnchorCutoffEventProbability
        cutoff extent event)

/-- Canonical cutoff-free event probability on one fixed corrected slab. -/
def slabAnchorCutoffEventProbabilityLimit
    (extent : Nat)
    (event : EdgeLabelling → Bool) : CReal where
  approx cutoff :=
    slabAnchorCutoffEventProbability
      cutoff extent event
  cauchy := by
    intro ε hε
    refine
      ⟨slabAnchorEventProbabilityModulus extent ε,
        fun first second hfirst hsecond => ?_⟩
    exact
      slabAnchorCutoffEventProbability_twoSided_of_modulus
        extent event hε hfirst hsecond

@[simp] theorem slabAnchorCutoffEventProbabilityLimit_approx
    (extent cutoff : Nat)
    (event : EdgeLabelling → Bool) :
    (slabAnchorCutoffEventProbabilityLimit
      extent event).approx cutoff =
        slabAnchorCutoffEventProbability
          cutoff extent event :=
  rfl

/-- The exact cutoff probabilities converge with precisely the already
constructed slab modulus on both indices. -/
theorem slabAnchorCutoffEventProbabilitySeq_converges
    (extent : Nat)
    (event : EdgeLabelling → Bool) :
    CReal.ConvergesTo
      (slabAnchorCutoffEventProbabilitySeq
        extent event)
      (slabAnchorCutoffEventProbabilityLimit
        extent event) := by
  intro ε hε
  let retained :=
    slabAnchorEventProbabilityModulus extent ε
  refine
    ⟨retained, fun cutoff hcutoff =>
      ⟨retained, fun approximation happ => ?_⟩⟩
  change
    slabAnchorCutoffEventProbability
          cutoff extent event ≤
        slabAnchorCutoffEventProbability
            approximation extent event + ε ∧
      slabAnchorCutoffEventProbability
          approximation extent event ≤
        slabAnchorCutoffEventProbability
            cutoff extent event + ε
  exact
    slabAnchorCutoffEventProbability_twoSided_of_modulus
      extent event hε hcutoff happ

private theorem crealEquiv_refl (x : CReal) :
    CReal.Equiv x x :=
  fun ε hε =>
    ⟨0, fun n _ =>
      ⟨Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε),
        Q'.add_le_self_of_nonneg
          (x.approx n) ε
          (Q'.le_of_lt hε)⟩⟩

/-- Constructive uniqueness of the corrected-slab cutoff limit. -/
theorem slabAnchorCutoffEventProbabilityLimit_equiv_of_converges
    (extent : Nat)
    (event : EdgeLabelling → Bool)
    (limit : CReal)
    (hlimit :
      CReal.ConvergesTo
        (slabAnchorCutoffEventProbabilitySeq
          extent event)
        limit) :
    CReal.Equiv
      (slabAnchorCutoffEventProbabilityLimit
        extent event)
      limit := by
  exact CReal.Equiv_of_limit_of_equal
    (fun cutoff =>
      crealEquiv_refl
        (slabAnchorCutoffEventProbabilitySeq
          extent event cutoff))
    (slabAnchorCutoffEventProbabilitySeq_converges
      extent event)
    hlimit

/-! ## 2. Finite-stage and limiting unit interval -/

theorem slabAnchorCutoffEventProbability_nonnegative
    (cutoff extent : Nat)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤
      slabAnchorCutoffEventProbability
        cutoff extent event := by
  unfold slabAnchorCutoffEventProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (slabParametricKEventNumerator_nonnegative
      (w := anchorCoupling) (by decide)
      cutoff extent event)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (slabParametricKPhysicalPartition_pos
          (w := anchorCoupling)
          (by decide) cutoff extent)))

theorem slabAnchorCutoffEventProbability_le_one
    (cutoff extent : Nat)
    (event : EdgeLabelling → Bool) :
    slabAnchorCutoffEventProbability
        cutoff extent event ≤
      (1 : Q') := by
  unfold slabAnchorCutoffEventProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (slabParametricKEventNumerator_le_partition
      (w := anchorCoupling) (by decide)
      cutoff extent event)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (slabParametricKPhysicalPartition
          anchorCoupling cutoff extent)))

theorem slabAnchorCutoffEventProbabilityLimit_nonnegative
    (extent : Nat)
    (event : EdgeLabelling → Bool) :
    CReal.leEv CReal.czero
      (slabAnchorCutoffEventProbabilityLimit
        extent event) := by
  apply CReal.leEv_ofQ'_of_approx_ge
  intro cutoff
  exact
    slabAnchorCutoffEventProbability_nonnegative
      cutoff extent event

theorem slabAnchorCutoffEventProbabilityLimit_le_one
    (extent : Nat)
    (event : EdgeLabelling → Bool) :
    CReal.leEv
      (slabAnchorCutoffEventProbabilityLimit
        extent event)
      CReal.cone := by
  apply CReal.leEv_le_ofQ'_of_approx_le
  intro cutoff
  exact
    slabAnchorCutoffEventProbability_le_one
      cutoff extent event

theorem slabAnchorCutoffEventProbabilityLimit_mem_unitInterval
    (extent : Nat)
    (event : EdgeLabelling → Bool) :
    CReal.leEv CReal.czero
        (slabAnchorCutoffEventProbabilityLimit
          extent event) ∧
      CReal.leEv
        (slabAnchorCutoffEventProbabilityLimit
          extent event)
        CReal.cone :=
  ⟨slabAnchorCutoffEventProbabilityLimit_nonnegative
      extent event,
    slabAnchorCutoffEventProbabilityLimit_le_one
      extent event⟩

/-! ## 3. Boolean-complement normalization -/

private theorem listQSum_mask_eq_filter_local
    {A : Type} (weight : A → Q')
    (event : A → Bool) :
    ∀ source : List A,
      listQSum
          (fun item =>
            if event item then weight item else 0)
          source ≈
        listQSum weight (source.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head
      · simp only [listQSum, hevent,
          Bool.false_eq_true, ↓reduceIte,
          List.filter_cons]
        exact Q'.eqv_trans _
          (0 + listQSum weight
            (tail.filter event)) _
          (Q'.add_eqv_congr_left 0 _
            (listQSum weight (tail.filter event))
            (listQSum_mask_eq_filter_local
              weight event tail))
          (QPoly.q_zero_add_eqv
            (listQSum weight
              (tail.filter event)))
      · simp only [listQSum, hevent,
          ↓reduceIte, List.filter_cons]
        exact Q'.add_eqv_congr_left
          (weight head)
          (listQSum
            (fun item =>
              if event item
                then weight item else 0)
            tail)
          (listQSum weight (tail.filter event))
          (listQSum_mask_eq_filter_local
            weight event tail)

/-- At every finite cutoff, an event numerator and its Boolean complement
partition the complete corrected-slab mass exactly. -/
theorem slabAnchorCutoffEventNumerator_add_complement_eqv_partition
    (cutoff extent : Nat)
    (event : EdgeLabelling → Bool) :
    slabParametricKEventNumerator
          anchorCoupling cutoff extent event +
        slabParametricKEventNumerator
          anchorCoupling cutoff extent
          (fun state => !(event state)) ≈
      slabParametricKPhysicalPartition
        anchorCoupling cutoff extent := by
  unfold slabParametricKEventNumerator
    slabParametricKEventTerm
    slabParametricKPhysicalPartition
  let states :=
    boundedEdgeLabellings cutoff
      (slabPhysicalFaceEdges extent)
  let weight :=
    slabParametricKPhysicalTerm
      anchorCoupling cutoff extent
  have hevent :=
    listQSum_mask_eq_filter_local
      weight event states
  have hcomplement :=
    listQSum_mask_eq_filter_local
      weight (fun state => !(event state)) states
  have hpartition :=
    listQSum_filter_partition
      weight event states
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hevent hcomplement)
    (Q'.eqv_symm hpartition)

private theorem add_divPos_eqv_local
    (p q d : Q') (hd : (0 : Q') < d) :
    Q'.divPos p d hd + Q'.divPos q d hd ≈
      Q'.divPos (p + q) d hd :=
  Q'.eqv_symm
    (Q'.add_mul_eqv
      p q (Q'.recipPos d hd))

theorem slabAnchorCutoffEventProbability_add_complement_eqv_one
    (cutoff extent : Nat)
    (event : EdgeLabelling → Bool) :
    slabAnchorCutoffEventProbability
          cutoff extent event +
        slabAnchorCutoffEventProbability
          cutoff extent
          (fun state => !(event state)) ≈
      (1 : Q') := by
  have hsplit :=
    slabAnchorCutoffEventNumerator_add_complement_eqv_partition
      cutoff extent event
  unfold slabAnchorCutoffEventProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (slabParametricKEventNumerator
        anchorCoupling cutoff extent event)
      (slabParametricKEventNumerator
        anchorCoupling cutoff extent
        (fun state => !(event state)))
      (slabParametricKPhysicalPartition
        anchorCoupling cutoff extent)
      (slabParametricKPhysicalPartition_pos
        (w := anchorCoupling)
        (by decide) cutoff extent)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos
        (slabParametricKPhysicalPartition
          anchorCoupling cutoff extent)
        (slabParametricKPhysicalPartition_pos
          (w := anchorCoupling)
          (by decide) cutoff extent))
      hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (slabParametricKPhysicalPartition
      anchorCoupling cutoff extent)
    (slabParametricKPhysicalPartition_pos
      (w := anchorCoupling)
      (by decide) cutoff extent)

theorem
    slabAnchorCutoffEventProbabilityLimit_add_complement_equiv_one
    (extent : Nat)
    (event : EdgeLabelling → Bool) :
    CReal.Equiv
      (CReal.add
        (slabAnchorCutoffEventProbabilityLimit
          extent event)
        (slabAnchorCutoffEventProbabilityLimit
          extent (fun state => !(event state))))
      CReal.cone := by
  apply Equiv_of_approx_eqv
  intro cutoff
  exact
    slabAnchorCutoffEventProbability_add_complement_eqv_one
      cutoff extent event

/-! ## Axiom audit -/

#print axioms slabAnchorEventProbabilityModulus
#print axioms slabAnchorCutoffEventProbabilityLimit
#print axioms slabAnchorCutoffEventProbabilitySeq_converges
#print axioms
  slabAnchorCutoffEventProbabilityLimit_equiv_of_converges
#print axioms
  slabAnchorCutoffEventProbabilityLimit_mem_unitInterval
#print axioms
  slabAnchorCutoffEventProbabilityLimit_add_complement_equiv_one

end YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffCRealLimit
