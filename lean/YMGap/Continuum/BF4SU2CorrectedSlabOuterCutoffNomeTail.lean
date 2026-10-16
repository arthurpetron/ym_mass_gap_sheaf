/-
# Arbitrary-nome corrected-slab outer-cutoff tails

The corrected-slab retained/new-sector decomposition is coupling-parametric,
and its new-sector mass injects into the corresponding ambient-box mass at
the same nome.  Combining that exact injection with the existing
arbitrary-nome degree-thirteen tensor-tail schedule gives an executable
cutoff modulus for every fixed rational `0 < w < 1`, fixed slab extent, and
Boolean event of the physical face labelling.

This removes the strong-coupling anchor from the corrected-slab cutoff
estimate.  The modulus still depends on `w` and may diverge as `w` approaches
one.  No estimate comparing different nomes is proved here, and there is no
uniform AF-scale modulus, continuum limit, spectral gap, or Clay theorem.

Constructive contract: finite weighted sums, rational inequalities, and the
existing executable arbitrary-nome tail schedule only; no choice,
`Classical`, `native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
import YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance

namespace YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffNomeTail

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Arbitrary-nome normalized corrected-slab events -/

/-- Normalized corrected-slab probability of a Boolean event at arbitrary
nonnegative rational nome. -/
def slabNomeCutoffEventProbability
    (w : Q') (hw0 : (0 : Q') ≤ w)
    (cutoff extent : Nat)
    (event : EdgeLabelling → Bool) : Q' :=
  Q'.divPos
    (slabParametricKEventNumerator
      w cutoff extent event)
    (slabParametricKPhysicalPartition
      w cutoff extent)
    (slabParametricKPhysicalPartition_pos
      hw0 cutoff extent)

private theorem qeqv_of_le_of_ge_local
    {left right : Q'}
    (hleft : left ≤ right) (hright : right ≤ left) :
    left ≈ right := by
  show left.num * (right.den : Int) =
    right.num * (left.den : Int)
  exact Int.le_antisymm hleft hright

private theorem divPos_eqv_congr_local
    {numerator numerator' denominator denominator' : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hdenominator' : (0 : Q') < denominator')
    (hnumerator : numerator ≈ numerator')
    (hdenominatorEq : denominator ≈ denominator') :
    Q'.divPos numerator denominator hdenominator ≈
      Q'.divPos numerator' denominator' hdenominator' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator denominator hdenominator)
          denominator' denominator
          (Q'.eqv_symm hdenominatorEq))
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator denominator hdenominator)
          hnumerator))
  · apply Q'.le_divPos_of_mul_le
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator' denominator' hdenominator')
          denominator denominator' hdenominatorEq)
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator' denominator' hdenominator')
          (Q'.eqv_symm hnumerator)))

/-- The normalized corrected-slab change is bounded sharply by the complete
new-label mass, at every nonnegative nome. -/
theorem slabNomeCutoffEventProbability_abs_le_increment
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    {retained later extent : Nat}
    (hcutoff : retained ≤ later)
    (event : EdgeLabelling → Bool) :
    absQ
        (slabNomeCutoffEventProbability
            w hw0 retained extent event +
          -slabNomeCutoffEventProbability
            w hw0 later extent event) ≤
      slabParametricKCutoffIncrement
        w retained later extent := by
  let baseEvent :=
    slabParametricKEventNumerator
      w retained extent event
  let newEvent :=
    slabParametricKEventCutoffIncrement
      w retained later extent event
  let basePartition :=
    slabParametricKPhysicalPartition
      w retained extent
  let newPartition :=
    slabParametricKCutoffIncrement
      w retained later extent
  let laterEvent :=
    slabParametricKEventNumerator
      w later extent event
  let laterPartition :=
    slabParametricKPhysicalPartition
      w later extent
  have hbaseEvent : (0 : Q') ≤ baseEvent := by
    dsimp only [baseEvent]
    exact slabParametricKEventNumerator_nonnegative
      hw0 retained extent event
  have hnewEvent : (0 : Q') ≤ newEvent := by
    dsimp only [newEvent]
    exact slabParametricKEventCutoffIncrement_nonnegative
      hw0 retained later extent event
  have hnewPartition : (0 : Q') ≤ newPartition := by
    dsimp only [newPartition]
    exact slabParametricKCutoffIncrement_nonnegative
      hw0 retained later extent
  have hbasePartitionOne : (1 : Q') ≤ basePartition := by
    dsimp only [basePartition]
    exact slabParametricKPhysicalPartition_one_le
      hw0 retained extent
  have hbaseEventPartition : baseEvent ≤ basePartition := by
    dsimp only [baseEvent, basePartition]
    exact slabParametricKEventNumerator_le_partition
      hw0 retained extent event
  have hnewEventPartition : newEvent ≤ newPartition := by
    dsimp only [newEvent, newPartition]
    exact slabParametricKEventCutoffIncrement_le_total
      hw0 retained later extent event
  have hnested :=
    nested_normalized_event_abs_le_newMass
      hbaseEvent hnewEvent hnewPartition
      hbasePartitionOne hbaseEventPartition
      hnewEventPartition
  have hbasePartitionPos : (0 : Q') < basePartition :=
    YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
      (by decide) hbasePartitionOne
  have hsumPartitionPos :
      (0 : Q') < basePartition + newPartition :=
    YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
      (by decide)
      (Q'.le_trans' _ _ _ hbasePartitionOne
        (Q'.add_le_self_of_nonneg
          basePartition newPartition hnewPartition))
  have hlaterEvent :
      laterEvent ≈ baseEvent + newEvent := by
    dsimp only [laterEvent, baseEvent, newEvent]
    exact
      slabParametricKEventNumerator_eq_base_add_increment
        hcutoff event
  have hlaterPartition :
      laterPartition ≈ basePartition + newPartition := by
    dsimp only [laterPartition, basePartition, newPartition]
    exact
      slabParametricKPhysicalPartition_eq_base_add_increment
        hcutoff
  have hlaterPartitionPos : (0 : Q') < laterPartition := by
    dsimp only [laterPartition]
    exact slabParametricKPhysicalPartition_pos
      hw0 later extent
  have hlaterRatio :
      Q'.divPos laterEvent laterPartition hlaterPartitionPos ≈
        Q'.divPos
          (baseEvent + newEvent)
          (basePartition + newPartition)
          hsumPartitionPos :=
    divPos_eqv_congr_local
      hlaterPartitionPos hsumPartitionPos
      hlaterEvent hlaterPartition
  unfold slabNomeCutoffEventProbability
  dsimp only [baseEvent, newEvent, basePartition,
    newPartition, laterEvent, laterPartition]
    at hnested hlaterRatio ⊢
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (YMGap.Continuum.ContinuumYMStack.absQ_eqv_congr
        (Q'.add_eqv_congr_left
          (Q'.divPos
            (slabParametricKEventNumerator
              w retained extent event)
            (slabParametricKPhysicalPartition
              w retained extent)
            (slabParametricKPhysicalPartition_pos
              hw0 retained extent))
          _
          (-(Q'.divPos
            (slabParametricKEventNumerator
                w retained extent event +
              slabParametricKEventCutoffIncrement
                w retained later extent event)
            (slabParametricKPhysicalPartition
                w retained extent +
              slabParametricKCutoffIncrement
                w retained later extent)
            hsumPartitionPos))
          (Q'.neg_eqv_congr _ _ hlaterRatio))))
    hnested

/-! ## 2. Executable arbitrary-nome slab tolerance -/

/-- The corrected-slab new-label mass inherits the arbitrary-nome ambient
tensor-tail tolerance. -/
theorem slabNomeCutoffIncrement_le_tolerance
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (extent : Nat) {ε : Q'} (hε : (0 : Q') < ε)
    {later : Nat}
    (hcutoff :
      physicalNomeTensorToleranceRetainedCutoff
          w (plaquetteEdgeCount (extent + 1)) ε ≤ later) :
    slabParametricKCutoffIncrement
        w
        (physicalNomeTensorToleranceRetainedCutoff
          w (plaquetteEdgeCount (extent + 1)) ε)
        later extent ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (slabParametricKCutoffIncrement_le_ambient
      (w := w) (Q'.le_of_lt hw0))
    (physicalNomeCutoffIncrement_le_tolerance
      hw0 hw1 (extent + 1) hε hcutoff)

/-- Arbitrary-nome normalized Boolean-event stability at the executable
retained cutoff, uniformly in every later corrected-slab cutoff. -/
theorem slabNomeCutoffEventProbability_abs_le_tolerance
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (extent : Nat) {ε : Q'} (hε : (0 : Q') < ε)
    {later : Nat}
    (hcutoff :
      physicalNomeTensorToleranceRetainedCutoff
          w (plaquetteEdgeCount (extent + 1)) ε ≤ later)
    (event : EdgeLabelling → Bool) :
    absQ
        (slabNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            (physicalNomeTensorToleranceRetainedCutoff
              w (plaquetteEdgeCount (extent + 1)) ε)
            extent event +
          -slabNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            later extent event) ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (slabNomeCutoffEventProbability_abs_le_increment
      (Q'.le_of_lt hw0) hcutoff event)
    (slabNomeCutoffIncrement_le_tolerance
      hw0 hw1 extent hε hcutoff)

/-! ## 3. Bishop-Cauchy modulus at fixed nome and extent -/

/-- Event-independent corrected-slab cutoff modulus at fixed nome and
extent. -/
def slabNomeCutoffEventProbabilityModulus
    (w : Q') (extent : Nat) (ε : Q') : Nat :=
  physicalNomeTensorToleranceRetainedCutoff
    w (plaquetteEdgeCount (extent + 1))
    (half * ε)

private theorem slabNomeCutoffEventProbability_from_modulus_abs_le_half
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (extent : Nat) (event : EdgeLabelling → Bool)
    {ε : Q'} (hε : (0 : Q') < ε)
    {later : Nat}
    (hcutoff :
      slabNomeCutoffEventProbabilityModulus
          w extent ε ≤ later) :
    absQ
        (slabNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            (slabNomeCutoffEventProbabilityModulus
              w extent ε)
            extent event +
          -slabNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            later extent event) ≤
      half * ε := by
  have hhalf : (0 : Q') < half * ε :=
    YMGap.Constructive.ExpNeg.half_mul_pos ε hε
  exact slabNomeCutoffEventProbability_abs_le_tolerance
    hw0 hw1 extent hhalf hcutoff event

private theorem twoSided_of_absQ_sub_le
    {left right ε : Q'}
    (hbound : absQ (left + (-right)) ≤ ε) :
    left ≤ right + ε ∧ right ≤ left + ε := by
  have habs : Q'.abs (left + (-right)) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (YMGap.Continuum.ContinuumYMStack.absQ_eqv_abs
            (left + (-right)))))
      hbound
  constructor
  · exact
      YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
        habs
  · apply
      YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          right left))
      habs

private theorem add_two_halves_le
    (value ε : Q') :
    (value + half * ε) + half * ε ≤
      value + ε := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.add_assoc_eqv
        value (half * ε) (half * ε))) ?_
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr_left
      value
      (half * ε + half * ε)
      ε
      (YMGap.Constructive.ExpNeg.two_halves ε))

/-- Every two corrected-slab cutoffs beyond the arbitrary-nome modulus are
two-sided `ε`-close, uniformly over Boolean events. -/
theorem slabNomeCutoffEventProbability_twoSided_of_modulus
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (extent : Nat) (event : EdgeLabelling → Bool)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      slabNomeCutoffEventProbabilityModulus
        w extent ε ≤ first)
    (hsecond :
      slabNomeCutoffEventProbabilityModulus
        w extent ε ≤ second) :
    slabNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          first extent event ≤
        slabNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            second extent event + ε ∧
      slabNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          second extent event ≤
        slabNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            first extent event + ε := by
  let halfTolerance := half * ε
  have hfirstHalf :=
    twoSided_of_absQ_sub_le
      (slabNomeCutoffEventProbability_from_modulus_abs_le_half
        hw0 hw1 extent event hε hfirst)
  have hsecondHalf :=
    twoSided_of_absQ_sub_le
      (slabNomeCutoffEventProbability_from_modulus_abs_le_half
        hw0 hw1 extent event hε hsecond)
  constructor
  · have hchain :
      slabNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          first extent event ≤
        (slabNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            second extent event + halfTolerance) +
          halfTolerance :=
      Q'.le_trans' _ _ _
        hfirstHalf.2
        (Q'.add_le_add_right _ _ halfTolerance
          hsecondHalf.1)
    exact Q'.le_trans' _ _ _ hchain
      (add_two_halves_le
        (slabNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          second extent event) ε)
  · have hchain :
      slabNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          second extent event ≤
        (slabNomeCutoffEventProbability
            w (Q'.le_of_lt hw0)
            first extent event + halfTolerance) +
          halfTolerance :=
      Q'.le_trans' _ _ _
        hsecondHalf.2
        (Q'.add_le_add_right _ _ halfTolerance
          hfirstHalf.1)
    exact Q'.le_trans' _ _ _ hchain
      (add_two_halves_le
        (slabNomeCutoffEventProbability
          w (Q'.le_of_lt hw0)
          first extent event) ε)

/-! ## Axiom audit -/

#print axioms slabNomeCutoffEventProbability
#print axioms slabNomeCutoffEventProbability_abs_le_increment
#print axioms slabNomeCutoffIncrement_le_tolerance
#print axioms slabNomeCutoffEventProbability_abs_le_tolerance
#print axioms slabNomeCutoffEventProbabilityModulus
#print axioms slabNomeCutoffEventProbability_twoSided_of_modulus

end YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffNomeTail
