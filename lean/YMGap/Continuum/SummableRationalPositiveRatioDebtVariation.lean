/-
# Summable variation of a positive rational ratio debt

For positive rational streams `numerator` and `denominator`, the reciprocal
of the ratio `numerator / denominator` is exactly
`denominator / numerator`.  Hence a fixed positive shared floor divided by
that ratio has summable two-sided variation whenever:

* the denominator has summable variation;
* the numerator has summable variation; and
* one positive rational floor stays below every numerator value.

The numerator floor is the precise noncollapse input needed to compile
reciprocal variation.  The two variation streams remain independent until
their product is formed.  No physical or continuum estimate is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.SummableRationalReciprocalStepVariation
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.SummableRationalPositiveRatioDebtVariation

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SummableRationalReciprocalStepVariation
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

local infix:50 " ≈ " => Q'.eqv

private theorem eqv_divPos_of_mul_local
    {a numerator denominator : Q'}
    (denominator_pos : (0 : Q') < denominator)
    (product : a * denominator ≈ numerator) :
    a ≈ Q'.divPos numerator denominator denominator_pos := by
  apply Q'.mul_left_cancel_of_pos denominator_pos
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv denominator a) ?_
  refine Q'.eqv_trans _ _ _ product ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv denominator
      (Q'.divPos numerator denominator denominator_pos)) ?_
  exact Q'.divPos_mul_eqv numerator denominator denominator_pos

private theorem divPos_eqv_of_eqv_mul_local
    {numerator denominator quotient : Q'}
    (denominator_pos : (0 : Q') < denominator)
    (factor : numerator ≈ quotient * denominator) :
    Q'.divPos numerator denominator denominator_pos ≈ quotient := by
  show numerator * Q'.recipPos denominator denominator_pos ≈ quotient
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ factor) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv quotient denominator
      (Q'.recipPos denominator denominator_pos)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left quotient _ _
      (Q'.mul_recipPos_eqv denominator denominator_pos)) ?_
  exact Q'.mul_one_eqv quotient

/-! ## 1. Exact positive ratio algebra -/

/-- A positive numerator divided by a positive denominator. -/
def positiveRatio
    (numerator denominator : Nat -> Q')
    (denominator_pos : forall offset, (0 : Q') < denominator offset)
    (offset : Nat) : Q' :=
  Q'.divPos (numerator offset) (denominator offset)
    (denominator_pos offset)

theorem positiveRatio_pos
    (numerator denominator : Nat -> Q')
    (numerator_pos : forall offset, (0 : Q') < numerator offset)
    (denominator_pos : forall offset, (0 : Q') < denominator offset)
    (offset : Nat) :
    (0 : Q') < positiveRatio numerator denominator denominator_pos offset :=
  Q'.divPos_pos _ _ (denominator_pos offset) (numerator_pos offset)

/-- The reciprocal ratio, written without a nested reciprocal. -/
def reciprocalPositiveRatio
    (numerator denominator : Nat -> Q')
    (numerator_pos : forall offset, (0 : Q') < numerator offset)
    (offset : Nat) : Q' :=
  Q'.divPos (denominator offset) (numerator offset)
    (numerator_pos offset)

theorem reciprocalPositiveRatio_pos
    (numerator denominator : Nat -> Q')
    (numerator_pos : forall offset, (0 : Q') < numerator offset)
    (denominator_pos : forall offset, (0 : Q') < denominator offset)
    (offset : Nat) :
    (0 : Q') <
      reciprocalPositiveRatio numerator denominator numerator_pos offset :=
  Q'.divPos_pos _ _ (numerator_pos offset) (denominator_pos offset)

/-- The reciprocal ratio cancels the original positive ratio. -/
theorem reciprocalPositiveRatio_mul_positiveRatio_eqv_one
    (numerator denominator : Nat -> Q')
    (numerator_pos : forall offset, (0 : Q') < numerator offset)
    (denominator_pos : forall offset, (0 : Q') < denominator offset)
    (offset : Nat) :
    reciprocalPositiveRatio numerator denominator numerator_pos offset *
        positiveRatio numerator denominator denominator_pos offset ≈
      (1 : Q') := by
  let n := numerator offset
  let d := denominator offset
  let reciprocal :=
    reciprocalPositiveRatio numerator denominator numerator_pos offset
  let ratio := positiveRatio numerator denominator denominator_pos offset
  have hn : (0 : Q') < n := numerator_pos offset
  have hd : (0 : Q') < d := denominator_pos offset
  have reciprocal_mul_numerator : reciprocal * n ≈ d := by
    unfold reciprocal reciprocalPositiveRatio
    exact Q'.divPos_mul_eqv d n hn
  have ratio_mul_denominator : ratio * d ≈ n := by
    unfold ratio positiveRatio
    exact Q'.divPos_mul_eqv n d hd
  have product_mul_denominator :
      (reciprocal * ratio) * d ≈ d := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv reciprocal ratio d) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left reciprocal _ _ ratio_mul_denominator) ?_
    exact reciprocal_mul_numerator
  have product_eqv_self_division :
      reciprocal * ratio ≈ Q'.divPos d d hd :=
    eqv_divPos_of_mul_local hd product_mul_denominator
  refine Q'.eqv_trans _ _ _ product_eqv_self_division ?_
  unfold Q'.divPos
  exact Q'.mul_recipPos_eqv d hd

/-- A fixed shared floor divided by the positive ratio. -/
def positiveRatioDebt
    (sharedFloor : Q')
    (numerator denominator : Nat -> Q')
    (numerator_pos : forall offset, (0 : Q') < numerator offset)
    (denominator_pos : forall offset, (0 : Q') < denominator offset)
    (offset : Nat) : Q' :=
  Q'.divPos sharedFloor
    (positiveRatio numerator denominator denominator_pos offset)
    (positiveRatio_pos numerator denominator numerator_pos denominator_pos
      offset)

/-- Exact factorization of the debt into the shared floor times the
reciprocal ratio. -/
theorem positiveRatioDebt_eqv_sharedFloor_mul_reciprocal
    (sharedFloor : Q')
    (numerator denominator : Nat -> Q')
    (numerator_pos : forall offset, (0 : Q') < numerator offset)
    (denominator_pos : forall offset, (0 : Q') < denominator offset)
    (offset : Nat) :
    positiveRatioDebt sharedFloor numerator denominator
        numerator_pos denominator_pos offset ≈
      sharedFloor *
        reciprocalPositiveRatio numerator denominator numerator_pos offset := by
  let ratio := positiveRatio numerator denominator denominator_pos offset
  let reciprocal :=
    reciprocalPositiveRatio numerator denominator numerator_pos offset
  have ratio_pos : (0 : Q') < ratio :=
    positiveRatio_pos numerator denominator numerator_pos denominator_pos
      offset
  have cancellation : reciprocal * ratio ≈ (1 : Q') :=
    reciprocalPositiveRatio_mul_positiveRatio_eqv_one
      numerator denominator numerator_pos denominator_pos offset
  have factor : sharedFloor ≈
      (sharedFloor * reciprocal) * ratio := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv sharedFloor reciprocal ratio) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left sharedFloor _ _ cancellation) ?_
    exact Q'.mul_one_eqv sharedFloor
  unfold positiveRatioDebt
  exact divPos_eqv_of_eqv_mul_local ratio_pos factor

/-! ## 2. The two variation lanes and their contraction -/

/-- Summable numerator variation plus a positive noncollapse floor compiles
to summable variation of the reciprocal numerator. -/
def reciprocalNumeratorVariation
    (numerator : Nat -> Q')
    (numerator_pos : forall offset, (0 : Q') < numerator offset)
    (numeratorVariation : SummableRationalStepVariation numerator)
    (numeratorFloor : Q')
    (numeratorFloor_pos : (0 : Q') < numeratorFloor)
    (numeratorFloor_le : forall offset,
      numeratorFloor <= numerator offset) :
    SummableRationalStepVariation
      (fun offset => Q'.recipPos (numerator offset) (numerator_pos offset)) :=
  reciprocal numerator_pos numeratorVariation
    numeratorFloor numeratorFloor_pos numeratorFloor_le

/-- The load/denominator variation and kernel/numerator variation meet only
at this product.  The numerator floor supplies the required reciprocal
continuity; all product ceilings are derived from the variations. -/
def reciprocalPositiveRatioVariationOfPrimitiveComponents
    (numerator denominator : Nat -> Q')
    (numerator_pos : forall offset, (0 : Q') < numerator offset)
    (denominator_pos : forall offset, (0 : Q') < denominator offset)
    (denominatorVariation : SummableRationalStepVariation denominator)
    (numeratorVariation : SummableRationalStepVariation numerator)
    (numeratorFloor : Q')
    (numeratorFloor_pos : (0 : Q') < numeratorFloor)
    (numeratorFloor_le : forall offset,
      numeratorFloor <= numerator offset) :
    SummableRationalStepVariation
      (reciprocalPositiveRatio numerator denominator numerator_pos) := by
  let inverseVariation := reciprocalNumeratorVariation
    numerator numerator_pos numeratorVariation
    numeratorFloor numeratorFloor_pos numeratorFloor_le
  have productVariation := mul denominatorVariation inverseVariation
    (fun offset => Q'.le_of_lt (denominator_pos offset))
    (fun offset => Q'.le_of_lt
      (Q'.recipPos_pos (numerator offset) (numerator_pos offset)))
  exact ofPointwiseEqv productVariation (fun offset => by
    unfold reciprocalPositiveRatio Q'.divPos
    exact Q'.eqv_refl _)

/-- Serially scale the joined reciprocal-ratio variation and transport it
through the exact debt factorization. -/
def positiveRatioDebtVariationOfPrimitiveComponents
    (sharedFloor : Q')
    (sharedFloor_pos : (0 : Q') < sharedFloor)
    (numerator denominator : Nat -> Q')
    (numerator_pos : forall offset, (0 : Q') < numerator offset)
    (denominator_pos : forall offset, (0 : Q') < denominator offset)
    (denominatorVariation : SummableRationalStepVariation denominator)
    (numeratorVariation : SummableRationalStepVariation numerator)
    (numeratorFloor : Q')
    (numeratorFloor_pos : (0 : Q') < numeratorFloor)
    (numeratorFloor_le : forall offset,
      numeratorFloor <= numerator offset) :
    SummableRationalStepVariation
      (positiveRatioDebt sharedFloor numerator denominator
        numerator_pos denominator_pos) := by
  let reciprocalVariation :=
    reciprocalPositiveRatioVariationOfPrimitiveComponents
      numerator denominator numerator_pos denominator_pos
      denominatorVariation numeratorVariation
      numeratorFloor numeratorFloor_pos numeratorFloor_le
  let scaledVariation := scale reciprocalVariation
    sharedFloor sharedFloor_pos
  exact ofPointwiseEqv scaledVariation (fun offset =>
    Q'.eqv_symm
      (positiveRatioDebt_eqv_sharedFloor_mul_reciprocal
        sharedFloor numerator denominator numerator_pos denominator_pos
        offset))

end YMGap.Continuum.SummableRationalPositiveRatioDebtVariation

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.SummableRationalPositiveRatioDebtVariation.reciprocalPositiveRatio_mul_positiveRatio_eqv_one
#print axioms
  YMGap.Continuum.SummableRationalPositiveRatioDebtVariation.positiveRatioDebt_eqv_sharedFloor_mul_reciprocal
#print axioms
  YMGap.Continuum.SummableRationalPositiveRatioDebtVariation.reciprocalNumeratorVariation
#print axioms
  YMGap.Continuum.SummableRationalPositiveRatioDebtVariation.reciprocalPositiveRatioVariationOfPrimitiveComponents
#print axioms
  YMGap.Continuum.SummableRationalPositiveRatioDebtVariation.positiveRatioDebtVariationOfPrimitiveComponents
