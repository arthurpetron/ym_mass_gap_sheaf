/-
# Contextual order bridge for the signed four-valent Haar projector

The edge-touching double-cube geometry presents its exceptional-link factors
in the inherited face order

    reverse, forward, reverse, forward.

The signed fourth-moment theorem is stated in the canonical order

    forward, forward, reverse, reverse.

This leaf connects those two literal raw-polynomial words only beneath the
finite-product Haar functional.  The strongest theorem retains arbitrary
left and right complex-polynomial context.  No raw commutativity or
associativity is asserted.

Only the four local factors are permuted.  No face-index assignment space,
bounded labelling family, trajectory, or double-cube trace product is
unfolded or materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
import YMGap.Continuum.SU2QuaternionPlaquetteOrientationHaarReindex

namespace YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjectorReordering

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini
open YMGap.Continuum.SU2QuaternionPlaquetteOrientationHaarReindex
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector

/-! ## 1. Arbitrary-context `R F R F` to `F F R R` permutation -/

/-- **Contextual exceptional-link order bridge.** Exactly the four displayed
factors are permuted from the literal double-cube order `R F R F` to the
canonical projector order `F F R R`.  The left spectator and right suffix
remain fixed.  This is a Haar-value theorem, not raw polynomial equality. -/
theorem finiteProductHaarComplex_mul_mulFourLeft_reverseForwardReverseForward
    (blockCount : Nat)
    (spectator firstReverse firstForward secondReverse secondForward suffix :
      ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyMulFourLeft
              firstReverse firstForward secondReverse secondForward)
            suffix)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyMulFourLeft
              firstForward secondForward firstReverse secondReverse)
            suffix))) := by
  have hfirst :
      [firstReverse, firstForward, secondReverse, secondForward, suffix].Perm
        [firstForward, firstReverse, secondReverse, secondForward, suffix] :=
    List.Perm.swap firstForward firstReverse
      [secondReverse, secondForward, suffix]
  have hsecond :
      [firstForward, firstReverse, secondReverse, secondForward, suffix].Perm
        [firstForward, firstReverse, secondForward, secondReverse, suffix] :=
    List.Perm.cons firstForward
      (List.Perm.cons firstReverse
        (List.Perm.swap secondForward secondReverse [suffix]))
  have hthird :
      [firstForward, firstReverse, secondForward, secondReverse, suffix].Perm
        [firstForward, secondForward, firstReverse, secondReverse, suffix] :=
    List.Perm.cons firstForward
      (List.Perm.swap secondForward firstReverse [secondReverse, suffix])
  have hperm :
      [firstReverse, firstForward, secondReverse, secondForward, suffix].Perm
        [firstForward, secondForward, firstReverse, secondReverse, suffix] :=
    hfirst.trans (hsecond.trans hthird)
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_mulFourLeft_mul_eq_foldlFive
      blockCount spectator firstReverse firstForward secondReverse
        secondForward suffix) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_foldl_eq_mul_product blockCount spectator
      [firstReverse, firstForward, secondReverse, secondForward, suffix]) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_product_perm blockCount spectator hperm) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_foldl_eq_mul_product blockCount spectator
        [firstForward, secondForward, firstReverse, secondReverse, suffix])) ?_
  exact rationalComplexEqv_symm
    (finiteProductHaarComplex_mul_mulFourLeft_mul_eq_foldlFive
      blockCount spectator firstForward secondForward firstReverse
        secondReverse suffix)

/-! ## 2. Local canonicalization and signed projector -/

/-- The same order bridge for a bare left-associated four-factor word. -/
theorem finiteProductHaarComplex_mulFourLeft_reverseForwardReverseForward
    (blockCount : Nat)
    (firstReverse firstForward secondReverse secondForward : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMulFourLeft
          firstReverse firstForward secondReverse secondForward))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMulFourLeft
          firstForward secondForward firstReverse secondReverse)) := by
  unfold complexRatPolyMulFourLeft
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc blockCount
      (complexRatPolyMul firstReverse firstForward)
      secondReverse secondForward) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_four_swap blockCount
      firstReverse firstForward secondReverse secondForward) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_comm blockCount
      (complexRatPolyMul firstReverse secondReverse)
      (complexRatPolyMul firstForward secondForward)) ?_
  exact rationalComplexEqv_symm
    (finiteProductHaarComplex_mul_assoc blockCount
      (complexRatPolyMul firstForward secondForward)
      firstReverse secondReverse)

/-- Literal left-associated exceptional-link coefficient word in inherited
face order `R F R F`. -/
def reverseForwardReverseForwardFundamentalTerm
    (block : Nat)
    (firstReverseRow firstReverseColumn
      firstForwardRow firstForwardColumn
      secondReverseRow secondReverseColumn
      secondForwardRow secondForwardColumn : Bool) : ComplexRatPoly :=
  complexRatPolyMulFourLeft
    (reverseFundamentalCoefficient block
      firstReverseRow firstReverseColumn)
    (forwardFundamentalCoefficient block
      firstForwardRow firstForwardColumn)
    (reverseFundamentalCoefficient block
      secondReverseRow secondReverseColumn)
    (forwardFundamentalCoefficient block
      secondForwardRow secondForwardColumn)

/-- Coefficient-specialized contextual bridge with the complete external
eight-index permutation visible in its statement.  In `R₁,F₁,R₂,F₂` input
order, the canonical projector receives `F₁,F₂,R₁,R₂`, namely argument
permutation `[2,3,6,7,0,1,4,5]`. -/
theorem finiteProductHaarComplex_mul_reverseForwardReverseForwardTerm_eq_canonical
    (blockCount block : Nat) (spectator suffix : ComplexRatPoly)
    (firstReverseRow firstReverseColumn
      firstForwardRow firstForwardColumn
      secondReverseRow secondReverseColumn
      secondForwardRow secondForwardColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (reverseForwardReverseForwardFundamentalTerm block
              firstReverseRow firstReverseColumn
              firstForwardRow firstForwardColumn
              secondReverseRow secondReverseColumn
              secondForwardRow secondForwardColumn)
            suffix)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (twoForwardTwoReverseFundamentalTerm block
              firstForwardRow firstForwardColumn
              secondForwardRow secondForwardColumn
              firstReverseRow firstReverseColumn
              secondReverseRow secondReverseColumn)
            suffix))) := by
  exact
    finiteProductHaarComplex_mul_mulFourLeft_reverseForwardReverseForward
      blockCount spectator
      (reverseFundamentalCoefficient block
        firstReverseRow firstReverseColumn)
      (forwardFundamentalCoefficient block
        firstForwardRow firstForwardColumn)
      (reverseFundamentalCoefficient block
        secondReverseRow secondReverseColumn)
      (forwardFundamentalCoefficient block
        secondForwardRow secondForwardColumn)
      suffix

/-- **Signed projector in literal shared-link order.** The external arguments
are displayed in `R₁,F₁,R₂,F₂` order, while the result uses the canonical
projector argument order `F₁,F₂,R₁,R₂`. -/
theorem oneLink_reverseForwardReverseForward_fundamental_projector
    (firstReverseRow firstReverseColumn
      firstForwardRow firstForwardColumn
      secondReverseRow secondReverseColumn
      secondForwardRow secondForwardColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (reverseForwardReverseForwardFundamentalTerm 0
          firstReverseRow firstReverseColumn
          firstForwardRow firstForwardColumn
          secondReverseRow secondReverseColumn
          secondForwardRow secondForwardColumn))
      (orientedFourFundamentalHaarProjector
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn) := by
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mulFourLeft_reverseForwardReverseForward 1
      (reverseFundamentalCoefficient 0
        firstReverseRow firstReverseColumn)
      (forwardFundamentalCoefficient 0
        firstForwardRow firstForwardColumn)
      (reverseFundamentalCoefficient 0
        secondReverseRow secondReverseColumn)
      (forwardFundamentalCoefficient 0
        secondForwardRow secondForwardColumn)) ?_
  exact oneLink_twoForward_twoReverse_fundamental_projector
    firstForwardRow firstForwardColumn
    secondForwardRow secondForwardColumn
    firstReverseRow firstReverseColumn
    secondReverseRow secondReverseColumn

/-- The negative mixed entry survives the literal `R F R F` ordering. -/
theorem oneLink_reverseForwardReverseForward_negative_mixed_entry :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (reverseForwardReverseForwardFundamentalTerm 0
          true false false false
          false true true true))
      (-oneSixth, 0) := by
  refine rationalComplexEqv_trans
    (oneLink_reverseForwardReverseForward_fundamental_projector
      true false false false false true true true) ?_
  constructor <;> decide

/-- This positive off-diagonal entry detects the reverse-coefficient
row/column transpose: with the incorrect untransposed convention the same
external indices would give zero. -/
theorem oneLink_reverseForwardReverseForward_transpose_sensitive_entry :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (reverseForwardReverseForwardFundamentalTerm 0
          false false false false
          true false false true))
      (oneSixth, 0) := by
  refine rationalComplexEqv_trans
    (oneLink_reverseForwardReverseForward_fundamental_projector
      false false false false true false false true) ?_
  constructor <;> decide

#print axioms finiteProductHaarComplex_mul_mulFourLeft_reverseForwardReverseForward
#print axioms finiteProductHaarComplex_mulFourLeft_reverseForwardReverseForward
#print axioms finiteProductHaarComplex_mul_reverseForwardReverseForwardTerm_eq_canonical
#print axioms oneLink_reverseForwardReverseForward_fundamental_projector
#print axioms oneLink_reverseForwardReverseForward_negative_mixed_entry
#print axioms oneLink_reverseForwardReverseForward_transpose_sensitive_entry

end YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjectorReordering
