/-
# Haar reordering of distinct-block fundamental contraction products

The established contraction product is deliberately right-local:

    contractionProductOver one (step :: steps)
      = contractionProductOver one steps * (forward(step) * reverse(step)).

The geometric occurrence certificate instead exposes the schedule-order
coefficient word

    [forward(step), reverse(step), ...].

These expressions are not raw-equal.  This leaf proves their equality only
after the exact finite-product Haar functional, using the constructive
four-factor/contextual reordering facade.  The induction retains an arbitrary
left spectator; this is essential because equality of bare Haar values is not
a multiplication congruence.

No concrete schedule, Boolean assignment family, or global product is
unfolded here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
import YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct

namespace YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionReordering

open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct

/-! ## 1. Symbolic coefficient words -/

/-- The forward and reverse honest complex coefficient factors carried by one
oriented fundamental contraction, in their established within-row order. -/
def orientedFundamentalContractionCoefficientFactors
    (step : OrientedFundamentalContraction) : List ComplexRatPoly :=
  [forwardFundamentalCoefficient step.block
      step.forwardRow step.forwardColumn,
   reverseFundamentalCoefficient step.block
      step.reverseRow step.reverseColumn]

/-- Schedule-order flattening of all forward/reverse coefficient pairs. -/
def fundamentalContractionCoefficientWord
    (schedule : List OrientedFundamentalContraction) : List ComplexRatPoly :=
  schedule.flatMap orientedFundamentalContractionCoefficientFactors

/-! ## 2. Suffix-strengthened fold reconciliation -/

/-- Reversing the schedule and then flattening its coefficient rows gives a
permutation of the schedule-order word.  Within each row, forward still
precedes reverse. -/
theorem fundamentalContractionCoefficientWord_reverse_perm
    (schedule : List OrientedFundamentalContraction) :
    (fundamentalContractionCoefficientWord schedule.reverse).Perm
      (fundamentalContractionCoefficientWord schedule) :=
  List.Perm.flatMap_right orientedFundamentalContractionCoefficientFactors
    (List.reverse_perm schedule)

/-- The exact structural core.  Appending an arbitrary tail-first suffix to
the right-local fold is Haar-equivalent to placing the reverse-schedule
coefficient word before that suffix, with the external base retained.

The suffix is the induction invariant: one cons step uses the four-factor
reassociation

```text
((tail * forward) * (reverse * suffix))
```

and then recurses with `forward :: reverse :: suffix`.  Thus no recursive
Haar equivalence is transported through an unproved multiplication
congruence. -/
theorem finiteProductHaarComplex_contractionProductOver_mul_product_eq_reverseWord
    (blockCount : Nat) (base : ComplexRatPoly) :
    ∀ (schedule : List OrientedFundamentalContraction)
      (suffix : List ComplexRatPoly),
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul
            (contractionProductOver base schedule)
            (complexRatPolyProduct suffix)))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul base
            (complexRatPolyProduct
              (fundamentalContractionCoefficientWord schedule.reverse ++
                suffix))))
  | [], suffix =>
      rationalComplexEqv_refl
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul base (complexRatPolyProduct suffix)))
  | step :: steps, suffix => by
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_four_assoc blockCount
          (contractionProductOver base steps)
          (forwardFundamentalCoefficient step.block
            step.forwardRow step.forwardColumn)
          (reverseFundamentalCoefficient step.block
            step.reverseRow step.reverseColumn)
          (complexRatPolyProduct suffix)) ?_
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_assoc blockCount
          (contractionProductOver base steps)
          (forwardFundamentalCoefficient step.block
            step.forwardRow step.forwardColumn)
          (complexRatPolyMul
            (reverseFundamentalCoefficient step.block
              step.reverseRow step.reverseColumn)
            (complexRatPolyProduct suffix))) ?_
      simpa only [contractionProductOver,
        OrientedFundamentalContraction.polynomial,
        orientedFundamentalLinkContraction,
        fundamentalContractionCoefficientWord,
        orientedFundamentalContractionCoefficientFactors,
        List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_assoc, List.append_nil,
        complexRatPolyProduct] using
        (finiteProductHaarComplex_contractionProductOver_mul_product_eq_reverseWord
          blockCount base steps
          (forwardFundamentalCoefficient step.block
              step.forwardRow step.forwardColumn ::
            reverseFundamentalCoefficient step.block
              step.reverseRow step.reverseColumn :: suffix))

/-- The arbitrary-base right-local fold is Haar-equivalent to the external
base followed by the schedule-order coefficient word. -/
theorem finiteProductHaarComplex_contractionProductOver_eq_mul_word
    (blockCount : Nat) (base : ComplexRatPoly)
    (schedule : List OrientedFundamentalContraction) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (contractionProductOver base schedule))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul base
          (complexRatPolyProduct
            (fundamentalContractionCoefficientWord schedule)))) := by
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_mul_one blockCount
        (contractionProductOver base schedule))) ?_
  refine rationalComplexEqv_trans
    (by
      simpa only [complexRatPolyProduct, List.append_nil] using
        (finiteProductHaarComplex_contractionProductOver_mul_product_eq_reverseWord
          blockCount base schedule [])) ?_
  exact finiteProductHaarComplex_mul_product_perm blockCount base
    (fundamentalContractionCoefficientWord_reverse_perm schedule)

/-- **Right-local fold reconciliation.**  The pure distinct-block contraction
product has the same exact finite-product Haar value as the schedule-order
tail-first word of its individual forward/reverse coefficient factors. -/
theorem finiteProductHaarComplex_fundamentalContractionProduct_eq_word
    (blockCount : Nat)
    (schedule : List OrientedFundamentalContraction) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (fundamentalContractionProduct schedule))
      (finiteProductHaarComplex blockCount
        (complexRatPolyProduct
          (fundamentalContractionCoefficientWord schedule))) := by
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_contractionProductOver_eq_mul_word
      blockCount complexRatPolyOne schedule) ?_
  exact finiteProductHaarComplex_one_mul blockCount
    (complexRatPolyProduct
      (fundamentalContractionCoefficientWord schedule))

#print axioms orientedFundamentalContractionCoefficientFactors
#print axioms fundamentalContractionCoefficientWord
#print axioms fundamentalContractionCoefficientWord_reverse_perm
#print axioms finiteProductHaarComplex_contractionProductOver_mul_product_eq_reverseWord
#print axioms finiteProductHaarComplex_contractionProductOver_eq_mul_word
#print axioms finiteProductHaarComplex_fundamentalContractionProduct_eq_word

end YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionReordering
