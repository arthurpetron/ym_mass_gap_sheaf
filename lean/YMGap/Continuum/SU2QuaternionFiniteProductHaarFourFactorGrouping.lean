/-
# Four-factor row grouping under finite-product quaternion Haar

A plaquette trace summand is a left-associated product of four honest
complex coefficient polynomials.  A face-major contraction word instead
keeps all coefficient factors in one tail-first list.  These expressions are
not definitionally equal for the deliberately syntax-sensitive raw
polynomial carrier.

This leaf proves the required reconciliation after finite-product Haar.  The
induction retains both an accumulated prefix and an arbitrary suffix, so no
bare Haar equivalence is ever transported through multiplication.  Rows and
their factors remain completely symbolic; no cube-sized word or Boolean
assignment family is materialized here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
import YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarFourFactorGrouping

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion

/-! ## 1. Symbolic four-factor rows -/

/-- The left-associated polynomial carried by one symbolic four-factor row. -/
def complexRatPolyFourFactorRowPolynomial {Row : Type}
    (first second third fourth : Row → ComplexRatPoly)
    (row : Row) : ComplexRatPoly :=
  complexRatPolyMulFourLeft
    (first row) (second row) (third row) (fourth row)

/-- The same row as its schedule-order list of four individual factors. -/
def complexRatPolyFourFactorRowFactors {Row : Type}
    (first second third fourth : Row → ComplexRatPoly)
    (row : Row) : List ComplexRatPoly :=
  [first row, second row, third row, fourth row]

/-! ## 2. Prefix/suffix-strengthened grouping -/

/-- Accumulating one left-associated four-factor row into an existing prefix
has the same Haar value as accumulating its four factors one at a time, with
an arbitrary right suffix retained.

Both sides are sent to
`(prefix * first) * (second * (third * (fourth * suffix)))`.  The three
four-factor reassociations on the left are precisely what makes this valid
without an illicit contextual congruence. -/
private theorem finiteProductHaarComplex_mul_mulFourLeft_mul_eq_fourAccum_mul
    (blockCount : Nat)
    (spectator first second third fourth suffix : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul
          (complexRatPolyMul spectator
            (complexRatPolyMulFourLeft first second third fourth))
          suffix))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul
          (complexRatPolyMul
            (complexRatPolyMul
              (complexRatPolyMul
                (complexRatPolyMul spectator first) second) third) fourth)
          suffix)) := by
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_four_assoc blockCount
      spectator
      (complexRatPolyMul (complexRatPolyMul first second) third)
      fourth suffix) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_four_assoc blockCount
      spectator (complexRatPolyMul first second) third
      (complexRatPolyMul fourth suffix)) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_four_assoc blockCount
      spectator first second
      (complexRatPolyMul third
        (complexRatPolyMul fourth suffix))) ?_
  apply rationalComplexEqv_symm
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc blockCount
      (complexRatPolyMul
        (complexRatPolyMul (complexRatPolyMul spectator first) second) third)
      fourth suffix) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc blockCount
      (complexRatPolyMul (complexRatPolyMul spectator first) second)
      third (complexRatPolyMul fourth suffix)) ?_
  exact finiteProductHaarComplex_mul_assoc blockCount
    (complexRatPolyMul spectator first) second
    (complexRatPolyMul third (complexRatPolyMul fourth suffix))

/-- **Structural four-row grouping theorem.**  Beneath an arbitrary prefix
and with an arbitrary symbolic suffix, replacing every left-associated
four-factor row by its four individual factors preserves finite-product Haar.

The accumulated prefix is the induction invariant.  It makes the recursive
call directly applicable after the head row has been exposed, without using
the false principle that equality of bare Haar values is a multiplication
congruence. -/
theorem finiteProductHaarComplex_mul_fourFactorRowProducts_eq_flatMap
    {Row : Type}
    (blockCount : Nat)
    (first second third fourth : Row → ComplexRatPoly) :
    ∀ (spectator : ComplexRatPoly) (rows : List Row)
      (suffix : List ComplexRatPoly),
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct
              (rows.map
                  (complexRatPolyFourFactorRowPolynomial
                    first second third fourth) ++
                suffix))))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct
              (rows.flatMap
                  (complexRatPolyFourFactorRowFactors
                    first second third fourth) ++
                suffix))))
  | spectator, [], suffix =>
      rationalComplexEqv_refl
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct suffix)))
  | spectator, row :: rows, suffix => by
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_assoc_context blockCount
          spectator
          (complexRatPolyFourFactorRowPolynomial
            first second third fourth row)
          (complexRatPolyProduct
            (rows.map
                (complexRatPolyFourFactorRowPolynomial
                  first second third fourth) ++
              suffix))) ?_
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_mulFourLeft_mul_eq_fourAccum_mul
          blockCount spectator
          (first row) (second row) (third row) (fourth row)
          (complexRatPolyProduct
            (rows.map
                (complexRatPolyFourFactorRowPolynomial
                  first second third fourth) ++
              suffix))) ?_
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_fourFactorRowProducts_eq_flatMap
          blockCount first second third fourth
          (complexRatPolyMul
            (complexRatPolyMul
              (complexRatPolyMul
                (complexRatPolyMul spectator (first row))
                (second row))
              (third row))
            (fourth row))
          rows suffix) ?_
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_assoc blockCount
          (complexRatPolyMul
            (complexRatPolyMul
              (complexRatPolyMul spectator (first row)) (second row))
            (third row))
          (fourth row)
          (complexRatPolyProduct
            (rows.flatMap
                (complexRatPolyFourFactorRowFactors
                  first second third fourth) ++
              suffix))) ?_
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_assoc blockCount
          (complexRatPolyMul
            (complexRatPolyMul spectator (first row)) (second row))
          (third row)
          (complexRatPolyMul (fourth row)
            (complexRatPolyProduct
              (rows.flatMap
                  (complexRatPolyFourFactorRowFactors
                    first second third fourth) ++
                suffix)))) ?_
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_assoc blockCount
          (complexRatPolyMul spectator (first row))
          (second row)
          (complexRatPolyMul (third row)
            (complexRatPolyMul (fourth row)
              (complexRatPolyProduct
                (rows.flatMap
                    (complexRatPolyFourFactorRowFactors
                      first second third fourth) ++
                  suffix))))) ?_
      simpa only [complexRatPolyFourFactorRowPolynomial,
        complexRatPolyFourFactorRowFactors, complexRatPolyMulFourLeft,
        List.map_cons, List.flatMap_cons, List.cons_append,
        complexRatPolyProduct] using
        (finiteProductHaarComplex_mul_assoc blockCount
          spectator (first row)
          (complexRatPolyMul (second row)
            (complexRatPolyMul (third row)
              (complexRatPolyMul (fourth row)
                (complexRatPolyProduct
                  (rows.flatMap
                      (complexRatPolyFourFactorRowFactors
                        first second third fourth) ++
                    suffix))))))

/-! ## 3. Bare grouped-to-flat endpoint -/

/-- A tail-first product of left-associated four-factor rows has the same
finite-product Haar value as the tail-first product of their flattened factor
word. -/
theorem finiteProductHaarComplex_fourFactorRowProducts_eq_flatMap
    {Row : Type}
    (blockCount : Nat)
    (first second third fourth : Row → ComplexRatPoly)
    (rows : List Row) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyProduct
          (rows.map
            (complexRatPolyFourFactorRowPolynomial
              first second third fourth))))
      (finiteProductHaarComplex blockCount
        (complexRatPolyProduct
          (rows.flatMap
            (complexRatPolyFourFactorRowFactors
              first second third fourth)))) := by
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_one_mul blockCount
        (complexRatPolyProduct
          (rows.map
            (complexRatPolyFourFactorRowPolynomial
              first second third fourth))))) ?_
  refine rationalComplexEqv_trans
    (by
      simpa only [List.append_nil] using
        (finiteProductHaarComplex_mul_fourFactorRowProducts_eq_flatMap
          blockCount first second third fourth
          complexRatPolyOne rows [])) ?_
  exact finiteProductHaarComplex_one_mul blockCount
    (complexRatPolyProduct
      (rows.flatMap
        (complexRatPolyFourFactorRowFactors
          first second third fourth)))

#print axioms complexRatPolyFourFactorRowPolynomial
#print axioms complexRatPolyFourFactorRowFactors
#print axioms finiteProductHaarComplex_mul_fourFactorRowProducts_eq_flatMap
#print axioms finiteProductHaarComplex_fourFactorRowProducts_eq_flatMap

end YMGap.Continuum.SU2QuaternionFiniteProductHaarFourFactorGrouping
