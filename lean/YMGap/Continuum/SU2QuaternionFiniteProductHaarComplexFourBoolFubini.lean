/-
# Contextual four-binder Fubini for finite-product quaternion Haar

One plaquette trace expansion contains exactly four nested Boolean binders.
This leaf packages four applications of the established one-binder
contextual Haar theorem into the precise bounded interface needed by the
six-face elementary-cube bridge.

Only the safe depth-four syntax is exposed.  Arbitrary accumulated and
unresolved polynomial factors remain inside every Haar branch, and no raw
polynomial associativity, distributivity, or Haar multiplicativity is
asserted.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexBoolFubini
import YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexBoolFubini
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion

/-! ## 1. Opening exactly four leading positional binders -/

/-- A positional sum with four additional leading coordinates is literally
four bounded Boolean binders followed by the still-opaque suffix sum.  This
identity may be specialized at a large suffix depth: only the four leading
constructors are exposed. -/
theorem rationalComplexBoolSum_add_four
    (depth : Nat) (family : List Bool → RationalComplex) :
    rationalComplexBoolSum (depth + 4) family =
      rationalComplexFourBoolSum (fun first second third fourth =>
        rationalComplexBoolSum depth (fun suffix =>
          family (first :: second :: third :: fourth :: suffix))) := by
  rfl

/-! ## 2. Contextual four-binder Haar Fubini -/

/-- Move one four-index symbolic trace expansion through finite-product Haar
while retaining an arbitrary accumulated spectator and unresolved suffix. -/
theorem finiteProductHaarComplex_mul_fourBoolSum_inner
    (blockCount : Nat)
    (spectator suffix : ComplexRatPoly)
    (family : Bool → Bool → Bool → Bool → ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyFourBoolSum family) suffix)))
      (rationalComplexFourBoolSum (fun first second third fourth =>
        finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul
              (family first second third fourth) suffix)))) := by
  unfold complexRatPolyFourBoolSum rationalComplexFourBoolSum
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_boolBind_inner
      blockCount spectator (fun first =>
        complexRatPolyBoolBind (fun second =>
          complexRatPolyBoolBind (fun third =>
            complexRatPolyBoolBind (fun fourth =>
              family first second third fourth)))) suffix) ?_
  exact rationalComplexBoolBind_congr (fun first => by
    refine rationalComplexEqv_trans
      (finiteProductHaarComplex_mul_boolBind_inner
        blockCount spectator (fun second =>
          complexRatPolyBoolBind (fun third =>
            complexRatPolyBoolBind (fun fourth =>
              family first second third fourth))) suffix) ?_
    exact rationalComplexBoolBind_congr (fun second => by
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_boolBind_inner
          blockCount spectator (fun third =>
            complexRatPolyBoolBind (fun fourth =>
              family first second third fourth)) suffix) ?_
      exact rationalComplexBoolBind_congr (fun third =>
        finiteProductHaarComplex_mul_boolBind_inner
          blockCount spectator
          (fun fourth => family first second third fourth) suffix)))

/-! ## 3. Order-preserving accumulated products -/

/-- A left-associated accumulated factor word followed by a tail-first
suffix has the same Haar value as the single tail-first concatenated word
beneath the original spectator.  No factors are exchanged.  Retaining the
suffix as a list makes the empty-factor base definitionally reflexive. -/
theorem finiteProductHaarComplex_foldl_mul_product_eq_mul_append_product
    (blockCount : Nat) :
    ∀ (spectator : ComplexRatPoly)
      (factors suffix : List ComplexRatPoly),
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul
            (factors.foldl complexRatPolyMul spectator)
            (complexRatPolyProduct suffix)))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct (factors ++ suffix))))
  | spectator, [], suffix => by
      simpa only [List.foldl_nil, List.nil_append] using
        (rationalComplexEqv_refl
          (finiteProductHaarComplex blockCount
            (complexRatPolyMul spectator
              (complexRatPolyProduct suffix))))
  | spectator, factor :: factors, suffix => by
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_foldl_mul_product_eq_mul_append_product
          blockCount (complexRatPolyMul spectator factor)
          factors suffix) ?_
      simpa only [List.cons_append, complexRatPolyProduct] using
        (finiteProductHaarComplex_mul_assoc blockCount
          spectator factor
          (complexRatPolyProduct (factors ++ suffix)))

/-- Remove the trailing polynomial one from the accumulated form and obtain
the corresponding tail-first word beneath an arbitrary spectator. -/
theorem finiteProductHaarComplex_foldl_eq_mul_product
    (blockCount : Nat) (spectator : ComplexRatPoly)
    (factors : List ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (factors.foldl complexRatPolyMul spectator))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyProduct factors))) := by
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_mul_one blockCount
        (factors.foldl complexRatPolyMul spectator))) ?_
  simpa only [complexRatPolyProduct, List.append_nil] using
    (finiteProductHaarComplex_foldl_mul_product_eq_mul_append_product
      blockCount spectator factors [])

/-- Endpoint used after all six outward face terms have been selected. -/
theorem finiteProductHaarComplex_foldl_one_eq_product
    (blockCount : Nat) (factors : List ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (factors.foldl complexRatPolyMul complexRatPolyOne))
      (finiteProductHaarComplex blockCount
        (complexRatPolyProduct factors)) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_foldl_eq_mul_product
      blockCount complexRatPolyOne factors)
    (finiteProductHaarComplex_one_mul blockCount
      (complexRatPolyProduct factors))

#print axioms rationalComplexBoolSum_add_four
#print axioms finiteProductHaarComplex_mul_fourBoolSum_inner
#print axioms finiteProductHaarComplex_foldl_mul_product_eq_mul_append_product
#print axioms finiteProductHaarComplex_foldl_eq_mul_product
#print axioms finiteProductHaarComplex_foldl_one_eq_product

end YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini
