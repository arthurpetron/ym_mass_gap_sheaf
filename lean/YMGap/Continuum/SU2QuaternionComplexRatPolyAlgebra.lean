/-
# Public algebra for honest complex rational polynomials

The fundamental-matrix leaves use the honest complexification

    ComplexRatPoly = RatPoly x RatPoly

but the elementary algebra needed by a symbolic plaquette trace was
previously scattered across several namespaces.  This leaf exposes a small,
constructive facade:

* canonical zero and one values in the polynomial and rational-complex
  carriers;
* tail-first finite products, intended for one abstract coefficient word;
* the componentwise setoid calculus for rational-complex values;
* exact evaluation laws for zero, one, addition, multiplication, and finite
  products; and
* zero, one, and addition laws for the exact finite-product Haar functional.

The matrix-semantics multiplication is the canonical rational-complex
multiplication in this facade.  The generic-block Schur leaf introduced the
same formula under its own namespace before this public facade existed, so a
componentwise bridge is supplied without changing that verified theorem's
public statement.

## Representation fences

`RatPoly` is a duplicate-preserving raw list carrier.  Consequently this file
does not claim raw associativity, commutativity, normalization, or extensional
Haar congruence.  In particular, pointwise `RatPolyEqv` is not transported
through `finiteProductHaar`, and `finiteProductHaarComplex` is not claimed to
be multiplicative.

`complexRatPolyProduct` must remain opaque on global data.  It is intended for
an abstract factor list or a single four-coefficient plaquette term, not for
unfolding a six-face or twenty-four-corner network.  Later trace-network work
must keep its large sums and products symbolic and use explicit Haar-level
Fubini, association, and reordering theorems.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
import YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur

namespace YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra

open YMGap.Constructive
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion

local infix:50 " ≈ " => Q'.eqv

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Canonical constants and tail-first products -/

/-- The canonical zero in the rational-complex pair carrier. -/
def rationalComplexZero : RationalComplex := (0, 0)

/-- The canonical one in the rational-complex pair carrier. -/
def rationalComplexOne : RationalComplex := (1, 0)

/-- The canonical zero in the honest complex polynomial carrier. -/
def complexRatPolyZero : ComplexRatPoly := (polyZero, polyZero)

/-- The canonical one in the honest complex polynomial carrier. -/
def complexRatPolyOne : ComplexRatPoly := (polyOne, polyZero)

/-- Tail-first product of rational-complex values. -/
def rationalComplexProduct : List RationalComplex → RationalComplex
  | [] => rationalComplexOne
  | value :: values =>
      rationalComplexMul value (rationalComplexProduct values)

/-- Tail-first raw product of honest complex polynomials.  Downstream code
keeps this definition opaque on any nontrivial global network. -/
def complexRatPolyProduct : List ComplexRatPoly → ComplexRatPoly
  | [] => complexRatPolyOne
  | value :: values =>
      complexRatPolyMul value (complexRatPolyProduct values)

/-! ## 2. Public rational-complex setoid calculus -/

/-- Rational-complex equivalence is reflexive. -/
theorem rationalComplexEqv_refl (value : RationalComplex) :
    RationalComplexEqv value value :=
  ⟨Q'.eqv_refl value.1, Q'.eqv_refl value.2⟩

/-- Rational-complex equivalence is symmetric. -/
theorem rationalComplexEqv_symm
    {left right : RationalComplex}
    (h : RationalComplexEqv left right) :
    RationalComplexEqv right left :=
  ⟨Q'.eqv_symm h.1, Q'.eqv_symm h.2⟩

/-- Rational-complex equivalence is transitive. -/
theorem rationalComplexEqv_trans
    {first second third : RationalComplex}
    (hfirst : RationalComplexEqv first second)
    (hsecond : RationalComplexEqv second third) :
    RationalComplexEqv first third :=
  ⟨Q'.eqv_trans _ _ _ hfirst.1 hsecond.1,
    Q'.eqv_trans _ _ _ hfirst.2 hsecond.2⟩

/-- Rational-complex addition respects componentwise equivalence. -/
theorem rationalComplexAdd_congr
    {left left' right right' : RationalComplex}
    (hleft : RationalComplexEqv left left')
    (hright : RationalComplexEqv right right') :
    RationalComplexEqv
      (rationalComplexAdd left right)
      (rationalComplexAdd left' right') :=
  ⟨q_add_congr hleft.1 hright.1,
    q_add_congr hleft.2 hright.2⟩

/-- Rational-complex multiplication respects componentwise equivalence. -/
theorem rationalComplexMul_congr
    {left left' right right' : RationalComplex}
    (hleft : RationalComplexEqv left left')
    (hright : RationalComplexEqv right right') :
    RationalComplexEqv
      (rationalComplexMul left right)
      (rationalComplexMul left' right') :=
  ⟨q_add_congr
      (q_mul_congr hleft.1 hright.1)
      (Q'.neg_eqv_congr _ _ (q_mul_congr hleft.2 hright.2)),
    q_add_congr
      (q_mul_congr hleft.1 hright.2)
      (q_mul_congr hleft.2 hright.1)⟩

/-- Right-factor specialization of rational-complex multiplicative
congruence, used when a local Schur value replaces the right factor of a
spectator product. -/
theorem rationalComplexMul_congr_right
    (left : RationalComplex) {right right' : RationalComplex}
    (hright : RationalComplexEqv right right') :
    RationalComplexEqv
      (rationalComplexMul left right)
      (rationalComplexMul left right') :=
  rationalComplexMul_congr
    (rationalComplexEqv_refl left) hright

/-! ## 3. Evaluation homomorphism -/

private theorem evalRatPoly_negMul
    (rho : Nat → Q') (left right : RatPoly) :
    evalRatPoly rho (polyNeg (polyMul left right)) ≈
      -(evalRatPoly rho left * evalRatPoly rho right) :=
  Q'.eqv_trans _ _ _
    (evalRatPoly_neg rho (polyMul left right))
    (Q'.neg_eqv_congr _ _ (evalRatPoly_mul rho left right))

/-- Evaluation sends the canonical complex polynomial zero to zero. -/
theorem evalComplexRatPoly_zero (rho : Nat → Q') :
    RationalComplexEqv
      (evalComplexRatPoly rho complexRatPolyZero)
      rationalComplexZero := by
  unfold evalComplexRatPoly complexRatPolyZero rationalComplexZero
    RationalComplexEqv
  exact ⟨evalRatPoly_zero rho, evalRatPoly_zero rho⟩

/-- Evaluation sends the canonical complex polynomial one to one. -/
theorem evalComplexRatPoly_one (rho : Nat → Q') :
    RationalComplexEqv
      (evalComplexRatPoly rho complexRatPolyOne)
      rationalComplexOne := by
  unfold evalComplexRatPoly complexRatPolyOne rationalComplexOne
    RationalComplexEqv
  exact
    ⟨YMGap.Continuum.SU2QuaternionWilsonWeightSOS.evalRatPoly_one rho,
      evalRatPoly_zero rho⟩

/-- Evaluation commutes with honest complex polynomial addition. -/
theorem evalComplexRatPoly_add
    (rho : Nat → Q') (left right : ComplexRatPoly) :
    RationalComplexEqv
      (evalComplexRatPoly rho (complexRatPolyAdd left right))
      (rationalComplexAdd
        (evalComplexRatPoly rho left)
        (evalComplexRatPoly rho right)) := by
  unfold evalComplexRatPoly complexRatPolyAdd rationalComplexAdd
    RationalComplexEqv
  exact ⟨evalRatPoly_add rho left.1 right.1,
    evalRatPoly_add rho left.2 right.2⟩

/-- Evaluation commutes with honest complex polynomial multiplication. -/
theorem evalComplexRatPoly_mul
    (rho : Nat → Q') (left right : ComplexRatPoly) :
    RationalComplexEqv
      (evalComplexRatPoly rho (complexRatPolyMul left right))
      (rationalComplexMul
        (evalComplexRatPoly rho left)
        (evalComplexRatPoly rho right)) := by
  unfold evalComplexRatPoly complexRatPolyMul rationalComplexMul
    RationalComplexEqv
  constructor
  · exact Q'.eqv_trans _ _ _
      (evalRatPoly_add rho
        (polyMul left.1 right.1)
        (polyNeg (polyMul left.2 right.2)))
      (q_add_congr
        (evalRatPoly_mul rho left.1 right.1)
        (evalRatPoly_negMul rho left.2 right.2))
  · exact Q'.eqv_trans _ _ _
      (evalRatPoly_add rho
        (polyMul left.1 right.2)
        (polyMul left.2 right.1))
      (q_add_congr
        (evalRatPoly_mul rho left.1 right.2)
        (evalRatPoly_mul rho left.2 right.1))

/-- Evaluation of a tail-first complex polynomial product is the matching
tail-first product of the evaluated factors. -/
theorem evalComplexRatPoly_product (rho : Nat → Q') :
    ∀ factors : List ComplexRatPoly,
      RationalComplexEqv
        (evalComplexRatPoly rho (complexRatPolyProduct factors))
        (rationalComplexProduct
          (factors.map (evalComplexRatPoly rho)))
  | [] => by
      simpa only [complexRatPolyProduct, List.map,
        rationalComplexProduct] using evalComplexRatPoly_one rho
  | factor :: factors => by
      change
        RationalComplexEqv
          (evalComplexRatPoly rho
            (complexRatPolyMul factor
              (complexRatPolyProduct factors)))
          (rationalComplexMul
            (evalComplexRatPoly rho factor)
            (rationalComplexProduct
              (factors.map (evalComplexRatPoly rho))))
      exact rationalComplexEqv_trans
        (evalComplexRatPoly_mul rho factor
          (complexRatPolyProduct factors))
        (rationalComplexMul_congr_right
          (evalComplexRatPoly rho factor)
          (evalComplexRatPoly_product rho factors))

/-! ## 4. Componentwise finite-product Haar linearity -/

/-- Finite-product Haar sends the canonical complex polynomial zero to zero. -/
theorem finiteProductHaarComplex_zero (blockCount : Nat) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount complexRatPolyZero)
      rationalComplexZero := by
  unfold finiteProductHaarComplex complexRatPolyZero rationalComplexZero
    RationalComplexEqv
  exact ⟨finiteProductHaar_zero blockCount,
    finiteProductHaar_zero blockCount⟩

/-- Finite-product Haar sends the canonical complex polynomial one to one. -/
theorem finiteProductHaarComplex_one (blockCount : Nat) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount complexRatPolyOne)
      rationalComplexOne := by
  unfold finiteProductHaarComplex complexRatPolyOne rationalComplexOne
    RationalComplexEqv
  exact ⟨finiteProductHaar_one blockCount,
    finiteProductHaar_zero blockCount⟩

/-- Finite-product Haar is additive on the honest complex polynomial
carrier, componentwise in the rational-complex setoid. -/
theorem finiteProductHaarComplex_add
    (blockCount : Nat) (left right : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyAdd left right))
      (rationalComplexAdd
        (finiteProductHaarComplex blockCount left)
        (finiteProductHaarComplex blockCount right)) := by
  unfold finiteProductHaarComplex complexRatPolyAdd rationalComplexAdd
    RationalComplexEqv
  exact ⟨finiteProductHaar_add blockCount left.1 right.1,
    finiteProductHaar_add blockCount left.2 right.2⟩

/-! ## 5. Compatibility with the generic-block Schur value -/

/-- The duplicate rational-complex multiplication introduced by the
generic-block Schur leaf agrees componentwise with the matrix-semantics
multiplication chosen as canonical by this facade. -/
theorem generic_rationalComplexMul_eqv
    (left right : RationalComplex) :
    RationalComplexEqv
      (YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        left right)
      (YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics.rationalComplexMul
        left right) := by
  unfold
    YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
    YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics.rationalComplexMul
    RationalComplexEqv
  exact ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩

#print axioms rationalComplexMul_congr
#print axioms rationalComplexMul_congr_right
#print axioms evalComplexRatPoly_mul
#print axioms evalComplexRatPoly_product
#print axioms finiteProductHaarComplex_add
#print axioms generic_rationalComplexMul_eqv

end YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
