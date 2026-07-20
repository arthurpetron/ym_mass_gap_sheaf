/-
# Contextual Boolean Fubini for finite-product quaternion Haar

The symbolic Boolean-sum carrier keeps a trace-index family opaque rather
than materializing its complete assignment space.  In a product of trace
factors, however, such a sum can occur between an already accumulated
complex-polynomial spectator and an unresolved right suffix.  Bare Haar
linearity is not enough to move a pointwise equivalence through those raw
multiplications.

This leaf supplies the required contextual form.  The one-binder theorem is
an exact specialization of the established inner distributivity law.  The
recursive theorem then lifts it structurally through an arbitrary Boolean
depth while retaining both the spectator and suffix at every branch.

The recursion is a symbolic theorem in `depth`.  In particular, this file
does not specialize, unfold, simplify, reduce, print, or evaluate the
depth-twenty-four elementary-cube sum.  It asserts no raw-polynomial
distributivity, no Haar multiplicativity, and no extensional Haar
congruence.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
import YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexBoolFubini

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra

private theorem neg_num_cast (value : Q') :
    (-value).num = -(value.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add,
               Int.add_zero];
             ac_rfl))

/-! ## 1. Binary and contextual complex bilinearity -/

/-- The scalar four-term expansion of one complex product after applying the
finite-product Haar functional. -/
private def finiteHaarComplexMulValue
    (blockCount : Nat) (left right : ComplexRatPoly) : RationalComplex :=
  (finiteProductHaar blockCount (polyMul left.1 right.1) +
      -(finiteProductHaar blockCount (polyMul left.2 right.2)),
    finiteProductHaar blockCount (polyMul left.1 right.2) +
      finiteProductHaar blockCount (polyMul left.2 right.1))

/-- Expanding one honest complex product requires only scalar Haar additivity
and compatibility with negation. -/
private theorem finiteProductHaarComplex_mul_expansion
    (blockCount : Nat) (left right : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul left right))
      (finiteHaarComplexMulValue blockCount left right) := by
  unfold finiteProductHaarComplex complexRatPolyMul
    finiteHaarComplexMulValue RationalComplexEqv
  constructor
  · exact Q'.eqv_trans _ _ _
      (finiteProductHaar_add blockCount _ _)
      (QPoly.q_add_congr (Q'.eqv_refl _)
        (finiteProductHaar_neg blockCount _))
  · exact finiteProductHaar_add blockCount _ _

/-- The scalar expansion of a complex product is additive in its right
complex factor. -/
private theorem finiteHaarComplexMulValue_add_right
    (blockCount : Nat)
    (source left right : ComplexRatPoly) :
    RationalComplexEqv
      (finiteHaarComplexMulValue blockCount source
        (complexRatPolyAdd left right))
      (rationalComplexAdd
        (finiteHaarComplexMulValue blockCount source left)
        (finiteHaarComplexMulValue blockCount source right)) := by
  unfold finiteHaarComplexMulValue complexRatPolyAdd
    rationalComplexAdd RationalComplexEqv
  constructor
  · refine Q'.eqv_trans _
      ((finiteProductHaar blockCount
            (polyMul source.1 left.1) +
          finiteProductHaar blockCount
            (polyMul source.1 right.1)) +
        -(finiteProductHaar blockCount
            (polyMul source.2 left.2) +
          finiteProductHaar blockCount
            (polyMul source.2 right.2))) _ ?_ ?_
    · exact QPoly.q_add_congr
        (finiteProductHaar_polyMul_add_right
          blockCount source.1 left.1 right.1)
        (Q'.neg_eqv_congr _ _
          (finiteProductHaar_polyMul_add_right
            blockCount source.2 left.2 right.2))
    · ring_qeqv
  · refine Q'.eqv_trans _
      ((finiteProductHaar blockCount
            (polyMul source.1 left.2) +
          finiteProductHaar blockCount
            (polyMul source.1 right.2)) +
        (finiteProductHaar blockCount
            (polyMul source.2 left.1) +
          finiteProductHaar blockCount
            (polyMul source.2 right.1))) _ ?_ ?_
    · exact QPoly.q_add_congr
        (finiteProductHaar_polyMul_add_right
          blockCount source.1 left.2 right.2)
        (finiteProductHaar_polyMul_add_right
          blockCount source.2 left.1 right.1)
    · ring_qeqv

/-- Honest complex multiplication distributes over addition in its right
factor after finite-product Haar evaluation. This is a functional-level
bilinearity theorem, not a raw-polynomial quotient law. -/
theorem finiteProductHaarComplex_mul_add_right
    (blockCount : Nat)
    (source left right : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul source
          (complexRatPolyAdd left right)))
      (rationalComplexAdd
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul source left))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul source right))) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_expansion
      blockCount source (complexRatPolyAdd left right))
    (rationalComplexEqv_trans
      (finiteHaarComplexMulValue_add_right
        blockCount source left right)
      (rationalComplexEqv_symm
        (rationalComplexAdd_congr
          (finiteProductHaarComplex_mul_expansion
            blockCount source left)
          (finiteProductHaarComplex_mul_expansion
            blockCount source right))))

/-- Distribute a complex sum occurring between an arbitrary accumulated
spectator and an arbitrary right suffix. Reordering the suffix next to the
spectator reduces the result to binary right-distributivity, after which the
two branches are restored to their original order. -/
theorem finiteProductHaarComplex_mul_add_inner
    (blockCount : Nat)
    (spectator left right suffix : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyAdd left right) suffix)))
      (rationalComplexAdd
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul left suffix)))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul right suffix)))) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_middle_comm
      blockCount spectator (complexRatPolyAdd left right) suffix)
    (rationalComplexEqv_trans
      (rationalComplexEqv_symm
        (finiteProductHaarComplex_mul_assoc
          blockCount spectator suffix (complexRatPolyAdd left right)))
      (rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_add_right blockCount
          (complexRatPolyMul spectator suffix) left right)
        (rationalComplexAdd_congr
          (rationalComplexEqv_trans
            (finiteProductHaarComplex_mul_assoc
              blockCount spectator suffix left)
            (finiteProductHaarComplex_mul_middle_comm
              blockCount spectator suffix left))
          (rationalComplexEqv_trans
            (finiteProductHaarComplex_mul_assoc
              blockCount spectator suffix right)
            (finiteProductHaarComplex_mul_middle_comm
              blockCount spectator suffix right)))))

/-! ## 2. One contextual Boolean binder -/

/-- Distribute one symbolic Boolean binder while retaining an arbitrary
accumulated spectator on the left and an arbitrary unresolved suffix on the
right.  This is a Haar-level theorem only; it does not identify the two raw
complex-polynomial representatives. -/
theorem finiteProductHaarComplex_mul_boolBind_inner
    (blockCount : Nat)
    (spectator : ComplexRatPoly)
    (family : Bool → ComplexRatPoly)
    (suffix : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyBoolBind family) suffix)))
      (rationalComplexBoolBind (fun index =>
        finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul (family index) suffix)))) := by
  unfold complexRatPolyBoolBind rationalComplexBoolBind
  exact finiteProductHaarComplex_mul_add_inner
    blockCount spectator (family false) (family true) suffix

/-! ## 3. Structural contextual Boolean sum -/

/-- **Contextual finite-product-Haar Boolean Fubini.**  A symbolic Boolean
sum occurring between an arbitrary spectator and suffix may be moved through
the exact finite-product Haar functional, pointwise in the still-opaque
assignment family.

The proof recurses only on the supplied depth.  Each successor step exposes
one Boolean binder, applies `finiteProductHaarComplex_mul_boolBind_inner`, and
combines the two recursive branches by rational-complex additive
congruence. -/
theorem finiteProductHaarComplex_mul_boolSum_inner
    (blockCount : Nat)
    (spectator suffix : ComplexRatPoly) :
    ∀ (depth : Nat) (family : List Bool → ComplexRatPoly),
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul
              (complexRatPolyBoolSum depth family) suffix)))
        (rationalComplexBoolSum depth (fun assignment =>
          finiteProductHaarComplex blockCount
            (complexRatPolyMul spectator
              (complexRatPolyMul (family assignment) suffix))))
  | 0, family =>
      rationalComplexEqv_refl
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul (family []) suffix)))
  | depth + 1, family => by
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_boolBind_inner
          blockCount spectator (fun index =>
            complexRatPolyBoolSum depth (fun assignment =>
              family (index :: assignment))) suffix) ?_
      exact rationalComplexAdd_congr
        (finiteProductHaarComplex_mul_boolSum_inner
          blockCount spectator suffix depth
          (fun assignment => family (false :: assignment)))
        (finiteProductHaarComplex_mul_boolSum_inner
          blockCount spectator suffix depth
          (fun assignment => family (true :: assignment)))

#print axioms finiteProductHaarComplex_mul_add_right
#print axioms finiteProductHaarComplex_mul_add_inner
#print axioms finiteProductHaarComplex_mul_boolBind_inner
#print axioms finiteProductHaarComplex_mul_boolSum_inner

end YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexBoolFubini
