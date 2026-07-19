/-
# Complex reordering laws for the finite-product quaternion Haar functional

The real raw-polynomial Haar carrier already proves commutativity,
last-two-factor exchange, associativity, and genuine four-factor exchange at
the level of the exact finite-product functional.  This leaf supplies the
corresponding constructive facade for the honest complex carrier
`ComplexRatPoly = RatPoly × RatPoly`, culminating in arbitrary symbolic
factor reordering from an explicit `List.Perm` witness.

The carrier is deliberately syntax-sensitive: no pointwise polynomial
equivalence is transported through Haar, and no raw associativity or
commutativity is asserted.  Every result is stated only after applying
`finiteProductHaarComplex` and remains in `RationalComplexEqv`.

No global factor list or Boolean assignment family is materialized here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
import YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarMultihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra

local infix:50 " ≈ " => Q'.eqv

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

/-! ## 1. Scalar linear-congruence helpers -/

/-- Addition of raw real polynomials respects any two already established
finite-product Haar equivalences.  This is a congruence only after Haar; it
does not assert a raw-polynomial quotient law. -/
theorem finiteProductHaar_polyAdd_congr
    (blockCount : Nat) {left left' right right' : RatPoly}
    (hleft : finiteProductHaar blockCount left ≈
      finiteProductHaar blockCount left')
    (hright : finiteProductHaar blockCount right ≈
      finiteProductHaar blockCount right') :
    finiteProductHaar blockCount (polyAdd left right) ≈
      finiteProductHaar blockCount (polyAdd left' right') :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_add blockCount left right)
    (Q'.eqv_trans _ _ _
      (QPoly.q_add_congr hleft hright)
      (Q'.eqv_symm
        (finiteProductHaar_add blockCount left' right')))

/-- Negation of a raw real polynomial respects an established Haar
equivalence, again only at the functional level. -/
theorem finiteProductHaar_polyNeg_congr
    (blockCount : Nat) {source target : RatPoly}
    (h : finiteProductHaar blockCount source ≈
      finiteProductHaar blockCount target) :
    finiteProductHaar blockCount (polyNeg source) ≈
      finiteProductHaar blockCount (polyNeg target) :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_neg blockCount source)
    (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ h)
      (Q'.eqv_symm (finiteProductHaar_neg blockCount target)))

/-- Raw polynomial addition may be exchanged after finite-product Haar. -/
theorem finiteProductHaar_polyAdd_comm
    (blockCount : Nat) (left right : RatPoly) :
    finiteProductHaar blockCount (polyAdd left right) ≈
      finiteProductHaar blockCount (polyAdd right left) :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_add blockCount left right)
    (Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv
        (finiteProductHaar blockCount left)
        (finiteProductHaar blockCount right))
      (Q'.eqv_symm
        (finiteProductHaar_add blockCount right left)))

/-- Appending the raw polynomial zero does not change finite-product Haar. -/
theorem finiteProductHaar_polyAdd_zero_right
    (blockCount : Nat) (polynomial : RatPoly) :
    finiteProductHaar blockCount (polyAdd polynomial polyZero) ≈
      finiteProductHaar blockCount polynomial :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_add blockCount polynomial polyZero)
    (Q'.eqv_trans _ _ _
      (QPoly.q_add_congr
        (Q'.eqv_refl _)
        (finiteProductHaar_zero blockCount))
      (QPoly.q_add_zero_eqv _))

/-- The raw zero polynomial is a left multiplicative zero after Haar. -/
theorem finiteProductHaar_polyZero_mul
    (blockCount : Nat) (polynomial : RatPoly) :
    finiteProductHaar blockCount (polyMul polyZero polynomial) ≈
      finiteProductHaar blockCount polyZero := by
  exact Q'.eqv_refl _

/-- The raw zero polynomial is a right multiplicative zero after Haar. -/
theorem finiteProductHaar_mul_polyZero
    (blockCount : Nat) (polynomial : RatPoly) :
    finiteProductHaar blockCount (polyMul polynomial polyZero) ≈
      finiteProductHaar blockCount polyZero :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_polyMul_comm
      blockCount polynomial polyZero)
    (finiteProductHaar_polyZero_mul blockCount polynomial)

/-- The canonical raw polynomial one is a left unit after finite-product
Haar.  The proof is structural in the raw term list and uses rational
setoid congruence for the otherwise unnormalized coefficient `1 * c`. -/
theorem finiteProductHaar_polyOne_mul
    (blockCount : Nat) : ∀ polynomial : RatPoly,
    finiteProductHaar blockCount (polyMul polyOne polynomial) ≈
      finiteProductHaar blockCount polynomial
  | [] => Q'.eqv_refl 0
  | term :: polynomial => by
      change
        ((1 : Q') * term.2) *
              finiteProductHaarMono blockCount term.1 +
            finiteProductHaar blockCount
              (polyMul polyOne polynomial) ≈
          term.2 * finiteProductHaarMono blockCount term.1 +
            finiteProductHaar blockCount polynomial
      exact QPoly.q_add_congr
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.one_mul_eqv term.2))
        (finiteProductHaar_polyOne_mul blockCount polynomial)

/-- The canonical raw polynomial one is a right unit after finite-product
Haar. -/
theorem finiteProductHaar_mul_polyOne
    (blockCount : Nat) (polynomial : RatPoly) :
    finiteProductHaar blockCount (polyMul polynomial polyOne) ≈
      finiteProductHaar blockCount polynomial :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_polyMul_comm
      blockCount polynomial polyOne)
    (finiteProductHaar_polyOne_mul blockCount polynomial)

/-! ## 2. Scalar bilinearity beneath a product -/

/-- Finite-product Haar distributes over a raw sum in the left polynomial
factor. -/
theorem finiteProductHaar_polyMul_add_left
    (blockCount : Nat) (left right target : RatPoly) :
    finiteProductHaar blockCount
        (polyMul (polyAdd left right) target) ≈
      finiteProductHaar blockCount (polyMul left target) +
        finiteProductHaar blockCount (polyMul right target) := by
  have hmul :
      polyMul (polyAdd left right) target =
        polyAdd (polyMul left target) (polyMul right target) := by
    simp [polyAdd, polyMul]
  rw [hmul]
  exact finiteProductHaar_add blockCount _ _

/-- Finite-product Haar distributes over a raw sum in the right polynomial
factor. -/
theorem finiteProductHaar_polyMul_add_right
    (blockCount : Nat) (source left right : RatPoly) :
    finiteProductHaar blockCount
        (polyMul source (polyAdd left right)) ≈
      finiteProductHaar blockCount (polyMul source left) +
        finiteProductHaar blockCount (polyMul source right) :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_polyMul_comm
      blockCount source (polyAdd left right))
    (Q'.eqv_trans _ _ _
      (finiteProductHaar_polyMul_add_left
        blockCount left right source)
      (QPoly.q_add_congr
        (finiteProductHaar_polyMul_comm blockCount left source)
        (finiteProductHaar_polyMul_comm blockCount right source)))

private theorem finiteHaarRow_neg_left
    (blockCount : Nat) (left : RatTerm) : ∀ right : RatPoly,
    finiteHaarRow blockCount (left.1, -left.2) right ≈
      -(finiteHaarRow blockCount left right)
  | [] => by
      change (0 : Q') ≈ 0
      exact Q'.eqv_refl 0
  | right :: polynomial => by
      change
        ((-left.2) * right.2) *
              finiteProductHaarMono blockCount
                (monoMul left.1 right.1) +
            finiteHaarRow blockCount (left.1, -left.2) polynomial ≈
          -((left.2 * right.2) *
                finiteProductHaarMono blockCount
                  (monoMul left.1 right.1) +
              finiteHaarRow blockCount left polynomial)
      refine Q'.eqv_trans _
        (-((left.2 * right.2) *
              finiteProductHaarMono blockCount
                (monoMul left.1 right.1)) +
          -(finiteHaarRow blockCount left polynomial)) _ ?_ ?_
      · exact QPoly.q_add_congr
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.neg_mul_eqv left.2 right.2))
            (Q'.neg_mul_eqv (left.2 * right.2)
              (finiteProductHaarMono blockCount
                (monoMul left.1 right.1))))
          (finiteHaarRow_neg_left blockCount left polynomial)
      · exact Q'.eqv_symm
          (Q'.neg_add_eqv_split
            ((left.2 * right.2) *
              finiteProductHaarMono blockCount
                (monoMul left.1 right.1))
            (finiteHaarRow blockCount left polynomial))

private theorem finiteHaarBilinear_neg_left
    (blockCount : Nat) : ∀ left right : RatPoly,
    finiteHaarBilinear blockCount (polyNeg left) right ≈
      -(finiteHaarBilinear blockCount left right)
  | [], _ => by
      change (0 : Q') ≈ 0
      exact Q'.eqv_refl 0
  | left :: polynomial, right => by
      change
        finiteHaarRow blockCount (left.1, -left.2) right +
            finiteHaarBilinear blockCount (polyNeg polynomial) right ≈
          -(finiteHaarRow blockCount left right +
            finiteHaarBilinear blockCount polynomial right)
      refine Q'.eqv_trans _
        (-(finiteHaarRow blockCount left right) +
          -(finiteHaarBilinear blockCount polynomial right)) _ ?_ ?_
      · exact QPoly.q_add_congr
          (finiteHaarRow_neg_left blockCount left right)
          (finiteHaarBilinear_neg_left
            blockCount polynomial right)
      · exact Q'.eqv_symm
          (Q'.neg_add_eqv_split
            (finiteHaarRow blockCount left right)
            (finiteHaarBilinear blockCount polynomial right))

/-- A negated left polynomial factor pulls out as scalar negation after
finite-product Haar. -/
theorem finiteProductHaar_polyMul_neg_left
    (blockCount : Nat) (source target : RatPoly) :
    finiteProductHaar blockCount
        (polyMul (polyNeg source) target) ≈
      -(finiteProductHaar blockCount (polyMul source target)) :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_polyMul_eq_bilinear
      blockCount (polyNeg source) target)
    (Q'.eqv_trans _ _ _
      (finiteHaarBilinear_neg_left blockCount source target)
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_symm
          (finiteProductHaar_polyMul_eq_bilinear
            blockCount source target))))

/-- A negated right polynomial factor pulls out as scalar negation after
finite-product Haar. -/
theorem finiteProductHaar_polyMul_neg_right
    (blockCount : Nat) (source target : RatPoly) :
    finiteProductHaar blockCount
        (polyMul source (polyNeg target)) ≈
      -(finiteProductHaar blockCount (polyMul source target)) :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_polyMul_comm
      blockCount source (polyNeg target))
    (Q'.eqv_trans _ _ _
      (finiteProductHaar_polyMul_neg_left
        blockCount target source)
      (Q'.neg_eqv_congr _ _
        (finiteProductHaar_polyMul_comm
          blockCount target source)))

/-! ## 3. Canonical complex triple expansion -/

private def finiteHaarTripleValue
    (blockCount : Nat) (first middle target : RatPoly) : Q' :=
  finiteProductHaar blockCount
    (polyMul first (polyMul middle target))

/-- The common four-term real/imaginary expansion of a complex triple. -/
private def finiteHaarComplexTripleValue
    (blockCount : Nat)
    (first middle target : ComplexRatPoly) : RationalComplex :=
  (((finiteHaarTripleValue blockCount first.1 middle.1 target.1 +
        -(finiteHaarTripleValue blockCount first.1 middle.2 target.2)) +
      (-(finiteHaarTripleValue blockCount first.2 middle.1 target.2) +
        -(finiteHaarTripleValue blockCount first.2 middle.2 target.1))),
    ((finiteHaarTripleValue blockCount first.1 middle.1 target.2 +
        finiteHaarTripleValue blockCount first.1 middle.2 target.1) +
      (finiteHaarTripleValue blockCount first.2 middle.1 target.1 +
        -(finiteHaarTripleValue blockCount first.2 middle.2 target.2))))

private theorem finiteProductHaarComplex_mul_right_expansion
    (blockCount : Nat)
    (first middle target : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul first
          (complexRatPolyMul middle target)))
      (finiteHaarComplexTripleValue
        blockCount first middle target) := by
  unfold finiteProductHaarComplex complexRatPolyMul
    finiteHaarComplexTripleValue RationalComplexEqv
  constructor
  · change
      finiteProductHaar blockCount
          (polyAdd
            (polyMul first.1
              (polyAdd
                (polyMul middle.1 target.1)
                (polyNeg (polyMul middle.2 target.2))))
            (polyNeg
              (polyMul first.2
                (polyAdd
                  (polyMul middle.1 target.2)
                  (polyMul middle.2 target.1))))) ≈ _
    refine Q'.eqv_trans _
      (finiteProductHaar blockCount
          (polyMul first.1
            (polyAdd
              (polyMul middle.1 target.1)
              (polyNeg (polyMul middle.2 target.2)))) +
        finiteProductHaar blockCount
          (polyNeg
            (polyMul first.2
              (polyAdd
                (polyMul middle.1 target.2)
                (polyMul middle.2 target.1))))) _
      (finiteProductHaar_add blockCount _ _) ?_
    refine Q'.eqv_trans _
      (finiteProductHaar blockCount
          (polyMul first.1
            (polyAdd
              (polyMul middle.1 target.1)
              (polyNeg (polyMul middle.2 target.2)))) +
        -(finiteProductHaar blockCount
          (polyMul first.2
            (polyAdd
              (polyMul middle.1 target.2)
              (polyMul middle.2 target.1))))) _
      (QPoly.q_add_congr (Q'.eqv_refl _)
        (finiteProductHaar_neg blockCount _)) ?_
    refine Q'.eqv_trans _
      ((finiteProductHaar blockCount
            (polyMul first.1 (polyMul middle.1 target.1)) +
          finiteProductHaar blockCount
            (polyMul first.1
              (polyNeg (polyMul middle.2 target.2)))) +
        -(finiteProductHaar blockCount
          (polyMul first.2
            (polyAdd
              (polyMul middle.1 target.2)
              (polyMul middle.2 target.1))))) _
      (QPoly.q_add_congr
        (finiteProductHaar_polyMul_add_right blockCount first.1 _ _)
        (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _
      ((finiteHaarTripleValue blockCount first.1 middle.1 target.1 +
          -(finiteHaarTripleValue blockCount first.1 middle.2 target.2)) +
        -(finiteProductHaar blockCount
          (polyMul first.2
            (polyAdd
              (polyMul middle.1 target.2)
              (polyMul middle.2 target.1))))) _
      (QPoly.q_add_congr
        (QPoly.q_add_congr (Q'.eqv_refl _)
          (finiteProductHaar_polyMul_neg_right
            blockCount first.1 (polyMul middle.2 target.2)))
        (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _
      ((finiteHaarTripleValue blockCount first.1 middle.1 target.1 +
          -(finiteHaarTripleValue blockCount first.1 middle.2 target.2)) +
        -(finiteHaarTripleValue blockCount first.2 middle.1 target.2 +
          finiteHaarTripleValue blockCount first.2 middle.2 target.1)) _
      (QPoly.q_add_congr (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _
          (finiteProductHaar_polyMul_add_right
            blockCount first.2 _ _))) ?_
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den,
      neg_num_cast, Int.add_mul, Int.neg_mul, Int.neg_add]
  · change
      finiteProductHaar blockCount
          (polyAdd
            (polyMul first.1
              (polyAdd
                (polyMul middle.1 target.2)
                (polyMul middle.2 target.1)))
            (polyMul first.2
              (polyAdd
                (polyMul middle.1 target.1)
                (polyNeg (polyMul middle.2 target.2))))) ≈ _
    refine Q'.eqv_trans _
      (finiteProductHaar blockCount
          (polyMul first.1
            (polyAdd
              (polyMul middle.1 target.2)
              (polyMul middle.2 target.1))) +
        finiteProductHaar blockCount
          (polyMul first.2
            (polyAdd
              (polyMul middle.1 target.1)
              (polyNeg (polyMul middle.2 target.2))))) _
      (finiteProductHaar_add blockCount _ _) ?_
    refine Q'.eqv_trans _
      ((finiteHaarTripleValue blockCount first.1 middle.1 target.2 +
          finiteHaarTripleValue blockCount first.1 middle.2 target.1) +
        (finiteProductHaar blockCount
            (polyMul first.2 (polyMul middle.1 target.1)) +
          finiteProductHaar blockCount
            (polyMul first.2
              (polyNeg (polyMul middle.2 target.2))))) _
      (QPoly.q_add_congr
        (finiteProductHaar_polyMul_add_right blockCount first.1 _ _)
        (finiteProductHaar_polyMul_add_right blockCount first.2 _ _)) ?_
    refine Q'.eqv_trans _
      ((finiteHaarTripleValue blockCount first.1 middle.1 target.2 +
          finiteHaarTripleValue blockCount first.1 middle.2 target.1) +
        (finiteHaarTripleValue blockCount first.2 middle.1 target.1 +
          -(finiteHaarTripleValue blockCount first.2 middle.2 target.2))) _
      (QPoly.q_add_congr (Q'.eqv_refl _)
        (QPoly.q_add_congr (Q'.eqv_refl _)
          (finiteProductHaar_polyMul_neg_right
            blockCount first.2 (polyMul middle.2 target.2)))) ?_
    exact Q'.eqv_refl _

private theorem finiteProductHaarComplex_mul_left_expansion
    (blockCount : Nat)
    (first middle target : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul
          (complexRatPolyMul first middle) target))
      (finiteHaarComplexTripleValue
        blockCount first middle target) := by
  unfold finiteProductHaarComplex complexRatPolyMul
    finiteHaarComplexTripleValue RationalComplexEqv
  constructor
  · change
      finiteProductHaar blockCount
          (polyAdd
            (polyMul
              (polyAdd
                (polyMul first.1 middle.1)
                (polyNeg (polyMul first.2 middle.2))) target.1)
            (polyNeg
              (polyMul
                (polyAdd
                  (polyMul first.1 middle.2)
                  (polyMul first.2 middle.1)) target.2))) ≈ _
    refine Q'.eqv_trans _
      (finiteProductHaar blockCount
          (polyMul
            (polyAdd
              (polyMul first.1 middle.1)
              (polyNeg (polyMul first.2 middle.2))) target.1) +
        finiteProductHaar blockCount
          (polyNeg
            (polyMul
              (polyAdd
                (polyMul first.1 middle.2)
                (polyMul first.2 middle.1)) target.2))) _
      (finiteProductHaar_add blockCount _ _) ?_
    refine Q'.eqv_trans _
      ((finiteProductHaar blockCount
            (polyMul (polyMul first.1 middle.1) target.1) +
          finiteProductHaar blockCount
            (polyMul (polyNeg (polyMul first.2 middle.2)) target.1)) +
        -(finiteProductHaar blockCount
          (polyMul
            (polyAdd
              (polyMul first.1 middle.2)
              (polyMul first.2 middle.1)) target.2))) _
      (QPoly.q_add_congr
        (finiteProductHaar_polyMul_add_left blockCount _ _ target.1)
        (finiteProductHaar_neg blockCount _)) ?_
    refine Q'.eqv_trans _
      ((finiteProductHaar blockCount
            (polyMul (polyMul first.1 middle.1) target.1) +
          -(finiteProductHaar blockCount
            (polyMul (polyMul first.2 middle.2) target.1))) +
        -(finiteProductHaar blockCount
            (polyMul (polyMul first.1 middle.2) target.2) +
          finiteProductHaar blockCount
            (polyMul (polyMul first.2 middle.1) target.2))) _
      (QPoly.q_add_congr
        (QPoly.q_add_congr (Q'.eqv_refl _)
          (finiteProductHaar_polyMul_neg_left
            blockCount (polyMul first.2 middle.2) target.1))
        (Q'.neg_eqv_congr _ _
          (finiteProductHaar_polyMul_add_left
            blockCount _ _ target.2))) ?_
    refine Q'.eqv_trans _
      ((finiteHaarTripleValue blockCount first.1 middle.1 target.1 +
          -(finiteHaarTripleValue blockCount first.2 middle.2 target.1)) +
        -(finiteHaarTripleValue blockCount first.1 middle.2 target.2 +
          finiteHaarTripleValue blockCount first.2 middle.1 target.2)) _
      (QPoly.q_add_congr
        (QPoly.q_add_congr
          (finiteProductHaar_polyMul_assoc
            blockCount first.1 middle.1 target.1)
          (Q'.neg_eqv_congr _ _
            (finiteProductHaar_polyMul_assoc
              blockCount first.2 middle.2 target.1)))
        (Q'.neg_eqv_congr _ _
          (QPoly.q_add_congr
            (finiteProductHaar_polyMul_assoc
              blockCount first.1 middle.2 target.2)
            (finiteProductHaar_polyMul_assoc
              blockCount first.2 middle.1 target.2)))) ?_
    ring_qeqv
  · change
      finiteProductHaar blockCount
          (polyAdd
            (polyMul
              (polyAdd
                (polyMul first.1 middle.1)
                (polyNeg (polyMul first.2 middle.2))) target.2)
            (polyMul
              (polyAdd
                (polyMul first.1 middle.2)
                (polyMul first.2 middle.1)) target.1)) ≈ _
    refine Q'.eqv_trans _
      (finiteProductHaar blockCount
          (polyMul
            (polyAdd
              (polyMul first.1 middle.1)
              (polyNeg (polyMul first.2 middle.2))) target.2) +
        finiteProductHaar blockCount
          (polyMul
            (polyAdd
              (polyMul first.1 middle.2)
              (polyMul first.2 middle.1)) target.1)) _
      (finiteProductHaar_add blockCount _ _) ?_
    refine Q'.eqv_trans _
      ((finiteProductHaar blockCount
            (polyMul (polyMul first.1 middle.1) target.2) +
          -(finiteProductHaar blockCount
            (polyMul (polyMul first.2 middle.2) target.2))) +
        (finiteProductHaar blockCount
            (polyMul (polyMul first.1 middle.2) target.1) +
          finiteProductHaar blockCount
            (polyMul (polyMul first.2 middle.1) target.1))) _
      (QPoly.q_add_congr
        (Q'.eqv_trans _ _ _
          (finiteProductHaar_polyMul_add_left
            blockCount _ _ target.2)
          (QPoly.q_add_congr (Q'.eqv_refl _)
            (finiteProductHaar_polyMul_neg_left
              blockCount (polyMul first.2 middle.2) target.2)))
        (finiteProductHaar_polyMul_add_left
          blockCount _ _ target.1)) ?_
    refine Q'.eqv_trans _
      ((finiteHaarTripleValue blockCount first.1 middle.1 target.2 +
          -(finiteHaarTripleValue blockCount first.2 middle.2 target.2)) +
        (finiteHaarTripleValue blockCount first.1 middle.2 target.1 +
          finiteHaarTripleValue blockCount first.2 middle.1 target.1)) _
      (QPoly.q_add_congr
        (QPoly.q_add_congr
          (finiteProductHaar_polyMul_assoc
            blockCount first.1 middle.1 target.2)
          (Q'.neg_eqv_congr _ _
            (finiteProductHaar_polyMul_assoc
              blockCount first.2 middle.2 target.2)))
        (QPoly.q_add_congr
          (finiteProductHaar_polyMul_assoc
            blockCount first.1 middle.2 target.1)
          (finiteProductHaar_polyMul_assoc
            blockCount first.2 middle.1 target.1))) ?_
    ring_qeqv

/-- Honest complex associativity after finite-product Haar evaluation. -/
theorem finiteProductHaarComplex_mul_assoc
    (blockCount : Nat)
    (first middle target : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul
          (complexRatPolyMul first middle) target))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul first
          (complexRatPolyMul middle target))) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_left_expansion
      blockCount first middle target)
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_mul_right_expansion
        blockCount first middle target))

private theorem finiteHaarComplexTripleValue_middle_comm
    (blockCount : Nat)
    (first middle target : ComplexRatPoly) :
    RationalComplexEqv
      (finiteHaarComplexTripleValue blockCount first middle target)
      (finiteHaarComplexTripleValue blockCount first target middle) := by
  unfold finiteHaarComplexTripleValue RationalComplexEqv
  constructor
  · refine Q'.eqv_trans _
      ((finiteHaarTripleValue blockCount first.1 target.1 middle.1 +
          -(finiteHaarTripleValue blockCount first.1 target.2 middle.2)) +
        (-(finiteHaarTripleValue blockCount first.2 target.2 middle.1) +
          -(finiteHaarTripleValue blockCount first.2 target.1 middle.2))) _ ?_ ?_
    · exact QPoly.q_add_congr
        (QPoly.q_add_congr
          (finiteProductHaar_polyMul_middle_comm
            blockCount first.1 middle.1 target.1)
          (Q'.neg_eqv_congr _ _
            (finiteProductHaar_polyMul_middle_comm
              blockCount first.1 middle.2 target.2)))
        (QPoly.q_add_congr
          (Q'.neg_eqv_congr _ _
            (finiteProductHaar_polyMul_middle_comm
              blockCount first.2 middle.1 target.2))
          (Q'.neg_eqv_congr _ _
            (finiteProductHaar_polyMul_middle_comm
              blockCount first.2 middle.2 target.1)))
    · ring_qeqv
  · refine Q'.eqv_trans _
      ((finiteHaarTripleValue blockCount first.1 target.2 middle.1 +
          finiteHaarTripleValue blockCount first.1 target.1 middle.2) +
        (finiteHaarTripleValue blockCount first.2 target.1 middle.1 +
          -(finiteHaarTripleValue blockCount first.2 target.2 middle.2))) _ ?_ ?_
    · exact QPoly.q_add_congr
        (QPoly.q_add_congr
          (finiteProductHaar_polyMul_middle_comm
            blockCount first.1 middle.1 target.2)
          (finiteProductHaar_polyMul_middle_comm
            blockCount first.1 middle.2 target.1))
        (QPoly.q_add_congr
          (finiteProductHaar_polyMul_middle_comm
            blockCount first.2 middle.1 target.1)
          (Q'.neg_eqv_congr _ _
            (finiteProductHaar_polyMul_middle_comm
              blockCount first.2 middle.2 target.2)))
    · ring_qeqv

/-- Honest exchange of the last two complex factors after finite-product
Haar evaluation. -/
theorem finiteProductHaarComplex_mul_middle_comm
    (blockCount : Nat)
    (first middle target : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul first
          (complexRatPolyMul middle target)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul first
          (complexRatPolyMul target middle))) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_right_expansion
      blockCount first middle target)
    (rationalComplexEqv_trans
      (finiteHaarComplexTripleValue_middle_comm
        blockCount first middle target)
      (rationalComplexEqv_symm
        (finiteProductHaarComplex_mul_right_expansion
          blockCount first target middle)))

/-! ## 4. Canonical complex four-factor expansion -/

/-- A real four-factor value in the right-associated normal form used by the
complexification below. -/
private def finiteHaarFourValue
    (blockCount : Nat) (first second third fourth : RatPoly) : Q' :=
  finiteHaarTripleValue blockCount first second (polyMul third fourth)

/-- Finite-product Haar is additive in the final argument of the canonical
real triple. -/
private theorem finiteHaarTripleValue_add_target
    (blockCount : Nat) (first middle left right : RatPoly) :
    finiteHaarTripleValue blockCount first middle (polyAdd left right) ≈
      finiteHaarTripleValue blockCount first middle left +
        finiteHaarTripleValue blockCount first middle right :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finiteProductHaar_polyMul_assoc
        blockCount first middle (polyAdd left right)))
    (Q'.eqv_trans _ _ _
      (finiteProductHaar_polyMul_add_right
        blockCount (polyMul first middle) left right)
      (QPoly.q_add_congr
        (finiteProductHaar_polyMul_assoc
          blockCount first middle left)
        (finiteProductHaar_polyMul_assoc
          blockCount first middle right)))

/-- Finite-product Haar pulls a negation out of the final argument of the
canonical real triple. -/
private theorem finiteHaarTripleValue_neg_target
    (blockCount : Nat) (first middle target : RatPoly) :
    finiteHaarTripleValue blockCount first middle (polyNeg target) ≈
      -(finiteHaarTripleValue blockCount first middle target) :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finiteProductHaar_polyMul_assoc
        blockCount first middle (polyNeg target)))
    (Q'.eqv_trans _ _ _
      (finiteProductHaar_polyMul_neg_right
        blockCount (polyMul first middle) target)
      (Q'.neg_eqv_congr _ _
        (finiteProductHaar_polyMul_assoc
          blockCount first middle target)))

/-- The canonical real four-factor value inherits the genuine middle-factor
exchange from the arbitrary-block real Haar backend. -/
private theorem finiteHaarFourValue_swap
    (blockCount : Nat) (first second third fourth : RatPoly) :
    finiteHaarFourValue blockCount first second third fourth ≈
      finiteHaarFourValue blockCount first third second fourth :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finiteProductHaar_polyMul_assoc
        blockCount first second (polyMul third fourth)))
    (Q'.eqv_trans _ _ _
      (finiteProductHaar_polyMul_four_swap
        blockCount first second third fourth)
      (finiteProductHaar_polyMul_assoc
        blockCount first third (polyMul second fourth)))

/-- Expansion of a real component of a complex product in the final slot of
the canonical triple. -/
private theorem finiteHaarTripleValue_complexMul_re
    (blockCount : Nat) (first middle thirdRe thirdIm fourthRe fourthIm : RatPoly) :
    finiteHaarTripleValue blockCount first middle
        (polyAdd (polyMul thirdRe fourthRe)
          (polyNeg (polyMul thirdIm fourthIm))) ≈
      finiteHaarFourValue blockCount first middle thirdRe fourthRe +
        -(finiteHaarFourValue blockCount first middle thirdIm fourthIm) :=
  Q'.eqv_trans _ _ _
    (finiteHaarTripleValue_add_target blockCount first middle
      (polyMul thirdRe fourthRe) (polyNeg (polyMul thirdIm fourthIm)))
    (QPoly.q_add_congr (Q'.eqv_refl _)
      (finiteHaarTripleValue_neg_target blockCount first middle
        (polyMul thirdIm fourthIm)))

/-- Expansion of an imaginary component of a complex product in the final
slot of the canonical triple. -/
private theorem finiteHaarTripleValue_complexMul_im
    (blockCount : Nat) (first middle thirdRe thirdIm fourthRe fourthIm : RatPoly) :
    finiteHaarTripleValue blockCount first middle
        (polyAdd (polyMul thirdRe fourthIm)
          (polyMul thirdIm fourthRe)) ≈
      finiteHaarFourValue blockCount first middle thirdRe fourthIm +
        finiteHaarFourValue blockCount first middle thirdIm fourthRe :=
  finiteHaarTripleValue_add_target blockCount first middle
    (polyMul thirdRe fourthIm) (polyMul thirdIm fourthRe)

/-- The common eight-term expansion of a paired complex four-factor Haar
value.  Its grouping mirrors `finiteHaarComplexTripleValue`, making the
expansion proof purely componentwise. -/
private def finiteHaarComplexFourValue
    (blockCount : Nat)
    (first second third fourth : ComplexRatPoly) : RationalComplex :=
  (((finiteHaarFourValue blockCount first.1 second.1 third.1 fourth.1 +
          -(finiteHaarFourValue blockCount first.1 second.1 third.2 fourth.2)) +
        -(finiteHaarFourValue blockCount first.1 second.2 third.1 fourth.2 +
          finiteHaarFourValue blockCount first.1 second.2 third.2 fourth.1)) +
      (-(finiteHaarFourValue blockCount first.2 second.1 third.1 fourth.2 +
          finiteHaarFourValue blockCount first.2 second.1 third.2 fourth.1) +
        -(finiteHaarFourValue blockCount first.2 second.2 third.1 fourth.1 +
          -(finiteHaarFourValue blockCount first.2 second.2 third.2 fourth.2))),
    (((finiteHaarFourValue blockCount first.1 second.1 third.1 fourth.2 +
          finiteHaarFourValue blockCount first.1 second.1 third.2 fourth.1) +
        (finiteHaarFourValue blockCount first.1 second.2 third.1 fourth.1 +
          -(finiteHaarFourValue blockCount first.1 second.2 third.2 fourth.2))) +
      ((finiteHaarFourValue blockCount first.2 second.1 third.1 fourth.1 +
          -(finiteHaarFourValue blockCount first.2 second.1 third.2 fourth.2)) +
        -(finiteHaarFourValue blockCount first.2 second.2 third.1 fourth.2 +
          finiteHaarFourValue blockCount first.2 second.2 third.2 fourth.1))))

private theorem finiteHaarComplexTripleValue_mul_target_expansion
    (blockCount : Nat)
    (first second third fourth : ComplexRatPoly) :
    RationalComplexEqv
      (finiteHaarComplexTripleValue blockCount first second
        (complexRatPolyMul third fourth))
      (finiteHaarComplexFourValue blockCount first second third fourth) := by
  unfold finiteHaarComplexTripleValue finiteHaarComplexFourValue
    complexRatPolyMul RationalComplexEqv
  constructor
  · exact QPoly.q_add_congr
      (QPoly.q_add_congr
        (finiteHaarTripleValue_complexMul_re blockCount first.1 second.1
          third.1 third.2 fourth.1 fourth.2)
        (Q'.neg_eqv_congr _ _
          (finiteHaarTripleValue_complexMul_im blockCount first.1 second.2
            third.1 third.2 fourth.1 fourth.2)))
      (QPoly.q_add_congr
        (Q'.neg_eqv_congr _ _
          (finiteHaarTripleValue_complexMul_im blockCount first.2 second.1
            third.1 third.2 fourth.1 fourth.2))
        (Q'.neg_eqv_congr _ _
          (finiteHaarTripleValue_complexMul_re blockCount first.2 second.2
            third.1 third.2 fourth.1 fourth.2)))
  · exact QPoly.q_add_congr
      (QPoly.q_add_congr
        (finiteHaarTripleValue_complexMul_im blockCount first.1 second.1
          third.1 third.2 fourth.1 fourth.2)
        (finiteHaarTripleValue_complexMul_re blockCount first.1 second.2
          third.1 third.2 fourth.1 fourth.2))
      (QPoly.q_add_congr
        (finiteHaarTripleValue_complexMul_re blockCount first.2 second.1
          third.1 third.2 fourth.1 fourth.2)
        (Q'.neg_eqv_congr _ _
          (finiteHaarTripleValue_complexMul_im blockCount first.2 second.2
            third.1 third.2 fourth.1 fourth.2)))

/-- The canonical complex four-factor expansion is invariant under exchange
of its two middle complex factors. -/
private theorem finiteHaarComplexFourValue_swap
    (blockCount : Nat)
    (first second third fourth : ComplexRatPoly) :
    RationalComplexEqv
      (finiteHaarComplexFourValue blockCount first second third fourth)
      (finiteHaarComplexFourValue blockCount first third second fourth) := by
  unfold finiteHaarComplexFourValue RationalComplexEqv
  constructor
  · have hswap := QPoly.q_add_congr
        (QPoly.q_add_congr
          (QPoly.q_add_congr
            (finiteHaarFourValue_swap blockCount
              first.1 second.1 third.1 fourth.1)
            (Q'.neg_eqv_congr _ _
              (finiteHaarFourValue_swap blockCount
                first.1 second.1 third.2 fourth.2)))
          (Q'.neg_eqv_congr _ _
            (QPoly.q_add_congr
              (finiteHaarFourValue_swap blockCount
                first.1 second.2 third.1 fourth.2)
              (finiteHaarFourValue_swap blockCount
                first.1 second.2 third.2 fourth.1))))
        (QPoly.q_add_congr
          (Q'.neg_eqv_congr _ _
            (QPoly.q_add_congr
              (finiteHaarFourValue_swap blockCount
                first.2 second.1 third.1 fourth.2)
              (finiteHaarFourValue_swap blockCount
                first.2 second.1 third.2 fourth.1)))
          (Q'.neg_eqv_congr _ _
            (QPoly.q_add_congr
              (finiteHaarFourValue_swap blockCount
                first.2 second.2 third.1 fourth.1)
              (Q'.neg_eqv_congr _ _
                (finiteHaarFourValue_swap blockCount
                  first.2 second.2 third.2 fourth.2)))))
    exact Q'.eqv_trans _ _ _ hswap (by ring_qeqv)
  · have hswap := QPoly.q_add_congr
        (QPoly.q_add_congr
          (QPoly.q_add_congr
            (finiteHaarFourValue_swap blockCount
              first.1 second.1 third.1 fourth.2)
            (finiteHaarFourValue_swap blockCount
              first.1 second.1 third.2 fourth.1))
          (QPoly.q_add_congr
            (finiteHaarFourValue_swap blockCount
              first.1 second.2 third.1 fourth.1)
            (Q'.neg_eqv_congr _ _
              (finiteHaarFourValue_swap blockCount
                first.1 second.2 third.2 fourth.2))))
        (QPoly.q_add_congr
          (QPoly.q_add_congr
            (finiteHaarFourValue_swap blockCount
              first.2 second.1 third.1 fourth.1)
            (Q'.neg_eqv_congr _ _
              (finiteHaarFourValue_swap blockCount
                first.2 second.1 third.2 fourth.2)))
          (Q'.neg_eqv_congr _ _
            (QPoly.q_add_congr
              (finiteHaarFourValue_swap blockCount
                first.2 second.2 third.1 fourth.2)
              (finiteHaarFourValue_swap blockCount
                first.2 second.2 third.2 fourth.1))))
    exact Q'.eqv_trans _ _ _ hswap (by ring_qeqv)

/-- **Complex four-factor exchange under arbitrary finite-product Haar.**
The two middle honest complex raw-polynomial factors may be exchanged in the
displayed paired parenthesization. -/
theorem finiteProductHaarComplex_mul_four_swap
    (blockCount : Nat)
    (first second third fourth : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul
          (complexRatPolyMul first second)
          (complexRatPolyMul third fourth)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul
          (complexRatPolyMul first third)
          (complexRatPolyMul second fourth))) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_left_expansion blockCount
      first second (complexRatPolyMul third fourth))
    (rationalComplexEqv_trans
      (finiteHaarComplexTripleValue_mul_target_expansion blockCount
        first second third fourth)
      (rationalComplexEqv_trans
        (finiteHaarComplexFourValue_swap blockCount
          first second third fourth)
        (rationalComplexEqv_trans
          (rationalComplexEqv_symm
            (finiteHaarComplexTripleValue_mul_target_expansion blockCount
              first third second fourth))
          (rationalComplexEqv_symm
            (finiteProductHaarComplex_mul_left_expansion blockCount
              first third (complexRatPolyMul second fourth))))))

/-! ## 5. Complex two-factor exchange -/

/-- **Complex finite-product Haar commutativity.**  Exchanging two honest
complex raw-polynomial factors preserves the exact finite-product Haar value.
The real component uses the real Haar commutativity theorem twice, including
under polynomial negation.  The imaginary component additionally exchanges
the two additive cross terms. -/
theorem finiteProductHaarComplex_mul_comm
    (blockCount : Nat) (left right : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul left right))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul right left)) := by
  unfold finiteProductHaarComplex complexRatPolyMul RationalComplexEqv
  constructor
  · exact finiteProductHaar_polyAdd_congr blockCount
      (finiteProductHaar_polyMul_comm
        blockCount left.1 right.1)
      (finiteProductHaar_polyNeg_congr blockCount
        (finiteProductHaar_polyMul_comm
          blockCount left.2 right.2))
  · refine Q'.eqv_trans _
      (finiteProductHaar blockCount
        (polyAdd
          (polyMul right.2 left.1)
          (polyMul right.1 left.2))) _ ?_ ?_
    · exact finiteProductHaar_polyAdd_congr blockCount
        (finiteProductHaar_polyMul_comm
          blockCount left.1 right.2)
        (finiteProductHaar_polyMul_comm
          blockCount left.2 right.1)
    · exact finiteProductHaar_polyAdd_comm blockCount
        (polyMul right.2 left.1)
        (polyMul right.1 left.2)

/-! ## 6. Complex unit laws -/

/-- The canonical honest complex polynomial one is a left unit under the
finite-product Haar functional. -/
theorem finiteProductHaarComplex_one_mul
    (blockCount : Nat) (value : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul complexRatPolyOne value))
      (finiteProductHaarComplex blockCount value) := by
  unfold finiteProductHaarComplex complexRatPolyMul complexRatPolyOne
    RationalComplexEqv
  constructor
  · refine Q'.eqv_trans _
      (finiteProductHaar blockCount
        (polyAdd value.1 polyZero)) _ ?_ ?_
    · exact finiteProductHaar_polyAdd_congr blockCount
        (finiteProductHaar_polyOne_mul blockCount value.1)
        (finiteProductHaar_polyNeg_congr blockCount
          (finiteProductHaar_polyZero_mul blockCount value.2))
    · exact finiteProductHaar_polyAdd_zero_right blockCount value.1
  · refine Q'.eqv_trans _
      (finiteProductHaar blockCount
        (polyAdd value.2 polyZero)) _ ?_ ?_
    · exact finiteProductHaar_polyAdd_congr blockCount
        (finiteProductHaar_polyOne_mul blockCount value.2)
        (finiteProductHaar_polyZero_mul blockCount value.1)
    · exact finiteProductHaar_polyAdd_zero_right blockCount value.2

/-- The canonical honest complex polynomial one is a right unit under the
finite-product Haar functional. -/
theorem finiteProductHaarComplex_mul_one
    (blockCount : Nat) (value : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul value complexRatPolyOne))
      (finiteProductHaarComplex blockCount value) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_comm
      blockCount value complexRatPolyOne)
    (finiteProductHaarComplex_one_mul blockCount value)

/-! ## 7. Contextual adjacent exchange and arbitrary finite reordering -/

/-- Reassociate a right-nested complex product into a single spectator prefix,
only after applying finite-product Haar. -/
theorem finiteProductHaarComplex_mul_assoc_context
    (blockCount : Nat)
    (spectator left right : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul left right)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul
          (complexRatPolyMul spectator left) right)) :=
  rationalComplexEqv_symm
    (finiteProductHaarComplex_mul_assoc
      blockCount spectator left right)

/-- Exchange two adjacent factors beneath an arbitrary complex spectator and
an arbitrary right suffix.  The genuine four-factor theorem is essential:
binary and triple Haar exchange alone do not provide this context closure. -/
theorem finiteProductHaarComplex_mul_adjacent_swap
    (blockCount : Nat)
    (spectator left right suffix : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul left
            (complexRatPolyMul right suffix))))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul right
            (complexRatPolyMul left suffix)))) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc_context
      blockCount spectator left (complexRatPolyMul right suffix))
    (rationalComplexEqv_trans
      (finiteProductHaarComplex_mul_four_swap
        blockCount spectator left right suffix)
      (finiteProductHaarComplex_mul_assoc
        blockCount spectator right (complexRatPolyMul left suffix)))

/-- A permutation of a tail-first factor word preserves its finite-product
Haar value beneath any already accumulated spectator prefix.  The proof is
structural in the supplied `List.Perm` witness, so it introduces no search,
decidable-permutation computation, or classical choice. -/
theorem finiteProductHaarComplex_mul_product_perm (blockCount : Nat) :
    ∀ (spectator : ComplexRatPoly) {left right : List ComplexRatPoly},
      left.Perm right →
        RationalComplexEqv
          (finiteProductHaarComplex blockCount
            (complexRatPolyMul spectator (complexRatPolyProduct left)))
          (finiteProductHaarComplex blockCount
            (complexRatPolyMul spectator (complexRatPolyProduct right)))
  | spectator, _, _, List.Perm.nil =>
      rationalComplexEqv_refl
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator complexRatPolyOne))
  | spectator, _, _, List.Perm.cons factor hperm => by
      exact rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_assoc_context blockCount
          spectator factor (complexRatPolyProduct _))
        (rationalComplexEqv_trans
          (finiteProductHaarComplex_mul_product_perm blockCount
            (complexRatPolyMul spectator factor) hperm)
          (rationalComplexEqv_symm
            (finiteProductHaarComplex_mul_assoc_context blockCount
              spectator factor (complexRatPolyProduct _))))
  | spectator, _, _, List.Perm.swap first second rest => by
      exact finiteProductHaarComplex_mul_adjacent_swap blockCount
        spectator second first (complexRatPolyProduct rest)
  | spectator, _, _, List.Perm.trans hfirst hsecond =>
      rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_product_perm blockCount
          spectator hfirst)
        (finiteProductHaarComplex_mul_product_perm blockCount
          spectator hsecond)

/-- **Finite complex product permutation invariance.**  Any explicitly
supplied permutation of a symbolic tail-first factor list preserves the exact
finite-product Haar value.  The concrete global factor word remains opaque. -/
theorem finiteProductHaarComplex_product_perm
    (blockCount : Nat) {left right : List ComplexRatPoly}
    (hperm : left.Perm right) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyProduct left))
      (finiteProductHaarComplex blockCount
        (complexRatPolyProduct right)) :=
  rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_one_mul blockCount
        (complexRatPolyProduct left)))
    (rationalComplexEqv_trans
      (finiteProductHaarComplex_mul_product_perm blockCount
        complexRatPolyOne hperm)
      (finiteProductHaarComplex_one_mul blockCount
        (complexRatPolyProduct right)))

#print axioms finiteProductHaar_polyAdd_congr
#print axioms finiteProductHaar_polyNeg_congr
#print axioms finiteProductHaar_polyAdd_comm
#print axioms finiteProductHaar_polyOne_mul
#print axioms finiteProductHaar_mul_polyOne
#print axioms finiteProductHaar_polyMul_add_left
#print axioms finiteProductHaar_polyMul_add_right
#print axioms finiteProductHaar_polyMul_neg_left
#print axioms finiteProductHaar_polyMul_neg_right
#print axioms finiteProductHaarComplex_mul_assoc
#print axioms finiteProductHaarComplex_mul_middle_comm
#print axioms finiteProductHaarComplex_mul_four_swap
#print axioms finiteProductHaarComplex_mul_comm
#print axioms finiteProductHaarComplex_one_mul
#print axioms finiteProductHaarComplex_mul_one
#print axioms finiteProductHaarComplex_mul_assoc_context
#print axioms finiteProductHaarComplex_mul_adjacent_swap
#print axioms finiteProductHaarComplex_mul_product_perm
#print axioms finiteProductHaarComplex_product_perm

end YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
