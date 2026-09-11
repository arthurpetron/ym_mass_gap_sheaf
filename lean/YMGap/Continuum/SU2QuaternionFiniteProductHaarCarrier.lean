/-
# Arbitrary finite products of exact rational quaternion sphere moments

The original quaternion-polynomial carrier has two four-coordinate blocks.
For a finite lattice gauge field, however, every distinct physical link must
receive its own four-coordinate block.  This leaf supplies the corresponding
finite product moment functional on the existing raw `RatPoly` carrier.

For block `b`, coordinates `4*b, ..., 4*b+3` carry one rational quaternion.
The monomial moment is the product of the exact normalized `S^3` moments over
the first `blockCount` blocks.  A nonzero exponent beyond coordinate
`4*blockCount-1` makes the monomial moment zero, matching the zero-extension
convention of the established two-block carrier.

The polynomial functional is deliberately the ordinary coefficient-times-
moment fold.  In particular, it does not reproduce the historical smart
zero-moment branch in the definition of `productHaar`; instead we prove that
the two definitions are rationally equivalent at exactly two blocks.

The list product is also exposed independently.  Its append and permutation
laws are the elementary finite Fubini/reordering atoms needed before a later
leaf introduces link-indexed coordinate substitutions.  This file does not
claim sphere-ideal descent, square positivity, or translation invariance.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionHaarSphereIdeal

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-! ## 1. One block and finite block products -/

/-- The exact normalized `S^3` moment of the four coordinates in block
`block`.  Blocks are laid out consecutively in scalar-first quaternion order.
-/
def quaternionBlockMoment (block : Nat) (monomial : List Nat) : Q' :=
  sphereMoment4
    (exponentAt monomial (4 * block))
    (exponentAt monomial (4 * block + 1))
    (exponentAt monomial (4 * block + 2))
    (exponentAt monomial (4 * block + 3))

/-- Product of the selected quaternion-block moments, in the supplied finite
order.  The value depends only on the resulting finite multiset of blocks, as
proved below by the permutation theorem. -/
def quaternionBlockMomentProduct (monomial : List Nat) : List Nat → Q'
  | [] => 1
  | block :: blocks =>
      quaternionBlockMoment block monomial *
        quaternionBlockMomentProduct monomial blocks

/-- Finite-product Fubini atom: concatenating two block orders multiplies the
corresponding exact moment products. -/
theorem quaternionBlockMomentProduct_append (monomial : List Nat) :
    ∀ left right : List Nat,
      quaternionBlockMomentProduct monomial (left ++ right) ≈
        quaternionBlockMomentProduct monomial left *
          quaternionBlockMomentProduct monomial right
  | [], right => Q'.eqv_symm
      (Q'.one_mul_eqv (quaternionBlockMomentProduct monomial right))
  | block :: blocks, right => by
      change
        quaternionBlockMoment block monomial *
            quaternionBlockMomentProduct monomial (blocks ++ right) ≈
          (quaternionBlockMoment block monomial *
              quaternionBlockMomentProduct monomial blocks) *
            quaternionBlockMomentProduct monomial right
      refine Q'.eqv_trans _
        (quaternionBlockMoment block monomial *
          (quaternionBlockMomentProduct monomial blocks *
            quaternionBlockMomentProduct monomial right)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (quaternionBlockMomentProduct_append monomial blocks right)
      · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- A finite reordering of quaternion blocks does not change their product
moment.  This is the exact constructive block-reindexing atom. -/
theorem quaternionBlockMomentProduct_perm (monomial : List Nat) :
    ∀ {left right : List Nat}, left.Perm right →
      quaternionBlockMomentProduct monomial left ≈
        quaternionBlockMomentProduct monomial right
  | _, _, List.Perm.nil => Q'.eqv_refl 1
  | _, _, List.Perm.cons _ hperm =>
      Q'.mul_eqv_congr_left _ _ _
        (quaternionBlockMomentProduct_perm monomial hperm)
  | _, _, List.Perm.swap first second rest => by
      change
        quaternionBlockMoment second monomial *
            (quaternionBlockMoment first monomial *
              quaternionBlockMomentProduct monomial rest) ≈
          quaternionBlockMoment first monomial *
            (quaternionBlockMoment second monomial *
              quaternionBlockMomentProduct monomial rest)
      refine Q'.eqv_trans _
        ((quaternionBlockMoment second monomial *
            quaternionBlockMoment first monomial) *
          quaternionBlockMomentProduct monomial rest) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((quaternionBlockMoment first monomial *
            quaternionBlockMoment second monomial) *
          quaternionBlockMomentProduct monomial rest) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (quaternionBlockMomentProduct_perm monomial hleft)
        (quaternionBlockMomentProduct_perm monomial hright)

/-! ## 2. Prefix product moment and the ordinary linear functional -/

/-- Exact product sphere moment on the first `blockCount` quaternion blocks.
Any genuinely higher-coordinate monomial is sent to zero. -/
def finiteProductHaarMono (blockCount : Nat) (monomial : List Nat) : Q' :=
  if allZero (monomial.drop (4 * blockCount)) then
    quaternionBlockMomentProduct monomial (List.range blockCount)
  else 0

/-- Ordinary coefficient-times-moment fold on the raw finite polynomial
carrier.  Duplicate monomials are intentionally retained. -/
def finiteProductHaar (blockCount : Nat) : RatPoly → Q'
  | [] => 0
  | term :: polynomial =>
      term.2 * finiteProductHaarMono blockCount term.1 +
        finiteProductHaar blockCount polynomial

/-! ## 3. Normalization and structural linearity -/

theorem quaternionBlockMoment_nil (block : Nat) :
    quaternionBlockMoment block [] ≈ 1 := by
  simpa [quaternionBlockMoment, exponentAt] using sphereMoment4_one

theorem quaternionBlockMomentProduct_nil : ∀ blocks : List Nat,
    quaternionBlockMomentProduct [] blocks ≈ 1
  | [] => Q'.eqv_refl 1
  | block :: blocks => by
      refine Q'.eqv_trans _ ((1 : Q') * 1) _ ?_ ?_
      · exact q_mul_congr
          (quaternionBlockMoment_nil block)
          (quaternionBlockMomentProduct_nil blocks)
      · exact Q'.one_mul_eqv 1

theorem finiteProductHaarMono_nil (blockCount : Nat) :
    finiteProductHaarMono blockCount [] ≈ 1 := by
  simp only [finiteProductHaarMono, List.drop_nil,
    SU2QuaternionPolynomialHaarCarrier.allZero, if_true]
  exact quaternionBlockMomentProduct_nil (List.range blockCount)

theorem finiteProductHaar_zero (blockCount : Nat) :
    finiteProductHaar blockCount polyZero ≈ 0 :=
  Q'.eqv_refl 0

theorem finiteProductHaar_one (blockCount : Nat) :
    finiteProductHaar blockCount polyOne ≈ 1 := by
  change
    (1 : Q') * finiteProductHaarMono blockCount [] + 0 ≈ 1
  refine Q'.eqv_trans _ ((1 : Q') * 1 + 0) _ ?_ ?_
  · exact q_add_congr
      (q_mul_congr (Q'.eqv_refl 1)
        (finiteProductHaarMono_nil blockCount))
      (Q'.eqv_refl 0)
  · exact Q'.eqv_trans _ ((1 : Q') * 1) _
      (QPoly.q_add_zero_eqv _) (Q'.one_mul_eqv 1)

theorem finiteProductHaar_append (blockCount : Nat) :
    ∀ polynomial remainder : RatPoly,
      finiteProductHaar blockCount (polynomial ++ remainder) ≈
        finiteProductHaar blockCount polynomial +
          finiteProductHaar blockCount remainder
  | [], remainder => Q'.eqv_symm
      (QPoly.q_zero_add_eqv (finiteProductHaar blockCount remainder))
  | term :: polynomial, remainder => by
      change
        term.2 * finiteProductHaarMono blockCount term.1 +
            finiteProductHaar blockCount (polynomial ++ remainder) ≈
          (term.2 * finiteProductHaarMono blockCount term.1 +
              finiteProductHaar blockCount polynomial) +
            finiteProductHaar blockCount remainder
      refine Q'.eqv_trans _
        (term.2 * finiteProductHaarMono blockCount term.1 +
          (finiteProductHaar blockCount polynomial +
            finiteProductHaar blockCount remainder)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (finiteProductHaar_append blockCount polynomial remainder)
      · exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

theorem finiteProductHaar_add (blockCount : Nat)
    (left right : RatPoly) :
    finiteProductHaar blockCount (polyAdd left right) ≈
      finiteProductHaar blockCount left + finiteProductHaar blockCount right :=
  finiteProductHaar_append blockCount left right

theorem finiteProductHaar_smul (blockCount : Nat) (scalar : Q') :
    ∀ polynomial : RatPoly,
      finiteProductHaar blockCount (polySmul scalar polynomial) ≈
        scalar * finiteProductHaar blockCount polynomial
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv scalar)
  | term :: polynomial => by
      change
        (scalar * term.2) * finiteProductHaarMono blockCount term.1 +
            finiteProductHaar blockCount (polySmul scalar polynomial) ≈
          scalar *
            (term.2 * finiteProductHaarMono blockCount term.1 +
              finiteProductHaar blockCount polynomial)
      refine Q'.eqv_trans _
        (scalar * (term.2 * finiteProductHaarMono blockCount term.1) +
          scalar * finiteProductHaar blockCount polynomial) _ ?_ ?_
      · exact q_add_congr
          (Q'.mul_assoc_eqv scalar term.2
            (finiteProductHaarMono blockCount term.1))
          (finiteProductHaar_smul blockCount scalar polynomial)
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv scalar
            (term.2 * finiteProductHaarMono blockCount term.1)
            (finiteProductHaar blockCount polynomial))

theorem finiteProductHaar_neg (blockCount : Nat) : ∀ polynomial : RatPoly,
    finiteProductHaar blockCount (polyNeg polynomial) ≈
      -(finiteProductHaar blockCount polynomial)
  | [] => by
      change (0 : Q') ≈ 0
      exact Q'.eqv_refl 0
  | term :: polynomial => by
      change
        (-term.2) * finiteProductHaarMono blockCount term.1 +
            finiteProductHaar blockCount (polyNeg polynomial) ≈
          -(term.2 * finiteProductHaarMono blockCount term.1 +
            finiteProductHaar blockCount polynomial)
      refine Q'.eqv_trans _
        (-(term.2 * finiteProductHaarMono blockCount term.1) +
          -(finiteProductHaar blockCount polynomial)) _ ?_ ?_
      · exact q_add_congr
          (Q'.neg_mul_eqv term.2
            (finiteProductHaarMono blockCount term.1))
          (finiteProductHaar_neg blockCount polynomial)
      · exact Q'.eqv_symm (Q'.neg_add_eqv _ _)

/-! ## 4. Exact regression to the established two-block functional -/

/-- At two blocks the new prefix monomial moment is exactly the established
two-quaternion product moment, up to the rational setoid's harmless terminal
multiplication by one. -/
theorem finiteProductHaarMono_two_eqv_productHaarMono
    (monomial : List Nat) :
    finiteProductHaarMono 2 monomial ≈ productHaarMono monomial := by
  unfold finiteProductHaarMono productHaarMono
  by_cases htail : allZero (monomial.drop 8) = true
  · rw [if_pos htail, if_pos htail]
    change
      sphereMoment4 (exponentAt monomial 0) (exponentAt monomial 1)
          (exponentAt monomial 2) (exponentAt monomial 3) *
        (sphereMoment4 (exponentAt monomial 4) (exponentAt monomial 5)
          (exponentAt monomial 6) (exponentAt monomial 7) * 1) ≈
      sphereMoment4 (exponentAt monomial 0) (exponentAt monomial 1)
          (exponentAt monomial 2) (exponentAt monomial 3) *
        sphereMoment4 (exponentAt monomial 4) (exponentAt monomial 5)
          (exponentAt monomial 6) (exponentAt monomial 7)
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _)
  · have hfalse : allZero (monomial.drop 8) = false := by
      cases hvalue : allZero (monomial.drop 8) with
      | false => rfl
      | true => exact (htail hvalue).elim
    rw [hfalse]
    exact Q'.eqv_refl 0

private theorem finiteProductHaar_two_eqv_linearSum : ∀ polynomial : RatPoly,
    finiteProductHaar 2 polynomial ≈ productHaarLinearSum polynomial
  | [] => Q'.eqv_refl 0
  | term :: polynomial => by
      change
        term.2 * finiteProductHaarMono 2 term.1 +
            finiteProductHaar 2 polynomial ≈
          term.2 * productHaarMono term.1 +
            productHaarLinearSum polynomial
      exact q_add_congr
        (Q'.mul_eqv_congr_left term.2 _ _
          (finiteProductHaarMono_two_eqv_productHaarMono term.1))
        (finiteProductHaar_two_eqv_linearSum polynomial)

/-- The arbitrary-block functional specializes at block count two to the
existing explicit product-Haar functional on every raw polynomial. -/
theorem finiteProductHaar_two_eqv_productHaar (polynomial : RatPoly) :
    finiteProductHaar 2 polynomial ≈ productHaar polynomial :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_two_eqv_linearSum polynomial)
    (Q'.eqv_symm (productHaar_eqv_linearSum polynomial))

#print axioms quaternionBlockMomentProduct_append
#print axioms quaternionBlockMomentProduct_perm
#print axioms finiteProductHaar_one
#print axioms finiteProductHaar_append
#print axioms finiteProductHaar_smul
#print axioms finiteProductHaar_neg
#print axioms finiteProductHaarMono_two_eqv_productHaarMono
#print axioms finiteProductHaar_two_eqv_productHaar

end YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
