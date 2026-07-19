/-
# Constructive radius homogenization for any finite quaternion-block prefix

Inside one coordinate-parity sector, different monomials may still have
different total degrees in each quaternion block.  This leaf removes that
remaining obstruction without enumerating either degree vectors or parity
vectors.

For each block, a computable target degree is obtained from a finite degree
sum.  Each original term is then raised independently by a block-recursive
schedule of powers of `quaternionBlockRadiusPolynomial`.  The schedule is
lazy in the block count and exponent: it is never evaluated to an enumerated
family in any proof below.  Literal support, coordinate parity, and the exact
degree invariant are propagated structurally.

The finite-product sphere-ideal theorem shows that every scheduled radius
insertion leaves Haar pairings unchanged.  Consequently the homogenized
square has exactly the same finite-product Haar value as the original square,
while it satisfies the arbitrary-block multihomogeneous positivity theorem.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarMultihomogeneousPositivity

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization

set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionFiniteProductHaarMultihomogeneousPositivity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Commutative polynomial-product algebra under finite Haar -/

theorem monoMul_comm (left right : List Nat) :
    monoMul left right = monoMul right left := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons head tail ih =>
      cases right with
      | nil => rfl
      | cons other rest => simp [monoMul, Nat.add_comm, ih rest]

theorem monoMul_assoc (first second third : List Nat) :
    monoMul (monoMul first second) third =
      monoMul first (monoMul second third) := by
  induction first generalizing second third with
  | nil => rfl
  | cons head tail ih =>
      cases second with
      | nil => rfl
      | cons other rest =>
          cases third with
          | nil => rfl
          | cons final remaining =>
              simp [monoMul, Nat.add_assoc, ih rest remaining]

private def finiteHaarCell
    (blockCount : Nat) (left right : RatTerm) : Q' :=
  (left.2 * right.2) *
    finiteProductHaarMono blockCount (monoMul left.1 right.1)

private theorem finiteHaarCell_symm
    (blockCount : Nat) (left right : RatTerm) :
    finiteHaarCell blockCount left right ≈
      finiteHaarCell blockCount right left := by
  unfold finiteHaarCell
  rw [monoMul_comm left.1 right.1]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_comm_eqv left.2 right.2)

private theorem finiteHaarBilinear_nil_right
    (blockCount : Nat) : ∀ polynomial : RatPoly,
    finiteHaarBilinear blockCount polynomial [] ≈ 0
  | [] => Q'.eqv_refl 0
  | _ :: polynomial =>
      Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr_left 0 _ _
          (finiteHaarBilinear_nil_right blockCount polynomial))
        (QPoly.q_zero_add_eqv 0)

private theorem finiteHaarBilinear_symm
    (blockCount : Nat) : ∀ left right : RatPoly,
    finiteHaarBilinear blockCount left right ≈
      finiteHaarBilinear blockCount right left
  | [], right => Q'.eqv_symm
      (finiteHaarBilinear_nil_right blockCount right)
  | left :: polynomial, [] =>
      finiteHaarBilinear_nil_right blockCount (left :: polynomial)
  | left :: polynomial, right :: remainder => by
      change
        (finiteHaarCell blockCount left right +
            finiteHaarRow blockCount left remainder) +
          finiteHaarBilinear blockCount polynomial (right :: remainder) ≈
        (finiteHaarCell blockCount right left +
            finiteHaarRow blockCount right polynomial) +
          finiteHaarBilinear blockCount remainder (left :: polynomial)
      refine Q'.eqv_trans _
        ((finiteHaarCell blockCount left right +
            finiteHaarRow blockCount left remainder) +
          (finiteHaarRow blockCount right polynomial +
            finiteHaarBilinear blockCount remainder polynomial)) _
        (Q'.add_eqv_congr_left _ _ _ (by
          simpa [finiteHaarBilinear] using
            finiteHaarBilinear_symm blockCount polynomial
              (right :: remainder))) ?_
      refine Q'.eqv_trans _
        ((finiteHaarCell blockCount right left +
            finiteHaarRow blockCount left remainder) +
          (finiteHaarRow blockCount right polynomial +
            finiteHaarBilinear blockCount polynomial remainder)) _
        (QPoly.q_add_congr
          (Q'.add_eqv_congr_right _ _ _
            (finiteHaarCell_symm blockCount left right))
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm
              (finiteHaarBilinear_symm
                blockCount polynomial remainder)))) ?_
      refine Q'.eqv_trans _
        ((finiteHaarCell blockCount right left +
            finiteHaarRow blockCount right polynomial) +
          (finiteHaarRow blockCount left remainder +
            finiteHaarBilinear blockCount polynomial remainder)) _
        (QPoly.q_interchange _ _ _ _) ?_
      exact Q'.add_eqv_congr_left _ _ _ (by
        simpa [finiteHaarBilinear] using
          finiteHaarBilinear_symm blockCount
            (left :: polynomial) remainder)

/-- Finite-product Haar is symmetric on raw polynomial products. -/
theorem finiteProductHaar_polyMul_comm
    (blockCount : Nat) (left right : RatPoly) :
    finiteProductHaar blockCount (polyMul left right) ≈
      finiteProductHaar blockCount (polyMul right left) :=
  Q'.eqv_trans _ (finiteHaarBilinear blockCount left right) _
    (finiteProductHaar_polyMul_eq_bilinear blockCount left right)
    (Q'.eqv_trans _ (finiteHaarBilinear blockCount right left) _
      (finiteHaarBilinear_symm blockCount left right)
      (Q'.eqv_symm
        (finiteProductHaar_polyMul_eq_bilinear
          blockCount right left)))

private theorem finiteHaarRow_append
    (blockCount : Nat) (term : RatTerm) : ∀ left right : RatPoly,
    finiteHaarRow blockCount term (left ++ right) ≈
      finiteHaarRow blockCount term left +
        finiteHaarRow blockCount term right
  | [], right => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | head :: tail, right => by
      change
        finiteHaarCell blockCount term head +
            finiteHaarRow blockCount term (tail ++ right) ≈
          (finiteHaarCell blockCount term head +
              finiteHaarRow blockCount term tail) +
            finiteHaarRow blockCount term right
      refine Q'.eqv_trans _
        (finiteHaarCell blockCount term head +
          (finiteHaarRow blockCount term tail +
            finiteHaarRow blockCount term right)) _
        (Q'.add_eqv_congr_left _ _ _
          (finiteHaarRow_append blockCount term tail right)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem finiteHaarBilinear_append_left
    (blockCount : Nat) : ∀ left right target : RatPoly,
    finiteHaarBilinear blockCount (left ++ right) target ≈
      finiteHaarBilinear blockCount left target +
        finiteHaarBilinear blockCount right target
  | [], right, target => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | term :: polynomial, right, target => by
      change
        finiteHaarRow blockCount term target +
            finiteHaarBilinear blockCount (polynomial ++ right) target ≈
          (finiteHaarRow blockCount term target +
              finiteHaarBilinear blockCount polynomial target) +
            finiteHaarBilinear blockCount right target
      refine Q'.eqv_trans _
        (finiteHaarRow blockCount term target +
          (finiteHaarBilinear blockCount polynomial target +
            finiteHaarBilinear blockCount right target)) _
        (Q'.add_eqv_congr_left _ _ _
          (finiteHaarBilinear_append_left
            blockCount polynomial right target)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem finiteHaarBilinear_append_right
    (blockCount : Nat) (source : RatPoly) : ∀ left right : RatPoly,
    finiteHaarBilinear blockCount source (left ++ right) ≈
      finiteHaarBilinear blockCount source left +
        finiteHaarBilinear blockCount source right
  | left, right => by
      refine Q'.eqv_trans _
        (finiteHaarBilinear blockCount (left ++ right) source) _
        (finiteHaarBilinear_symm blockCount source (left ++ right)) ?_
      refine Q'.eqv_trans _
        (finiteHaarBilinear blockCount left source +
          finiteHaarBilinear blockCount right source) _
        (finiteHaarBilinear_append_left
          blockCount left right source) ?_
      exact QPoly.q_add_congr
        (finiteHaarBilinear_symm blockCount left source)
        (finiteHaarBilinear_symm blockCount right source)

private def finiteHaarTripleCell
    (blockCount : Nat) (first second third : RatTerm) : Q' :=
  ((first.2 * second.2) * third.2) *
    finiteProductHaarMono blockCount
      (monoMul (monoMul first.1 second.1) third.1)

private def finiteHaarTripleLast
    (blockCount : Nat) (first second : RatTerm) : RatPoly → Q'
  | [] => 0
  | third :: remainder =>
      finiteHaarTripleCell blockCount first second third +
        finiteHaarTripleLast blockCount first second remainder

private def finiteHaarTripleMiddle
    (blockCount : Nat) (first : RatTerm) : RatPoly → RatPoly → Q'
  | [], _ => 0
  | second :: polynomial, target =>
      finiteHaarTripleLast blockCount first second target +
        finiteHaarTripleMiddle blockCount first polynomial target

private def finiteHaarTriple
    (blockCount : Nat) : RatPoly → RatPoly → RatPoly → Q'
  | [], _, _ => 0
  | first :: polynomial, middle, target =>
      finiteHaarTripleMiddle blockCount first middle target +
        finiteHaarTriple blockCount polynomial middle target

private theorem finiteHaarRow_generated
    (blockCount : Nat) (first second : RatTerm) : ∀ target : RatPoly,
    finiteHaarRow blockCount
        (monoMul first.1 second.1, first.2 * second.2) target ≈
      finiteHaarTripleLast blockCount first second target
  | [] => Q'.eqv_refl 0
  | third :: remainder => by
      change
        finiteHaarTripleCell blockCount first second third +
            finiteHaarRow blockCount
              (monoMul first.1 second.1, first.2 * second.2) remainder ≈
          finiteHaarTripleCell blockCount first second third +
            finiteHaarTripleLast blockCount first second remainder
      exact Q'.add_eqv_congr_left _ _ _
        (finiteHaarRow_generated blockCount first second remainder)

private theorem finiteHaarBilinear_generated
    (blockCount : Nat) (first : RatTerm) : ∀ middle target : RatPoly,
    finiteHaarBilinear blockCount
        (middle.map fun second =>
          (monoMul first.1 second.1, first.2 * second.2)) target ≈
      finiteHaarTripleMiddle blockCount first middle target
  | [], _ => Q'.eqv_refl 0
  | second :: polynomial, target =>
      QPoly.q_add_congr
        (finiteHaarRow_generated blockCount first second target)
        (finiteHaarBilinear_generated
          blockCount first polynomial target)

private theorem finiteHaarBilinear_polyMul_left
    (blockCount : Nat) : ∀ first middle target : RatPoly,
    finiteHaarBilinear blockCount (polyMul first middle) target ≈
      finiteHaarTriple blockCount first middle target
  | [], _, _ => Q'.eqv_refl 0
  | first :: polynomial, middle, target => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (finiteHaarBilinear blockCount
            (middle.map fun second =>
              (monoMul first.1 second.1, first.2 * second.2)) target +
          finiteHaarBilinear blockCount
            (polyMul polynomial middle) target) _
        (finiteHaarBilinear_append_left blockCount _ _ target) ?_
      exact QPoly.q_add_congr
        (finiteHaarBilinear_generated
          blockCount first middle target)
        (finiteHaarBilinear_polyMul_left
          blockCount polynomial middle target)

private theorem finiteHaarCell_right_assoc
    (blockCount : Nat) (first second third : RatTerm) :
    finiteHaarCell blockCount first
        (monoMul second.1 third.1, second.2 * third.2) ≈
      finiteHaarTripleCell blockCount first second third := by
  unfold finiteHaarCell finiteHaarTripleCell
  rw [← monoMul_assoc first.1 second.1 third.1]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv first.2 second.2 third.2))

private theorem finiteHaarRow_map_right
    (blockCount : Nat) (first second : RatTerm) : ∀ target : RatPoly,
    finiteHaarRow blockCount first
        (target.map fun third =>
          (monoMul second.1 third.1, second.2 * third.2)) ≈
      finiteHaarTripleLast blockCount first second target
  | [] => Q'.eqv_refl 0
  | third :: remainder =>
      QPoly.q_add_congr
        (finiteHaarCell_right_assoc blockCount first second third)
        (finiteHaarRow_map_right
          blockCount first second remainder)

private theorem finiteHaarRow_polyMul_right
    (blockCount : Nat) (first : RatTerm) : ∀ middle target : RatPoly,
    finiteHaarRow blockCount first (polyMul middle target) ≈
      finiteHaarTripleMiddle blockCount first middle target
  | [], _ => Q'.eqv_refl 0
  | second :: polynomial, target => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (finiteHaarRow blockCount first
            (target.map fun third =>
              (monoMul second.1 third.1, second.2 * third.2)) +
          finiteHaarRow blockCount first
            (polyMul polynomial target)) _
        (finiteHaarRow_append blockCount first _ _) ?_
      exact QPoly.q_add_congr
        (finiteHaarRow_map_right blockCount first second target)
        (finiteHaarRow_polyMul_right
          blockCount first polynomial target)

private theorem finiteHaarBilinear_polyMul_right
    (blockCount : Nat) : ∀ first middle target : RatPoly,
    finiteHaarBilinear blockCount first (polyMul middle target) ≈
      finiteHaarTriple blockCount first middle target
  | [], _, _ => Q'.eqv_refl 0
  | first :: polynomial, middle, target =>
      QPoly.q_add_congr
        (finiteHaarRow_polyMul_right
          blockCount first middle target)
        (finiteHaarBilinear_polyMul_right
          blockCount polynomial middle target)

private theorem finiteHaarTripleCell_swap_last
    (blockCount : Nat) (first second third : RatTerm) :
    finiteHaarTripleCell blockCount first second third ≈
      finiteHaarTripleCell blockCount first third second := by
  unfold finiteHaarTripleCell
  have hmonomial :
      monoMul (monoMul first.1 second.1) third.1 =
        monoMul (monoMul first.1 third.1) second.1 := by
    rw [monoMul_assoc, monoMul_comm second.1 third.1,
      ← monoMul_assoc]
  rw [hmonomial]
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  refine Q'.eqv_trans _ (first.2 * (second.2 * third.2)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (first.2 * (third.2 * second.2)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

private theorem finiteHaarTripleMiddle_nil_right
    (blockCount : Nat) (first : RatTerm) : ∀ middle : RatPoly,
    finiteHaarTripleMiddle blockCount first middle [] ≈ 0
  | [] => Q'.eqv_refl 0
  | _ :: middle =>
      Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr_left 0 _ _
          (finiteHaarTripleMiddle_nil_right
            blockCount first middle))
        (QPoly.q_zero_add_eqv 0)

private theorem finiteHaarTripleMiddle_swap
    (blockCount : Nat) (first : RatTerm) : ∀ middle target : RatPoly,
    finiteHaarTripleMiddle blockCount first middle target ≈
      finiteHaarTripleMiddle blockCount first target middle
  | [], target => Q'.eqv_symm
      (finiteHaarTripleMiddle_nil_right blockCount first target)
  | second :: polynomial, [] =>
      finiteHaarTripleMiddle_nil_right
        blockCount first (second :: polynomial)
  | second :: polynomial, third :: remainder => by
      change
        (finiteHaarTripleCell blockCount first second third +
            finiteHaarTripleLast blockCount first second remainder) +
          finiteHaarTripleMiddle blockCount first polynomial
            (third :: remainder) ≈
        (finiteHaarTripleCell blockCount first third second +
            finiteHaarTripleLast blockCount first third polynomial) +
          finiteHaarTripleMiddle blockCount first remainder
            (second :: polynomial)
      refine Q'.eqv_trans _
        ((finiteHaarTripleCell blockCount first second third +
            finiteHaarTripleLast blockCount first second remainder) +
          (finiteHaarTripleLast blockCount first third polynomial +
            finiteHaarTripleMiddle blockCount first remainder polynomial)) _
        (Q'.add_eqv_congr_left _ _ _ (by
          simpa [finiteHaarTripleMiddle] using
            finiteHaarTripleMiddle_swap blockCount first polynomial
              (third :: remainder))) ?_
      refine Q'.eqv_trans _
        ((finiteHaarTripleCell blockCount first third second +
            finiteHaarTripleLast blockCount first second remainder) +
          (finiteHaarTripleLast blockCount first third polynomial +
            finiteHaarTripleMiddle blockCount first polynomial remainder)) _
        (QPoly.q_add_congr
          (Q'.add_eqv_congr_right _ _ _
            (finiteHaarTripleCell_swap_last
              blockCount first second third))
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm
              (finiteHaarTripleMiddle_swap
                blockCount first polynomial remainder)))) ?_
      refine Q'.eqv_trans _
        ((finiteHaarTripleCell blockCount first third second +
            finiteHaarTripleLast blockCount first third polynomial) +
          (finiteHaarTripleLast blockCount first second remainder +
            finiteHaarTripleMiddle blockCount first polynomial remainder)) _
        (QPoly.q_interchange _ _ _ _) ?_
      exact Q'.add_eqv_congr_left _ _ _ (by
        simpa [finiteHaarTripleMiddle] using
          finiteHaarTripleMiddle_swap blockCount first
            (second :: polynomial) remainder)

private theorem finiteHaarTriple_swap_last
    (blockCount : Nat) : ∀ first middle target : RatPoly,
    finiteHaarTriple blockCount first middle target ≈
      finiteHaarTriple blockCount first target middle
  | [], _, _ => Q'.eqv_refl 0
  | first :: polynomial, middle, target =>
      QPoly.q_add_congr
        (finiteHaarTripleMiddle_swap
          blockCount first middle target)
        (finiteHaarTriple_swap_last
          blockCount polynomial middle target)

/-- The last two factors of a raw triple product may be exchanged under the
arbitrary finite-product Haar functional. -/
theorem finiteProductHaar_polyMul_middle_comm
    (blockCount : Nat) (first middle target : RatPoly) :
    finiteProductHaar blockCount
        (polyMul first (polyMul middle target)) ≈
      finiteProductHaar blockCount
        (polyMul first (polyMul target middle)) := by
  refine Q'.eqv_trans _
    (finiteHaarBilinear blockCount first
      (polyMul middle target)) _
    (finiteProductHaar_polyMul_eq_bilinear
      blockCount first (polyMul middle target)) ?_
  refine Q'.eqv_trans _
    (finiteHaarTriple blockCount first middle target) _
    (finiteHaarBilinear_polyMul_right
      blockCount first middle target) ?_
  refine Q'.eqv_trans _
    (finiteHaarTriple blockCount first target middle) _
    (finiteHaarTriple_swap_last
      blockCount first middle target) ?_
  refine Q'.eqv_trans _
    (finiteHaarBilinear blockCount first
      (polyMul target middle)) _
    (Q'.eqv_symm
      (finiteHaarBilinear_polyMul_right
        blockCount first target middle)) ?_
  exact Q'.eqv_symm
    (finiteProductHaar_polyMul_eq_bilinear
      blockCount first (polyMul target middle))

/-- Raw polynomial multiplication is associative under the arbitrary
finite-product Haar functional. -/
theorem finiteProductHaar_polyMul_assoc
    (blockCount : Nat) (first middle target : RatPoly) :
    finiteProductHaar blockCount
        (polyMul (polyMul first middle) target) ≈
      finiteProductHaar blockCount
        (polyMul first (polyMul middle target)) := by
  refine Q'.eqv_trans _
    (finiteHaarBilinear blockCount
      (polyMul first middle) target) _
    (finiteProductHaar_polyMul_eq_bilinear
      blockCount (polyMul first middle) target) ?_
  refine Q'.eqv_trans _
    (finiteHaarTriple blockCount first middle target) _
    (finiteHaarBilinear_polyMul_left
      blockCount first middle target) ?_
  refine Q'.eqv_trans _
    (finiteHaarBilinear blockCount first
      (polyMul middle target)) _
    (Q'.eqv_symm
      (finiteHaarBilinear_polyMul_right
        blockCount first middle target)) ?_
  exact Q'.eqv_symm
    (finiteProductHaar_polyMul_eq_bilinear
      blockCount first (polyMul middle target))

/-! ## 1.1 Four-linear contextual exchange -/

private theorem finiteMonoMul_four_swap
    (first second third fourth : List Nat) :
    monoMul (monoMul first second) (monoMul third fourth) =
      monoMul (monoMul first third) (monoMul second fourth) := by
  calc
    monoMul (monoMul first second) (monoMul third fourth) =
        monoMul first (monoMul second (monoMul third fourth)) :=
      monoMul_assoc first second (monoMul third fourth)
    _ = monoMul first (monoMul (monoMul second third) fourth) := by
      rw [monoMul_assoc second third fourth]
    _ = monoMul first (monoMul (monoMul third second) fourth) := by
      rw [monoMul_comm second third]
    _ = monoMul first (monoMul third (monoMul second fourth)) := by
      rw [monoMul_assoc third second fourth]
    _ = monoMul (monoMul first third) (monoMul second fourth) := by
      rw [monoMul_assoc first third (monoMul second fourth)]

private def finiteHaarTermMul (left right : RatTerm) : RatTerm :=
  (monoMul left.1 right.1, left.2 * right.2)

private def finiteHaarQuadCell
    (blockCount : Nat) (first second third fourth : RatTerm) : Q' :=
  ((first.2 * second.2) * (third.2 * fourth.2)) *
    finiteProductHaarMono blockCount
      (monoMul (monoMul first.1 second.1)
        (monoMul third.1 fourth.1))

private def finiteHaarQuadLast
    (blockCount : Nat) (first second third : RatTerm) : RatPoly → Q'
  | [] => 0
  | fourth :: remainder =>
      finiteHaarQuadCell blockCount first second third fourth +
        finiteHaarQuadLast blockCount first second third remainder

private def finiteHaarQuadThird
    (blockCount : Nat) (first second : RatTerm) :
    RatPoly → RatPoly → Q'
  | [], _ => 0
  | third :: polynomial, target =>
      finiteHaarQuadLast blockCount first second third target +
        finiteHaarQuadThird blockCount first second polynomial target

private def finiteHaarQuadSecond
    (blockCount : Nat) (first : RatTerm) :
    RatPoly → RatPoly → RatPoly → Q'
  | [], _, _ => 0
  | second :: polynomial, middle, target =>
      finiteHaarQuadThird blockCount first second middle target +
        finiteHaarQuadSecond blockCount first polynomial middle target

private def finiteHaarQuad
    (blockCount : Nat) :
    RatPoly → RatPoly → RatPoly → RatPoly → Q'
  | [], _, _, _ => 0
  | first :: polynomial, second, third, fourth =>
      finiteHaarQuadSecond blockCount first second third fourth +
        finiteHaarQuad blockCount polynomial second third fourth

private theorem finiteHaarRow_single_polyMul_quad
    (blockCount : Nat) (first second third : RatTerm) :
    ∀ fourth : RatPoly,
    finiteHaarRow blockCount (finiteHaarTermMul first second)
        (polyMul [third] fourth) ≈
      finiteHaarQuadLast blockCount first second third fourth
  | [] => Q'.eqv_refl 0
  | fourth :: remainder => by
      change
        finiteHaarQuadCell blockCount first second third fourth +
            finiteHaarRow blockCount (finiteHaarTermMul first second)
              (polyMul [third] remainder) ≈
          finiteHaarQuadCell blockCount first second third fourth +
            finiteHaarQuadLast blockCount first second third remainder
      exact Q'.add_eqv_congr_left _ _ _
        (finiteHaarRow_single_polyMul_quad
          blockCount first second third remainder)

private theorem finiteHaarRow_polyMul_quad
    (blockCount : Nat) (first second : RatTerm) :
    ∀ third fourth : RatPoly,
    finiteHaarRow blockCount (finiteHaarTermMul first second)
        (polyMul third fourth) ≈
      finiteHaarQuadThird blockCount first second third fourth
  | [], _ => Q'.eqv_refl 0
  | third :: polynomial, fourth => by
      have hmul :
          polyMul (third :: polynomial) fourth =
            polyMul [third] fourth ++ polyMul polynomial fourth := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (finiteHaarRow blockCount (finiteHaarTermMul first second)
            (polyMul [third] fourth) +
          finiteHaarRow blockCount (finiteHaarTermMul first second)
            (polyMul polynomial fourth)) _
        (finiteHaarRow_append blockCount _ _ _) ?_
      exact QPoly.q_add_congr
        (finiteHaarRow_single_polyMul_quad
          blockCount first second third fourth)
        (finiteHaarRow_polyMul_quad
          blockCount first second polynomial fourth)

private theorem finiteHaarBilinear_single_polyMul_quad
    (blockCount : Nat) (first : RatTerm) :
    ∀ second third fourth : RatPoly,
    finiteHaarBilinear blockCount (polyMul [first] second)
        (polyMul third fourth) ≈
      finiteHaarQuadSecond blockCount first second third fourth
  | [], _, _ => Q'.eqv_refl 0
  | second :: polynomial, third, fourth => by
      change
        finiteHaarRow blockCount (finiteHaarTermMul first second)
              (polyMul third fourth) +
            finiteHaarBilinear blockCount (polyMul [first] polynomial)
              (polyMul third fourth) ≈
          finiteHaarQuadThird blockCount first second third fourth +
            finiteHaarQuadSecond blockCount first polynomial third fourth
      exact QPoly.q_add_congr
        (finiteHaarRow_polyMul_quad
          blockCount first second third fourth)
        (finiteHaarBilinear_single_polyMul_quad
          blockCount first polynomial third fourth)

private theorem finiteHaarBilinear_polyMul_both_quad
    (blockCount : Nat) : ∀ first second third fourth : RatPoly,
    finiteHaarBilinear blockCount (polyMul first second)
        (polyMul third fourth) ≈
      finiteHaarQuad blockCount first second third fourth
  | [], _, _, _ => Q'.eqv_refl 0
  | first :: polynomial, second, third, fourth => by
      have hmul :
          polyMul (first :: polynomial) second =
            polyMul [first] second ++ polyMul polynomial second := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (finiteHaarBilinear blockCount (polyMul [first] second)
            (polyMul third fourth) +
          finiteHaarBilinear blockCount (polyMul polynomial second)
            (polyMul third fourth)) _
        (finiteHaarBilinear_append_left blockCount _ _ _) ?_
      exact QPoly.q_add_congr
        (finiteHaarBilinear_single_polyMul_quad
          blockCount first second third fourth)
        (finiteHaarBilinear_polyMul_both_quad
          blockCount polynomial second third fourth)

private theorem finiteProductHaar_four_eq_quad
    (blockCount : Nat) (first second third fourth : RatPoly) :
    finiteProductHaar blockCount
        (polyMul (polyMul first second) (polyMul third fourth)) ≈
      finiteHaarQuad blockCount first second third fourth :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_polyMul_eq_bilinear blockCount
      (polyMul first second) (polyMul third fourth))
    (finiteHaarBilinear_polyMul_both_quad
      blockCount first second third fourth)

private theorem finiteHaarQuadCell_swap
    (blockCount : Nat) (first second third fourth : RatTerm) :
    finiteHaarQuadCell blockCount first second third fourth ≈
      finiteHaarQuadCell blockCount first third second fourth := by
  unfold finiteHaarQuadCell
  rw [finiteMonoMul_four_swap
    first.1 second.1 third.1 fourth.1]
  exact Q'.mul_eqv_congr_right _ _ _
    (q_mul4_swap first.2 second.2 third.2 fourth.2)

private theorem finiteHaarQuadLast_swap
    (blockCount : Nat) (first second third : RatTerm) :
    ∀ fourth : RatPoly,
    finiteHaarQuadLast blockCount first second third fourth ≈
      finiteHaarQuadLast blockCount first third second fourth
  | [] => Q'.eqv_refl 0
  | fourth :: remainder =>
      QPoly.q_add_congr
        (finiteHaarQuadCell_swap
          blockCount first second third fourth)
        (finiteHaarQuadLast_swap
          blockCount first second third remainder)

private theorem finiteHaarQuadThird_single
    (blockCount : Nat) (first second third : RatTerm)
    (fourth : RatPoly) :
    finiteHaarQuadThird blockCount first second [third] fourth ≈
      finiteHaarQuadLast blockCount first second third fourth := by
  change
    finiteHaarQuadLast blockCount first second third fourth + 0 ≈
      finiteHaarQuadLast blockCount first second third fourth
  exact QPoly.q_add_zero_eqv _

private theorem finiteHaarQuadThird_append
    (blockCount : Nat) (first second : RatTerm) :
    ∀ third third' fourth : RatPoly,
    finiteHaarQuadThird blockCount first second
        (third ++ third') fourth ≈
      finiteHaarQuadThird blockCount first second third fourth +
        finiteHaarQuadThird blockCount first second third' fourth
  | [], third', fourth => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | third :: polynomial, third', fourth => by
      change
        finiteHaarQuadLast blockCount first second third fourth +
            finiteHaarQuadThird blockCount first second
              (polynomial ++ third') fourth ≈
          (finiteHaarQuadLast blockCount first second third fourth +
              finiteHaarQuadThird blockCount first second polynomial fourth) +
            finiteHaarQuadThird blockCount first second third' fourth
      refine Q'.eqv_trans _
        (finiteHaarQuadLast blockCount first second third fourth +
          (finiteHaarQuadThird blockCount first second polynomial fourth +
            finiteHaarQuadThird blockCount first second third' fourth)) _
        (Q'.add_eqv_congr_left _ _ _
          (finiteHaarQuadThird_append blockCount first second
            polynomial third' fourth)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem finiteHaar_q_add4_swap (first second third fourth : Q') :
    (first + second) + (third + fourth) ≈
      (first + third) + (second + fourth) := by
  refine Q'.eqv_trans _ (first + (second + (third + fourth))) _
    (Q'.add_assoc_eqv first second (third + fourth)) ?_
  refine Q'.eqv_trans _ (first + ((second + third) + fourth)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv second third fourth))) ?_
  refine Q'.eqv_trans _ (first + ((third + second) + fourth)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_comm_eqv second third))) ?_
  refine Q'.eqv_trans _ (first + (third + (second + fourth))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_assoc_eqv third second fourth)) ?_
  exact Q'.eqv_symm
    (Q'.add_assoc_eqv first third (second + fourth))

private theorem finiteHaarQuadSecond_third_append
    (blockCount : Nat) (first : RatTerm) :
    ∀ second third third' fourth : RatPoly,
    finiteHaarQuadSecond blockCount first second
        (third ++ third') fourth ≈
      finiteHaarQuadSecond blockCount first second third fourth +
        finiteHaarQuadSecond blockCount first second third' fourth
  | [], _, _, _ => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | second :: polynomial, third, third', fourth => by
      refine Q'.eqv_trans _
        ((finiteHaarQuadThird blockCount first second third fourth +
            finiteHaarQuadThird blockCount first second third' fourth) +
          (finiteHaarQuadSecond blockCount first polynomial third fourth +
            finiteHaarQuadSecond blockCount first polynomial third' fourth)) _
        (QPoly.q_add_congr
          (finiteHaarQuadThird_append blockCount first second
            third third' fourth)
          (finiteHaarQuadSecond_third_append blockCount first
            polynomial third third' fourth)) ?_
      exact finiteHaar_q_add4_swap _ _ _ _

private theorem finiteHaarQuadThird_swap_to_second
    (blockCount : Nat) (first second : RatTerm) :
    ∀ third fourth : RatPoly,
    finiteHaarQuadThird blockCount first second third fourth ≈
      finiteHaarQuadSecond blockCount first third [second] fourth
  | [], _ => Q'.eqv_refl 0
  | third :: polynomial, fourth => by
      refine Q'.eqv_trans _
        (finiteHaarQuadLast blockCount first third second fourth +
          finiteHaarQuadSecond blockCount first polynomial [second] fourth) _
        (QPoly.q_add_congr
          (finiteHaarQuadLast_swap
            blockCount first second third fourth)
          (finiteHaarQuadThird_swap_to_second
            blockCount first second polynomial fourth)) ?_
      exact Q'.eqv_symm
        (QPoly.q_add_congr
          (finiteHaarQuadThird_single
            blockCount first third second fourth)
          (Q'.eqv_refl _))

private theorem finiteHaarQuadSecond_third_nil
    (blockCount : Nat) (first : RatTerm) :
    ∀ third fourth : RatPoly,
    finiteHaarQuadSecond blockCount first third [] fourth ≈ 0
  | [], _ => Q'.eqv_refl 0
  | third :: polynomial, fourth => by
      change
        0 + finiteHaarQuadSecond blockCount first polynomial [] fourth ≈ 0
      refine Q'.eqv_trans _
        (finiteHaarQuadSecond blockCount first polynomial [] fourth) _
        (QPoly.q_zero_add_eqv _) ?_
      exact finiteHaarQuadSecond_third_nil
        blockCount first polynomial fourth

private theorem finiteHaarQuadSecond_swap
    (blockCount : Nat) (first : RatTerm) :
    ∀ second third fourth : RatPoly,
    finiteHaarQuadSecond blockCount first second third fourth ≈
      finiteHaarQuadSecond blockCount first third second fourth
  | [], third, fourth =>
      Q'.eqv_symm
        (finiteHaarQuadSecond_third_nil blockCount first third fourth)
  | second :: polynomial, third, fourth => by
      refine Q'.eqv_trans _
        (finiteHaarQuadSecond blockCount first third [second] fourth +
          finiteHaarQuadSecond blockCount first third polynomial fourth) _
        (QPoly.q_add_congr
          (finiteHaarQuadThird_swap_to_second
            blockCount first second third fourth)
          (finiteHaarQuadSecond_swap
            blockCount first polynomial third fourth)) ?_
      exact Q'.eqv_symm
        (finiteHaarQuadSecond_third_append blockCount first
          third [second] polynomial fourth)

private theorem finiteHaarQuad_swap
    (blockCount : Nat) : ∀ first second third fourth : RatPoly,
    finiteHaarQuad blockCount first second third fourth ≈
      finiteHaarQuad blockCount first third second fourth
  | [], _, _, _ => Q'.eqv_refl 0
  | first :: polynomial, second, third, fourth =>
      QPoly.q_add_congr
        (finiteHaarQuadSecond_swap
          blockCount first second third fourth)
        (finiteHaarQuad_swap
          blockCount polynomial second third fourth)

/-- **Four-factor exchange under arbitrary finite-product Haar.**  The two
middle raw polynomial factors may be exchanged inside the displayed paired
parenthesization.  This is the contextual atom that pair/triple Haar laws do
not supply by themselves. -/
theorem finiteProductHaar_polyMul_four_swap
    (blockCount : Nat) (first second third fourth : RatPoly) :
    finiteProductHaar blockCount
        (polyMul (polyMul first second) (polyMul third fourth)) ≈
      finiteProductHaar blockCount
        (polyMul (polyMul first third) (polyMul second fourth)) :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_four_eq_quad
      blockCount first second third fourth)
    (Q'.eqv_trans _ _ _
      (finiteHaarQuad_swap
        blockCount first second third fourth)
      (Q'.eqv_symm
        (finiteProductHaar_four_eq_quad
          blockCount first third second fourth)))

/-! ## 2. Lazy one-block radius schedules and Haar invariance -/

/-- Repeated right multiplication by the radius polynomial of one block.
The recursion is symbolic in the exponent. -/
def blockRadiusIter (block : Nat) : Nat → RatPoly → RatPoly
  | 0, polynomial => polynomial
  | iterations + 1, polynomial =>
      polyMul (blockRadiusIter block iterations polynomial)
        (quaternionBlockRadiusPolynomial block)

theorem finiteProductHaar_blockRadiusIter
    (blockCount block : Nat) (hblock : block < blockCount)
    (polynomial : RatPoly) : ∀ iterations : Nat,
    finiteProductHaar blockCount
        (blockRadiusIter block iterations polynomial) ≈
      finiteProductHaar blockCount polynomial
  | 0 => Q'.eqv_refl _
  | iterations + 1 =>
      Q'.eqv_trans _ _ _
        (finiteProductHaar_mul_blockRadius
          blockCount block hblock
          (blockRadiusIter block iterations polynomial))
        (finiteProductHaar_blockRadiusIter
          blockCount block hblock polynomial iterations)

private theorem finiteProductHaar_blockRadius_step_pair
    (blockCount block : Nat) (hblock : block < blockCount)
    (left right : RatPoly) :
    finiteProductHaar blockCount
        (polyMul
          (polyMul left (quaternionBlockRadiusPolynomial block)) right) ≈
      finiteProductHaar blockCount (polyMul left right) := by
  refine Q'.eqv_trans _
    (finiteProductHaar blockCount
      (polyMul left
        (polyMul (quaternionBlockRadiusPolynomial block) right))) _
    (finiteProductHaar_polyMul_assoc blockCount left
      (quaternionBlockRadiusPolynomial block) right) ?_
  refine Q'.eqv_trans _
    (finiteProductHaar blockCount
      (polyMul left
        (polyMul right (quaternionBlockRadiusPolynomial block)))) _
    (finiteProductHaar_polyMul_middle_comm blockCount left
      (quaternionBlockRadiusPolynomial block) right) ?_
  refine Q'.eqv_trans _
    (finiteProductHaar blockCount
      (polyMul (polyMul left right)
        (quaternionBlockRadiusPolynomial block))) _
    (Q'.eqv_symm
      (finiteProductHaar_polyMul_assoc blockCount left right
        (quaternionBlockRadiusPolynomial block))) ?_
  exact finiteProductHaar_mul_blockRadius
    blockCount block hblock (polyMul left right)

theorem finiteProductHaar_blockRadiusIter_pair
    (blockCount block : Nat) (hblock : block < blockCount)
    (left right : RatPoly) : ∀ iterations : Nat,
    finiteProductHaar blockCount
        (polyMul (blockRadiusIter block iterations left) right) ≈
      finiteProductHaar blockCount (polyMul left right)
  | 0 => Q'.eqv_refl _
  | iterations + 1 =>
      Q'.eqv_trans _ _ _
        (finiteProductHaar_blockRadius_step_pair
          blockCount block hblock
          (blockRadiusIter block iterations left) right)
        (finiteProductHaar_blockRadiusIter_pair
          blockCount block hblock left right iterations)

/-! ## 3. Structural support, parity, and degree invariants -/

private theorem mem_polyMul
    {left right : RatPoly} {term : RatTerm}
    (hterm : term ∈ polyMul left right) :
    ∃ leftTerm, leftTerm ∈ left ∧
      ∃ rightTerm, rightTerm ∈ right ∧
        term =
          (monoMul leftTerm.1 rightTerm.1,
            leftTerm.2 * rightTerm.2) := by
  unfold polyMul at hterm
  rw [List.mem_flatMap] at hterm
  obtain ⟨leftTerm, hleftTerm, hterm⟩ := hterm
  rw [List.mem_map] at hterm
  obtain ⟨rightTerm, hrightTerm, rfl⟩ := hterm
  exact ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, rfl⟩

private theorem monoMul_length_le
    {boundary : Nat} {left right : List Nat}
    (hleft : left.length ≤ boundary)
    (hright : right.length ≤ boundary) :
    (monoMul left right).length ≤ boundary := by
  apply List.drop_eq_nil_iff.mp
  rw [monoMul_drop_of_right_length_le left right boundary hright]
  exact List.drop_eq_nil_of_le hleft

private theorem supportedQuaternionBlocks_polyMul
    {blockCount : Nat} {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks blockCount left)
    (hright : SupportedQuaternionBlocks blockCount right) :
    SupportedQuaternionBlocks blockCount (polyMul left right) := by
  intro term hterm
  obtain ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, rfl⟩ :=
    mem_polyMul hterm
  exact monoMul_length_le
    (hleft leftTerm hleftTerm) (hright rightTerm hrightTerm)

theorem quaternionBlockRadiusPolynomial_supported
    {blockCount block : Nat} (hblock : block < blockCount) :
    SupportedQuaternionBlocks blockCount
      (quaternionBlockRadiusPolynomial block) := by
  intro term hterm
  simp only [quaternionBlockRadiusPolynomial, List.mem_cons,
    List.not_mem_nil, or_false] at hterm
  rcases hterm with rfl | rfl | rfl | rfl <;>
    simp only [quaternionBlockSquareMonomial_length] <;> omega

@[simp] private theorem exponentAt_nil_safe (coordinate : Nat) :
    exponentAt [] coordinate = 0 := by
  unfold exponentAt
  exact List.getD_nil

@[simp] private theorem exponentAt_cons_zero_safe
    (head : Nat) (tail : List Nat) :
    exponentAt (head :: tail) 0 = head := by
  unfold exponentAt
  exact List.getD_cons_zero

@[simp] private theorem exponentAt_cons_succ_safe
    (head : Nat) (tail : List Nat) (coordinate : Nat) :
    exponentAt (head :: tail) (coordinate + 1) =
      exponentAt tail coordinate := by
  unfold exponentAt
  exact List.getD_cons_succ

/-- Choice-free coordinatewise exponent addition, proved only through the
public `List.getD` equations. -/
private theorem exponentAt_monoMul_safe
    (left right : List Nat) (coordinate : Nat) :
    exponentAt (monoMul left right) coordinate =
      exponentAt left coordinate + exponentAt right coordinate := by
  induction left generalizing right coordinate with
  | nil =>
      simp only [monoMul, exponentAt_nil_safe, Nat.zero_add]
  | cons head tail ih =>
      cases right with
      | nil =>
          simp only [monoMul, exponentAt_nil_safe, Nat.add_zero]
      | cons other rest =>
          cases coordinate with
          | zero =>
              simp only [monoMul, exponentAt_cons_zero_safe]
          | succ coordinate =>
              simp only [monoMul, exponentAt_cons_succ_safe]
              exact ih rest coordinate

/-- Choice-free Boolean profile of one sparse coordinate-square monomial. -/
def coordinateSquareExponent (coordinate query : Nat) : Nat :=
  if query == coordinate then 2 else 0

/-- Choice-free exact lookup in the sparse coordinate-square monomial. -/
private theorem exponentAt_coordinateSquareMonomial_safe
    (coordinate query : Nat) :
    exponentAt (coordinateSquareMonomial coordinate) query =
      coordinateSquareExponent coordinate query := by
  rw [exponentAt_coordinateSquareMonomial]
  cases Nat.decEq query coordinate with
  | isFalse hne =>
      rw [if_neg hne]
      unfold coordinateSquareExponent
      have hbeq : (query == coordinate) = false := by
        cases hquery : query == coordinate with
        | false => rfl
        | true =>
            exfalso
            exact hne ((beq_iff_eq).1 hquery)
      rw [hbeq]
      rw [if_neg (by decide)]
  | isTrue hsame =>
      rw [if_pos hsame]
      unfold coordinateSquareExponent
      have hbeq : (query == coordinate) = true :=
        (beq_iff_eq).2 hsame
      rw [hbeq]
      rw [if_pos rfl]

/-- Every scalar exponent in a block-radius monomial is even. -/
theorem quaternionBlockRadiusPolynomial_zeroParity
    (blockCount block : Nat) :
    AllFiniteQuaternionCoordinateParity blockCount (fun _ => 0)
      (quaternionBlockRadiusPolynomial block) := by
  intro term hterm coordinate hcoordinate
  simp only [quaternionBlockRadiusPolynomial, List.mem_cons,
    List.not_mem_nil, or_false] at hterm
  rcases hterm with rfl | rfl | rfl | rfl <;>
    simp [quaternionBlockSquareMonomial,
      exponentAt_coordinateSquareMonomial_safe,
      coordinateSquareExponent]
  all_goals split <;> decide

theorem quaternionBlockDegree_monoMul
    (block : Nat) (left right : List Nat) :
    quaternionBlockDegree block (monoMul left right) =
      quaternionBlockDegree block left +
        quaternionBlockDegree block right := by
  unfold quaternionBlockDegree
  simp only [exponentAt_monoMul_safe]
  omega

/-- Choice-free degree increment contributed by one radius term.  Boolean
equality keeps the data definition independent of proposition decidability. -/
def blockRadiusDegreeIncrement (source block : Nat) : Nat :=
  if source == block then 2 else 0

/-- One coordinate square contributes degree two in its own block and zero
in every other block. -/
theorem quaternionBlockDegree_squareMonomial
    (source target component : Nat) (hcomponent : component < 4) :
    quaternionBlockDegree source
        (quaternionBlockSquareMonomial target component) =
      blockRadiusDegreeIncrement source target := by
  cases hbeq : source == target with
  | false =>
    have hsame : source ≠ target := by
      intro hsame
      have htrue : (source == target) = true :=
        (beq_iff_eq).2 hsame
      rw [htrue] at hbeq
      exact Bool.noConfusion hbeq
    have h0 : 4 * source ≠ 4 * target + component := by omega
    have h1 : 4 * source + 1 ≠ 4 * target + component := by omega
    have h2 : 4 * source + 2 ≠ 4 * target + component := by omega
    have h3 : 4 * source + 3 ≠ 4 * target + component := by omega
    unfold quaternionBlockDegree quaternionBlockSquareMonomial
    rw [exponentAt_coordinateSquareMonomial,
      exponentAt_coordinateSquareMonomial,
      exponentAt_coordinateSquareMonomial,
      exponentAt_coordinateSquareMonomial]
    rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]
    unfold blockRadiusDegreeIncrement
    rw [hbeq]
    rw [if_neg (by decide)]
  | true =>
    have hsame : source = target := (beq_iff_eq).mp hbeq
    subst source
    have hincrement :
        blockRadiusDegreeIncrement target target = 2 := by
      unfold blockRadiusDegreeIncrement
      have hself : (target == target) = true :=
        (beq_iff_eq).2 rfl
      rw [hself]
      rw [if_pos rfl]
    rw [hincrement]
    have hcomponentCases :
        component = 0 ∨ component = 1 ∨
          component = 2 ∨ component = 3 := by
      omega
    rcases hcomponentCases with rfl | rfl | rfl | rfl
    all_goals
      unfold quaternionBlockDegree quaternionBlockSquareMonomial
      rw [exponentAt_coordinateSquareMonomial,
        exponentAt_coordinateSquareMonomial,
        exponentAt_coordinateSquareMonomial,
        exponentAt_coordinateSquareMonomial]
    · have h0 : 4 * target = 4 * target + 0 := by omega
      have h1 : 4 * target + 1 ≠ 4 * target + 0 := by omega
      have h2 : 4 * target + 2 ≠ 4 * target + 0 := by omega
      have h3 : 4 * target + 3 ≠ 4 * target + 0 := by omega
      rw [if_pos h0, if_neg h1, if_neg h2, if_neg h3]
    · have h0 : 4 * target ≠ 4 * target + 1 := by omega
      have h1 : 4 * target + 1 = 4 * target + 1 := rfl
      have h2 : 4 * target + 2 ≠ 4 * target + 1 := by omega
      have h3 : 4 * target + 3 ≠ 4 * target + 1 := by omega
      rw [if_neg h0, if_pos h1, if_neg h2, if_neg h3]
    · have h0 : 4 * target ≠ 4 * target + 2 := by omega
      have h1 : 4 * target + 1 ≠ 4 * target + 2 := by omega
      have h2 : 4 * target + 2 = 4 * target + 2 := rfl
      have h3 : 4 * target + 3 ≠ 4 * target + 2 := by omega
      rw [if_neg h0, if_neg h1, if_pos h2, if_neg h3]
    · have h0 : 4 * target ≠ 4 * target + 3 := by omega
      have h1 : 4 * target + 1 ≠ 4 * target + 3 := by omega
      have h2 : 4 * target + 2 ≠ 4 * target + 3 := by omega
      have h3 : 4 * target + 3 = 4 * target + 3 := rfl
      rw [if_neg h0, if_neg h1, if_neg h2, if_pos h3]

/-- Every literal term of a block radius has the same block-degree profile:
two in the selected block, zero elsewhere. -/
theorem quaternionBlockRadiusPolynomial_degrees
    (block : Nat) :
    ∀ term, term ∈ quaternionBlockRadiusPolynomial block →
      ∀ source,
        quaternionBlockDegree source term.1 =
          blockRadiusDegreeIncrement source block := by
  intro term hterm source
  simp only [quaternionBlockRadiusPolynomial, List.mem_cons,
    List.not_mem_nil, or_false] at hterm
  rcases hterm with rfl | rfl | rfl | rfl
  · exact quaternionBlockDegree_squareMonomial source block 0 (by omega)
  · exact quaternionBlockDegree_squareMonomial source block 1 (by omega)
  · exact quaternionBlockDegree_squareMonomial source block 2 (by omega)
  · exact quaternionBlockDegree_squareMonomial source block 3 (by omega)

/-- A degree profile over every block index, used internally to state the
inductive schedule invariant even for blocks not processed yet. -/
def AllQuaternionBlockDegreesEverywhere
    (degrees : Nat → Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial → ∀ block,
    quaternionBlockDegree block term.1 = degrees block

private theorem allQuaternionBlockDegreesEverywhere_polyMul
    {leftDegrees rightDegrees : Nat → Nat}
    {left right : RatPoly}
    (hleft : AllQuaternionBlockDegreesEverywhere leftDegrees left)
    (hright : AllQuaternionBlockDegreesEverywhere rightDegrees right) :
    AllQuaternionBlockDegreesEverywhere
      (fun block => leftDegrees block + rightDegrees block)
      (polyMul left right) := by
  intro term hterm block
  obtain ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, rfl⟩ :=
    mem_polyMul hterm
  rw [quaternionBlockDegree_monoMul,
    hleft leftTerm hleftTerm block,
    hright rightTerm hrightTerm block]

private theorem finiteParity_polyMul_zero
    {blockCount : Nat} {parities : Nat → Nat}
    {left right : RatPoly}
    (hleft :
      AllFiniteQuaternionCoordinateParity blockCount parities left)
    (hright :
      AllFiniteQuaternionCoordinateParity blockCount (fun _ => 0) right) :
    AllFiniteQuaternionCoordinateParity blockCount parities
      (polyMul left right) := by
  intro term hterm coordinate hcoordinate
  obtain ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, rfl⟩ :=
    mem_polyMul hterm
  have hp := hleft leftTerm hleftTerm coordinate hcoordinate
  have hz := hright rightTerm hrightTerm coordinate hcoordinate
  rw [exponentAt_monoMul_safe]
  rw [Nat.add_mod, hp, hz]
  simp only [Nat.add_zero]
  apply Nat.mod_eq_of_lt
  rw [← hp]
  exact Nat.mod_lt _ (by omega)

theorem blockRadiusIter_supported
    (blockCount block : Nat) (hblock : block < blockCount)
    {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blockCount polynomial) :
    ∀ iterations : Nat,
      SupportedQuaternionBlocks blockCount
        (blockRadiusIter block iterations polynomial)
  | 0 => hsupport
  | iterations + 1 =>
      supportedQuaternionBlocks_polyMul
        (blockRadiusIter_supported
          blockCount block hblock hsupport iterations)
        (quaternionBlockRadiusPolynomial_supported hblock)

theorem blockRadiusIter_parity
    (blockCount block : Nat) {parities : Nat → Nat}
    {polynomial : RatPoly}
    (hparity :
      AllFiniteQuaternionCoordinateParity blockCount parities polynomial) :
    ∀ iterations : Nat,
      AllFiniteQuaternionCoordinateParity blockCount parities
        (blockRadiusIter block iterations polynomial)
  | 0 => hparity
  | iterations + 1 =>
      finiteParity_polyMul_zero
        (blockRadiusIter_parity
          blockCount block hparity iterations)
        (quaternionBlockRadiusPolynomial_zeroParity blockCount block)

/-- Exact degree evolution under a symbolic power of one block radius. -/
theorem blockRadiusIter_degrees
    (block : Nat) {degrees : Nat → Nat} {polynomial : RatPoly}
    (hdegrees : AllQuaternionBlockDegreesEverywhere degrees polynomial) :
    ∀ iterations : Nat,
      AllQuaternionBlockDegreesEverywhere
        (fun source =>
          degrees source +
            iterations * blockRadiusDegreeIncrement source block)
        (blockRadiusIter block iterations polynomial)
  | 0 => by
      intro term hterm source
      simpa using hdegrees term hterm source
  | iterations + 1 => by
      intro term hterm source
      obtain ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, rfl⟩ :=
        mem_polyMul hterm
      rw [quaternionBlockDegree_monoMul,
        blockRadiusIter_degrees block hdegrees iterations
          leftTerm hleftTerm source,
        quaternionBlockRadiusPolynomial_degrees
          block rightTerm hrightTerm source]
      cases hbeq : source == block <;>
        simp [blockRadiusDegreeIncrement, hbeq] <;> omega

private theorem supportedQuaternionBlocks_append
    {blockCount : Nat} {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks blockCount left)
    (hright : SupportedQuaternionBlocks blockCount right) :
    SupportedQuaternionBlocks blockCount (left ++ right) := by
  intro term hterm
  simp only [List.mem_append] at hterm
  cases hterm with
  | inl hterm => exact hleft term hterm
  | inr hterm => exact hright term hterm

private theorem finiteParity_append
    {blockCount : Nat} {parities : Nat → Nat}
    {left right : RatPoly}
    (hleft :
      AllFiniteQuaternionCoordinateParity blockCount parities left)
    (hright :
      AllFiniteQuaternionCoordinateParity blockCount parities right) :
    AllFiniteQuaternionCoordinateParity blockCount parities
      (left ++ right) := by
  intro term hterm
  simp only [List.mem_append] at hterm
  cases hterm with
  | inl hterm => exact hleft term hterm
  | inr hterm => exact hright term hterm

private theorem finiteDegrees_append
    {blockCount : Nat} {degrees : Nat → Nat}
    {left right : RatPoly}
    (hleft : AllFiniteQuaternionBlockDegrees blockCount degrees left)
    (hright : AllFiniteQuaternionBlockDegrees blockCount degrees right) :
    AllFiniteQuaternionBlockDegrees blockCount degrees
      (left ++ right) := by
  intro term hterm
  simp only [List.mem_append] at hterm
  cases hterm with
  | inl hterm => exact hleft term hterm
  | inr hterm => exact hright term hterm

/-! ## 4. The block-recursive term homogenization schedule -/

/-- Number of radius-square insertions needed to raise one term to the target
degree in one block. -/
def blockRaiseCount
    (targets : Nat → Nat) (block : Nat) (term : RatTerm) : Nat :=
  (targets block - quaternionBlockDegree block term.1) / 2

/-- Process the first `processed` blocks of one term.  At successor step the
new block is `processed`; no list of blocks or exponents is constructed. -/
def homogenizeTermPrefix : Nat → (Nat → Nat) → RatTerm → RatPoly
  | 0, _, term => [term]
  | processed + 1, targets, term =>
      blockRadiusIter processed (blockRaiseCount targets processed term)
        (homogenizeTermPrefix processed targets term)

/-- Homogenize one term across the complete carried block prefix. -/
def homogenizeFiniteTerm
    (blockCount : Nat) (targets : Nat → Nat)
    (term : RatTerm) : RatPoly :=
  homogenizeTermPrefix blockCount targets term

private theorem singleton_supported
    {blockCount : Nat} {term : RatTerm}
    (hsupport : term.1.length ≤ 4 * blockCount) :
    SupportedQuaternionBlocks blockCount [term] := by
  intro source hsource
  have heq : source = term := by simpa using hsource
  subst source
  exact hsupport

private theorem singleton_parity
    {blockCount : Nat} {parities : Nat → Nat} {term : RatTerm}
    (hparity : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt term.1 coordinate % 2 = parities coordinate) :
    AllFiniteQuaternionCoordinateParity blockCount parities [term] := by
  intro source hsource
  have heq : source = term := by simpa using hsource
  subst source
  exact hparity

private theorem singleton_degreesEverywhere (term : RatTerm) :
    AllQuaternionBlockDegreesEverywhere
      (fun block => quaternionBlockDegree block term.1) [term] := by
  intro source hsource block
  have heq : source = term := by simpa using hsource
  subst source
  rfl

theorem homogenizeTermPrefix_supported
    (blockCount : Nat) (targets : Nat → Nat) (term : RatTerm)
    (hterm : term.1.length ≤ 4 * blockCount) :
    ∀ processed : Nat, processed ≤ blockCount →
      SupportedQuaternionBlocks blockCount
        (homogenizeTermPrefix processed targets term)
  | 0, _ => singleton_supported hterm
  | processed + 1, hprocessed =>
      blockRadiusIter_supported blockCount processed (by omega)
        (homogenizeTermPrefix_supported blockCount targets term hterm
          processed (by omega))
        (blockRaiseCount targets processed term)

theorem homogenizeFiniteTerm_supported
    (blockCount : Nat) (targets : Nat → Nat) (term : RatTerm)
    (hterm : term.1.length ≤ 4 * blockCount) :
    SupportedQuaternionBlocks blockCount
      (homogenizeFiniteTerm blockCount targets term) := by
  exact homogenizeTermPrefix_supported
    blockCount targets term hterm blockCount (Nat.le_refl _)

theorem homogenizeTermPrefix_parity
    (blockCount : Nat) (targets parities : Nat → Nat)
    (term : RatTerm)
    (hparity : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt term.1 coordinate % 2 = parities coordinate) :
    ∀ processed : Nat,
      AllFiniteQuaternionCoordinateParity blockCount parities
        (homogenizeTermPrefix processed targets term)
  | 0 => singleton_parity hparity
  | processed + 1 =>
      blockRadiusIter_parity blockCount processed
        (homogenizeTermPrefix_parity
          blockCount targets parities term hparity processed)
        (blockRaiseCount targets processed term)

theorem homogenizeFiniteTerm_parity
    (blockCount : Nat) (targets parities : Nat → Nat)
    (term : RatTerm)
    (hparity : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt term.1 coordinate % 2 = parities coordinate) :
    AllFiniteQuaternionCoordinateParity blockCount parities
      (homogenizeFiniteTerm blockCount targets term) :=
  homogenizeTermPrefix_parity
    blockCount targets parities term hparity blockCount

private theorem allQuaternionBlockDegreesEverywhere_congr
    {left right : Nat → Nat} {polynomial : RatPoly}
    (hleft : AllQuaternionBlockDegreesEverywhere left polynomial)
    (heq : ∀ block, left block = right block) :
    AllQuaternionBlockDegreesEverywhere right polynomial := by
  intro term hterm block
  exact (hleft term hterm block).trans (heq block)

/-- Exact schedule invariant: processed blocks have their target degrees;
every as-yet-unprocessed block retains the original term degree. -/
theorem homogenizeTermPrefix_degrees
    (targets : Nat → Nat) (term : RatTerm) : ∀ processed : Nat,
    (∀ block, block < processed →
      quaternionBlockDegree block term.1 ≤ targets block) →
    (∀ block, block < processed →
      (targets block - quaternionBlockDegree block term.1) % 2 = 0) →
    AllQuaternionBlockDegreesEverywhere
      (fun block =>
        if block < processed then targets block
        else quaternionBlockDegree block term.1)
      (homogenizeTermPrefix processed targets term)
  | 0, _, _ => by
      apply allQuaternionBlockDegreesEverywhere_congr
        (singleton_degreesEverywhere term)
      intro block
      have hzero : ¬ block < 0 := by omega
      rw [if_neg hzero]
  | processed + 1, hle, heven => by
      have hprevious := homogenizeTermPrefix_degrees targets term processed
        (fun block hblock => hle block (by omega))
        (fun block hblock => heven block (by omega))
      have hraised := blockRadiusIter_degrees processed hprevious
        (blockRaiseCount targets processed term)
      apply allQuaternionBlockDegreesEverywhere_congr hraised
      intro block
      by_cases hbefore : block < processed
      · have hne : block ≠ processed := by omega
        have hnext : block < processed + 1 := by omega
        have hbeq : (block == processed) = false := by
          cases hblock : block == processed with
          | false => rfl
          | true =>
              exfalso
              exact hne ((beq_iff_eq).1 hblock)
        have hincrement :
            blockRadiusDegreeIncrement block processed = 0 := by
          unfold blockRadiusDegreeIncrement
          rw [hbeq]
          rw [if_neg (by decide)]
        rw [if_pos hbefore, if_pos hnext, hincrement]
        rw [Nat.mul_zero, Nat.add_zero]
      · by_cases heq : block = processed
        · subst block
          have hleBlock := hle processed (by omega)
          have hevenBlock := heven processed (by omega)
          have hnotBefore : ¬ processed < processed := by omega
          have hnext : processed < processed + 1 := by omega
          have hbeq : (processed == processed) = true :=
            (beq_iff_eq).2 rfl
          have hincrement :
              blockRadiusDegreeIncrement processed processed = 2 := by
            unfold blockRadiusDegreeIncrement
            rw [hbeq]
            rw [if_pos rfl]
          rw [if_neg hnotBefore, if_pos hnext, hincrement]
          unfold blockRaiseCount
          omega
        · have hafter : ¬ block < processed + 1 := by omega
          have hbeq : (block == processed) = false := by
            cases hblock : block == processed with
            | false => rfl
            | true =>
                exfalso
                exact heq ((beq_iff_eq).1 hblock)
          have hincrement :
              blockRadiusDegreeIncrement block processed = 0 := by
            unfold blockRadiusDegreeIncrement
            rw [hbeq]
            rw [if_neg (by decide)]
          rw [if_neg hbefore, if_neg hafter, hincrement]
          rw [Nat.mul_zero, Nat.add_zero]

theorem homogenizeFiniteTerm_degrees
    (blockCount : Nat) (targets : Nat → Nat) (term : RatTerm)
    (hle : ∀ block, block < blockCount →
      quaternionBlockDegree block term.1 ≤ targets block)
    (heven : ∀ block, block < blockCount →
      (targets block - quaternionBlockDegree block term.1) % 2 = 0) :
    AllFiniteQuaternionBlockDegrees blockCount targets
      (homogenizeFiniteTerm blockCount targets term) := by
  have hall := homogenizeTermPrefix_degrees
    targets term blockCount hle heven
  intro source hsource block hblock
  have hdegree := hall source hsource block
  simpa [hblock] using hdegree

/-! ## 5. Haar invariance of the term and polynomial schedules -/

theorem finiteProductHaar_homogenizeTermPrefix_pair_left
    (blockCount : Nat) (targets : Nat → Nat)
    (term : RatTerm) (right : RatPoly) :
    ∀ processed : Nat, processed ≤ blockCount →
      finiteProductHaar blockCount
          (polyMul (homogenizeTermPrefix processed targets term) right) ≈
        finiteProductHaar blockCount (polyMul [term] right)
  | 0, _ => Q'.eqv_refl _
  | processed + 1, hprocessed =>
      Q'.eqv_trans _ _ _
        (finiteProductHaar_blockRadiusIter_pair
          blockCount processed (by omega)
          (homogenizeTermPrefix processed targets term) right
          (blockRaiseCount targets processed term))
        (finiteProductHaar_homogenizeTermPrefix_pair_left
          blockCount targets term right processed (by omega))

theorem finiteProductHaar_homogenizeFiniteTerm_pair
    (blockCount : Nat) (targets : Nat → Nat)
    (left right : RatTerm) :
    finiteProductHaar blockCount
        (polyMul (homogenizeFiniteTerm blockCount targets left)
          (homogenizeFiniteTerm blockCount targets right)) ≈
      finiteProductHaar blockCount (polyMul [left] [right]) := by
  refine Q'.eqv_trans _
    (finiteProductHaar blockCount
      (polyMul [left]
        (homogenizeFiniteTerm blockCount targets right))) _
    (finiteProductHaar_homogenizeTermPrefix_pair_left
      blockCount targets left
      (homogenizeFiniteTerm blockCount targets right)
      blockCount (Nat.le_refl _)) ?_
  refine Q'.eqv_trans _
    (finiteProductHaar blockCount
      (polyMul (homogenizeFiniteTerm blockCount targets right) [left])) _
    (finiteProductHaar_polyMul_comm blockCount [left]
      (homogenizeFiniteTerm blockCount targets right)) ?_
  refine Q'.eqv_trans _
    (finiteProductHaar blockCount (polyMul [right] [left])) _
    (finiteProductHaar_homogenizeTermPrefix_pair_left
      blockCount targets right [left]
      blockCount (Nat.le_refl _)) ?_
  exact finiteProductHaar_polyMul_comm blockCount [right] [left]

/-- Homogenize every literal term independently and concatenate the finite
results.  The recursion does not enumerate block-degree assignments. -/
def homogenizeFiniteParity
    (blockCount : Nat) (targets : Nat → Nat) : RatPoly → RatPoly
  | [] => []
  | term :: polynomial =>
      homogenizeFiniteTerm blockCount targets term ++
        homogenizeFiniteParity blockCount targets polynomial

private theorem finiteProductHaar_polyMul_append_left
    (blockCount : Nat) (left right target : RatPoly) :
    finiteProductHaar blockCount (polyMul (left ++ right) target) ≈
      finiteProductHaar blockCount (polyMul left target) +
        finiteProductHaar blockCount (polyMul right target) := by
  simp only [polyMul, List.flatMap_append]
  exact finiteProductHaar_append blockCount _ _

private theorem finiteProductHaar_polyMul_append_right
    (blockCount : Nat) (source left right : RatPoly) :
    finiteProductHaar blockCount (polyMul source (left ++ right)) ≈
      finiteProductHaar blockCount (polyMul source left) +
        finiteProductHaar blockCount (polyMul source right) := by
  refine Q'.eqv_trans _
    (finiteProductHaar blockCount (polyMul (left ++ right) source)) _
    (finiteProductHaar_polyMul_comm blockCount source (left ++ right)) ?_
  refine Q'.eqv_trans _
    (finiteProductHaar blockCount (polyMul left source) +
      finiteProductHaar blockCount (polyMul right source)) _
    (finiteProductHaar_polyMul_append_left
      blockCount left right source) ?_
  exact QPoly.q_add_congr
    (finiteProductHaar_polyMul_comm blockCount left source)
    (finiteProductHaar_polyMul_comm blockCount right source)

private theorem polyMul_nil_right : ∀ polynomial : RatPoly,
    polyMul polynomial [] = []
  | [] => rfl
  | _ :: polynomial => by simp [polyMul]

private theorem finiteProductHaar_homogenizeFiniteTerm_right
    (blockCount : Nat) (targets : Nat → Nat)
    (left : RatTerm) : ∀ right : RatPoly,
    finiteProductHaar blockCount
        (polyMul (homogenizeFiniteTerm blockCount targets left)
          (homogenizeFiniteParity blockCount targets right)) ≈
      finiteProductHaar blockCount (polyMul [left] right)
  | [] => by
      change
        finiteProductHaar blockCount
            (polyMul (homogenizeFiniteTerm blockCount targets left) []) ≈
          finiteProductHaar blockCount (polyMul [left] [])
      rw [polyMul_nil_right, polyMul_nil_right]
      exact Q'.eqv_refl 0
  | right :: polynomial => by
      refine Q'.eqv_trans _
        (finiteProductHaar blockCount
            (polyMul (homogenizeFiniteTerm blockCount targets left)
              (homogenizeFiniteTerm blockCount targets right)) +
          finiteProductHaar blockCount
            (polyMul (homogenizeFiniteTerm blockCount targets left)
              (homogenizeFiniteParity blockCount targets polynomial))) _
        (finiteProductHaar_polyMul_append_right blockCount _ _ _) ?_
      refine Q'.eqv_trans _
        (finiteProductHaar blockCount (polyMul [left] [right]) +
          finiteProductHaar blockCount (polyMul [left] polynomial)) _
        (QPoly.q_add_congr
          (finiteProductHaar_homogenizeFiniteTerm_pair
            blockCount targets left right)
          (finiteProductHaar_homogenizeFiniteTerm_right
            blockCount targets left polynomial)) ?_
      exact Q'.eqv_symm
        (finiteProductHaar_polyMul_append_right
          blockCount [left] [right] polynomial)

/-- The complete termwise homogenization preserves every rectangular Haar
pairing, not only squares. -/
theorem finiteProductHaar_homogenizeFiniteParity_pair
    (blockCount : Nat) (targets : Nat → Nat) :
    ∀ left right : RatPoly,
    finiteProductHaar blockCount
        (polyMul (homogenizeFiniteParity blockCount targets left)
          (homogenizeFiniteParity blockCount targets right)) ≈
      finiteProductHaar blockCount (polyMul left right)
  | [], right => by
      simp [homogenizeFiniteParity, polyMul]
      exact Q'.eqv_refl 0
  | left :: polynomial, right => by
      refine Q'.eqv_trans _
        (finiteProductHaar blockCount
            (polyMul (homogenizeFiniteTerm blockCount targets left)
              (homogenizeFiniteParity blockCount targets right)) +
          finiteProductHaar blockCount
            (polyMul (homogenizeFiniteParity blockCount targets polynomial)
              (homogenizeFiniteParity blockCount targets right))) _
        (finiteProductHaar_polyMul_append_left blockCount _ _ _) ?_
      refine Q'.eqv_trans _
        (finiteProductHaar blockCount (polyMul [left] right) +
          finiteProductHaar blockCount (polyMul polynomial right)) _
        (QPoly.q_add_congr
          (finiteProductHaar_homogenizeFiniteTerm_right
            blockCount targets left right)
          (finiteProductHaar_homogenizeFiniteParity_pair
            blockCount targets polynomial right)) ?_
      exact Q'.eqv_symm
        (finiteProductHaar_polyMul_append_left
          blockCount [left] polynomial right)

theorem finiteProductHaar_homogenizeFiniteParity_square
    (blockCount : Nat) (targets : Nat → Nat)
    (polynomial : RatPoly) :
    finiteProductHaar blockCount
        (polyMul (homogenizeFiniteParity blockCount targets polynomial)
          (homogenizeFiniteParity blockCount targets polynomial)) ≈
      finiteProductHaar blockCount (polyMul polynomial polynomial) :=
  finiteProductHaar_homogenizeFiniteParity_pair
    blockCount targets polynomial polynomial

/-! ## 6. Constructive common target degrees -/

/-- Sum of all listed monomial degrees in one selected quaternion block. -/
def quaternionBlockDegreeSum (block : Nat) : RatPoly → Nat
  | [] => 0
  | term :: polynomial =>
      quaternionBlockDegree block term.1 +
        quaternionBlockDegreeSum block polynomial

/-- A common target in one block.  Its head term fixes the parity, while the
doubled tail degree sum makes it at least every listed degree. -/
def targetQuaternionBlockDegree (block : Nat) : RatPoly → Nat
  | [] => 0
  | term :: polynomial =>
      quaternionBlockDegree block term.1 +
        2 * quaternionBlockDegreeSum block polynomial

/-- The lazy target degree assignment for all block indices. -/
def targetQuaternionBlockDegrees
    (polynomial : RatPoly) (block : Nat) : Nat :=
  targetQuaternionBlockDegree block polynomial

private theorem quaternionBlockDegree_le_sum
    (block : Nat) {term : RatTerm} : ∀ {polynomial : RatPoly},
    term ∈ polynomial →
      quaternionBlockDegree block term.1 ≤
        quaternionBlockDegreeSum block polynomial
  | [], hterm => by simp at hterm
  | head :: polynomial, hterm => by
      simp only [List.mem_cons] at hterm
      cases hterm with
      | inl hterm =>
          subst term
          simp [quaternionBlockDegreeSum]
      | inr hterm =>
          have ih := quaternionBlockDegree_le_sum
            block hterm
          simp only [quaternionBlockDegreeSum]
          omega

theorem quaternionBlockDegree_le_target
    (block : Nat) {term : RatTerm} : ∀ {polynomial : RatPoly},
    term ∈ polynomial →
      quaternionBlockDegree block term.1 ≤
        targetQuaternionBlockDegrees polynomial block
  | [], hterm => by simp at hterm
  | head :: polynomial, hterm => by
      simp only [List.mem_cons] at hterm
      cases hterm with
      | inl hterm =>
          subst term
          simp [targetQuaternionBlockDegrees,
            targetQuaternionBlockDegree]
      | inr hterm =>
          have hsum := quaternionBlockDegree_le_sum block hterm
          simp only [targetQuaternionBlockDegrees,
            targetQuaternionBlockDegree]
          omega

/-- Common coordinate parity forces equal total-degree parity in every
carried quaternion block. -/
theorem quaternionBlockDegree_mod_two_eq_of_commonParity
    {blockCount : Nat} {parities : Nat → Nat}
    {left right : RatTerm}
    (hleft : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt left.1 coordinate % 2 = parities coordinate)
    (hright : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt right.1 coordinate % 2 = parities coordinate)
    (block : Nat) (hblock : block < blockCount) :
    quaternionBlockDegree block left.1 % 2 =
      quaternionBlockDegree block right.1 % 2 := by
  have h0 := (hleft (4 * block) (by omega)).trans
    (hright (4 * block) (by omega)).symm
  have h1 := (hleft (4 * block + 1) (by omega)).trans
    (hright (4 * block + 1) (by omega)).symm
  have h2 := (hleft (4 * block + 2) (by omega)).trans
    (hright (4 * block + 2) (by omega)).symm
  have h3 := (hleft (4 * block + 3) (by omega)).trans
    (hright (4 * block + 3) (by omega)).symm
  unfold quaternionBlockDegree
  omega

/-- In one common parity sector, every term has an even gap to the lazily
computed target degree of every carried block. -/
theorem targetQuaternionBlockDegree_even_gap
    {blockCount : Nat} {parities : Nat → Nat}
    {term : RatTerm} {polynomial : RatPoly}
    (hparity :
      AllFiniteQuaternionCoordinateParity
        blockCount parities polynomial)
    (hterm : term ∈ polynomial)
    (block : Nat) (hblock : block < blockCount) :
    (targetQuaternionBlockDegrees polynomial block -
      quaternionBlockDegree block term.1) % 2 = 0 := by
  cases polynomial with
  | nil => simp at hterm
  | cons head tail =>
      have hheadParity := hparity head (by simp)
      have htermParity := hparity term hterm
      have hmod := quaternionBlockDegree_mod_two_eq_of_commonParity
        hheadParity htermParity block hblock
      have hle := quaternionBlockDegree_le_target block hterm
      simp only [targetQuaternionBlockDegrees,
        targetQuaternionBlockDegree]
      omega

/-! ## 7. Global homogenization invariants and mixed-degree positivity -/

theorem homogenizeFiniteParity_supported
    (blockCount : Nat) (targets : Nat → Nat) :
    ∀ polynomial : RatPoly,
      SupportedQuaternionBlocks blockCount polynomial →
      SupportedQuaternionBlocks blockCount
        (homogenizeFiniteParity blockCount targets polynomial)
  | [], _ => by
      intro term hterm
      simp [homogenizeFiniteParity] at hterm
  | term :: polynomial, hsupport => by
      rw [homogenizeFiniteParity]
      apply supportedQuaternionBlocks_append
      · exact homogenizeFiniteTerm_supported
          blockCount targets term (hsupport term (by simp))
      · exact homogenizeFiniteParity_supported
          blockCount targets polynomial
          (fun source hsource =>
            hsupport source (by simp [hsource]))

theorem homogenizeFiniteParity_parity
    (blockCount : Nat) (targets parities : Nat → Nat) :
    ∀ polynomial : RatPoly,
      AllFiniteQuaternionCoordinateParity
          blockCount parities polynomial →
      AllFiniteQuaternionCoordinateParity blockCount parities
        (homogenizeFiniteParity blockCount targets polynomial)
  | [], _ => by
      intro term hterm
      simp [homogenizeFiniteParity] at hterm
  | term :: polynomial, hparity => by
      rw [homogenizeFiniteParity]
      apply finiteParity_append
      · exact homogenizeFiniteTerm_parity
          blockCount targets parities term
          (hparity term (by simp))
      · exact homogenizeFiniteParity_parity
          blockCount targets parities polynomial
          (fun source hsource =>
            hparity source (by simp [hsource]))

theorem homogenizeFiniteParity_degrees_of_bounds
    (blockCount : Nat) (targets : Nat → Nat) :
    ∀ polynomial : RatPoly,
      (∀ term, term ∈ polynomial → ∀ block, block < blockCount →
        quaternionBlockDegree block term.1 ≤ targets block) →
      (∀ term, term ∈ polynomial → ∀ block, block < blockCount →
        (targets block - quaternionBlockDegree block term.1) % 2 = 0) →
      AllFiniteQuaternionBlockDegrees blockCount targets
        (homogenizeFiniteParity blockCount targets polynomial)
  | [], _, _ => by
      intro term hterm
      simp [homogenizeFiniteParity] at hterm
  | term :: polynomial, hle, heven => by
      rw [homogenizeFiniteParity]
      apply finiteDegrees_append
      · exact homogenizeFiniteTerm_degrees
          blockCount targets term
          (hle term (by simp))
          (heven term (by simp))
      · exact homogenizeFiniteParity_degrees_of_bounds
          blockCount targets polynomial
          (fun source hsource => hle source (by simp [hsource]))
          (fun source hsource => heven source (by simp [hsource]))

/-- The computed target function makes the homogenized polynomial genuinely
multihomogeneous across every carried block. -/
theorem homogenizeFiniteParity_targetDegrees
    (blockCount : Nat) (parities : Nat → Nat)
    (polynomial : RatPoly)
    (hparity :
      AllFiniteQuaternionCoordinateParity
        blockCount parities polynomial) :
    AllFiniteQuaternionBlockDegrees blockCount
      (targetQuaternionBlockDegrees polynomial)
      (homogenizeFiniteParity blockCount
        (targetQuaternionBlockDegrees polynomial) polynomial) := by
  apply homogenizeFiniteParity_degrees_of_bounds
  · intro term hterm block hblock
    exact quaternionBlockDegree_le_target block hterm
  · intro term hterm block hblock
    exact targetQuaternionBlockDegree_even_gap
      hparity hterm block hblock

/-- **Arbitrary finite-product Haar positivity inside one common coordinate
parity sector.**  No common-degree hypothesis remains: the lazy radius
schedule computes and realizes one target degree in every carried block. -/
theorem finiteProductHaar_square_nonneg_of_parity
    (blockCount : Nat) (parities : Nat → Nat)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks blockCount polynomial)
    (hparity :
      AllFiniteQuaternionCoordinateParity
        blockCount parities polynomial) :
    (0 : Q') ≤
      finiteProductHaar blockCount
        (polyMul polynomial polynomial) := by
  let targets := targetQuaternionBlockDegrees polynomial
  let homogenized := homogenizeFiniteParity blockCount targets polynomial
  have hsupportHomogenized :
      SupportedQuaternionBlocks blockCount homogenized :=
    homogenizeFiniteParity_supported
      blockCount targets polynomial hsupport
  have hparityHomogenized :
      AllFiniteQuaternionCoordinateParity
        blockCount parities homogenized :=
    homogenizeFiniteParity_parity
      blockCount targets parities polynomial hparity
  have hdegreesHomogenized :
      AllFiniteQuaternionBlockDegrees
        blockCount targets homogenized := by
    exact homogenizeFiniteParity_targetDegrees
      blockCount parities polynomial hparity
  have hnonnegative :=
    finiteProductHaar_square_nonneg_of_multihomogeneous_parity
      blockCount targets parities homogenized
      hsupportHomogenized hparityHomogenized hdegreesHomogenized
  exact Q'.le_trans' _ _ _ hnonnegative
    (Q'.le_of_eqv
      (finiteProductHaar_homogenizeFiniteParity_square
        blockCount targets polynomial))

#print axioms finiteProductHaar_polyMul_comm
#print axioms finiteProductHaar_polyMul_middle_comm
#print axioms finiteProductHaar_polyMul_assoc
#print axioms finiteProductHaar_polyMul_four_swap
#print axioms finiteProductHaar_blockRadiusIter_pair
#print axioms quaternionBlockRadiusPolynomial_supported
#print axioms exponentAt_coordinateSquareMonomial_safe
#print axioms quaternionBlockDegree_monoMul
#print axioms quaternionBlockDegree_squareMonomial
#print axioms quaternionBlockRadiusPolynomial_degrees
#print axioms blockRadiusIter_degrees
#print axioms homogenizeTermPrefix_degrees
#print axioms finiteProductHaar_homogenizeFiniteParity_square
#print axioms targetQuaternionBlockDegree_even_gap
#print axioms homogenizeFiniteParity_targetDegrees
#print axioms finiteProductHaar_square_nonneg_of_parity

end YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization
