/-
# Blockwise homogenization for arbitrary-product quaternion Haar

This file lifts the two-boundary radius-homogenization algebra to
`SU(2)^blocks`.  The first half establishes the commutative and associative
pairing identities needed to insert a radius polynomial on either side of a
Haar pairing.  The second half constructs the finite blockwise
homogenization used by the all-degree positivity theorem.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
import YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization

namespace YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal

local infix:50 " ≈ " => Q'.eqv

private theorem quaternionHaarRow_nil_right
    (blocks : Nat) :
    ∀ polynomial : RatPoly,
      quaternionHaarBilinear blocks polynomial [] ≈ 0
  | [] => Q'.eqv_refl 0
  | _ :: rest =>
      Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr_left 0 _ _
          (quaternionHaarRow_nil_right blocks rest))
        (QPoly.q_zero_add_eqv 0)

private theorem quaternionHaarCell_symm
    (blocks : Nat) (left right : RatTerm) :
    (left.2 * right.2) *
        quaternionHaarMono blocks
          (monoMul left.1 right.1) ≈
      (right.2 * left.2) *
        quaternionHaarMono blocks
          (monoMul right.1 left.1) := by
  rw [YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.monoMul_comm
    left.1 right.1]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_comm_eqv left.2 right.2)

private theorem quaternionHaarBilinear_symm
    (blocks : Nat) :
    ∀ left right : RatPoly,
      quaternionHaarBilinear blocks left right ≈
        quaternionHaarBilinear blocks right left
  | [], right =>
      Q'.eqv_symm
        (quaternionHaarRow_nil_right blocks right)
  | left, [] =>
      quaternionHaarRow_nil_right blocks left
  | source :: left, target :: right => by
      change
        ((source.2 * target.2) *
              quaternionHaarMono blocks
                (monoMul source.1 target.1) +
            quaternionHaarRow blocks source right) +
            quaternionHaarBilinear
              blocks left (target :: right) ≈
          ((target.2 * source.2) *
                quaternionHaarMono blocks
                  (monoMul target.1 source.1) +
              quaternionHaarRow blocks target left) +
            quaternionHaarBilinear
              blocks right (source :: left)
      refine Q'.eqv_trans _
        (((source.2 * target.2) *
              quaternionHaarMono blocks
                (monoMul source.1 target.1) +
            quaternionHaarRow blocks source right) +
          (quaternionHaarRow blocks target left +
            quaternionHaarBilinear
              blocks right left)) _
        (Q'.add_eqv_congr_left _ _ _
          (by
            simpa [quaternionHaarBilinear] using
              quaternionHaarBilinear_symm
                blocks left (target :: right))) ?_
      refine Q'.eqv_trans _
        (((target.2 * source.2) *
              quaternionHaarMono blocks
                (monoMul target.1 source.1) +
            quaternionHaarRow blocks source right) +
          (quaternionHaarRow blocks target left +
            quaternionHaarBilinear
              blocks left right)) _
        (QPoly.q_add_congr
          (Q'.add_eqv_congr_right _ _ _
            (quaternionHaarCell_symm
              blocks source target))
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm
              (quaternionHaarBilinear_symm
                blocks left right)))) ?_
      refine Q'.eqv_trans _
        (((target.2 * source.2) *
              quaternionHaarMono blocks
                (monoMul target.1 source.1) +
            quaternionHaarRow blocks target left) +
          (quaternionHaarRow blocks source right +
            quaternionHaarBilinear
              blocks left right)) _
        (QPoly.q_interchange _ _ _ _) ?_
      exact Q'.add_eqv_congr_left _ _ _
        (by
          simpa [quaternionHaarBilinear] using
            quaternionHaarBilinear_symm
              blocks (source :: left) right)

/-- Commutativity of the polynomial product under arbitrary-product Haar. -/
theorem quaternionHaar_polyMul_comm
    (blocks : Nat) (left right : RatPoly) :
    quaternionHaar blocks (polyMul left right) ≈
      quaternionHaar blocks (polyMul right left) := by
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks left right) _
    (quaternionHaar_polyMul blocks left right) ?_
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks right left) _
    (quaternionHaarBilinear_symm blocks left right) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul blocks right left)

private def quaternionHaarTripleCell
    (blocks : Nat)
    (first second third : RatTerm) : Q' :=
  ((first.2 * second.2) * third.2) *
    quaternionHaarMono blocks
      (monoMul (monoMul first.1 second.1) third.1)

private def quaternionHaarTripleLast
    (blocks : Nat) (first second : RatTerm) :
    RatPoly → Q'
  | [] => 0
  | third :: rest =>
      quaternionHaarTripleCell
          blocks first second third +
        quaternionHaarTripleLast
          blocks first second rest

private def quaternionHaarTripleMiddle
    (blocks : Nat) (first : RatTerm) :
    RatPoly → RatPoly → Q'
  | [], _ => 0
  | second :: rest, third =>
      quaternionHaarTripleLast
          blocks first second third +
        quaternionHaarTripleMiddle
          blocks first rest third

private def quaternionHaarTriple
    (blocks : Nat) :
    RatPoly → RatPoly → RatPoly → Q'
  | [], _, _ => 0
  | first :: rest, second, third =>
      quaternionHaarTripleMiddle
          blocks first second third +
        quaternionHaarTriple
          blocks rest second third

private theorem quaternionHaarRow_generated
    (blocks : Nat) (first second : RatTerm) :
    ∀ third : RatPoly,
      quaternionHaarRow blocks
          (monoMul first.1 second.1,
            first.2 * second.2) third ≈
        quaternionHaarTripleLast
          blocks first second third
  | [] => Q'.eqv_refl 0
  | third :: rest => by
      change
        ((first.2 * second.2) * third.2) *
              quaternionHaarMono blocks
                (monoMul
                  (monoMul first.1 second.1)
                  third.1) +
            quaternionHaarRow blocks
              (monoMul first.1 second.1,
                first.2 * second.2) rest ≈
          quaternionHaarTripleCell
                blocks first second third +
            quaternionHaarTripleLast
              blocks first second rest
      exact Q'.add_eqv_congr_left _ _ _
        (quaternionHaarRow_generated
          blocks first second rest)

private theorem quaternionHaarBilinear_generated
    (blocks : Nat) (first : RatTerm) :
    ∀ second third : RatPoly,
      quaternionHaarBilinear blocks
          (second.map fun term =>
            (monoMul first.1 term.1,
              first.2 * term.2)) third ≈
        quaternionHaarTripleMiddle
          blocks first second third
  | [], _ => Q'.eqv_refl 0
  | second :: rest, third => by
      exact QPoly.q_add_congr
        (quaternionHaarRow_generated
          blocks first second third)
        (quaternionHaarBilinear_generated
          blocks first rest third)

private theorem quaternionHaarBilinear_polyMul_left
    (blocks : Nat) :
    ∀ first second third : RatPoly,
      quaternionHaarBilinear blocks
          (polyMul first second) third ≈
        quaternionHaarTriple
          blocks first second third
  | [], _, _ => Q'.eqv_refl 0
  | first :: rest, second, third => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (quaternionHaarBilinear blocks
              (second.map fun term =>
                (monoMul first.1 term.1,
                  first.2 * term.2)) third +
          quaternionHaarBilinear blocks
              (polyMul rest second) third) _ ?_ ?_
      · have happend :
          ∀ left right : RatPoly,
            quaternionHaarBilinear blocks
                (left ++ right) third ≈
              quaternionHaarBilinear blocks left third +
                quaternionHaarBilinear blocks right third := by
          intro left right
          induction left with
          | nil =>
              exact Q'.eqv_symm
                (QPoly.q_zero_add_eqv _)
          | cons term tail induction =>
              change
                quaternionHaarRow blocks term third +
                    quaternionHaarBilinear
                      blocks (tail ++ right) third ≈
                  (quaternionHaarRow blocks term third +
                      quaternionHaarBilinear
                        blocks tail third) +
                    quaternionHaarBilinear
                      blocks right third
              exact Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr_left _ _ _ induction)
                (Q'.eqv_symm
                  (Q'.add_assoc_eqv _ _ _))
        exact happend _ _
      · exact QPoly.q_add_congr
          (quaternionHaarBilinear_generated
            blocks first second third)
          (quaternionHaarBilinear_polyMul_left
            blocks rest second third)

private theorem quaternionHaarTripleCell_right_assoc
    (blocks : Nat)
    (first second third : RatTerm) :
    (first.2 * (second.2 * third.2)) *
        quaternionHaarMono blocks
          (monoMul first.1
            (monoMul second.1 third.1)) ≈
      quaternionHaarTripleCell
        blocks first second third := by
  unfold quaternionHaarTripleCell
  rw [←
    YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.monoMul_assoc
      first.1 second.1 third.1]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        first.2 second.2 third.2))

private theorem quaternionHaarRow_map_right
    (blocks : Nat) (first second : RatTerm) :
    ∀ third : RatPoly,
      quaternionHaarRow blocks first
          (third.map fun term =>
            (monoMul second.1 term.1,
              second.2 * term.2)) ≈
        quaternionHaarTripleLast
          blocks first second third
  | [] => Q'.eqv_refl 0
  | third :: rest => by
      exact QPoly.q_add_congr
        (quaternionHaarTripleCell_right_assoc
          blocks first second third)
        (quaternionHaarRow_map_right
          blocks first second rest)

private theorem quaternionHaarRow_polyMul_right
    (blocks : Nat) (first : RatTerm) :
    ∀ second third : RatPoly,
      quaternionHaarRow blocks first
          (polyMul second third) ≈
        quaternionHaarTripleMiddle
          blocks first second third
  | [], _ => Q'.eqv_refl 0
  | second :: rest, third => by
      unfold polyMul List.flatMap
      have hrowAppend :
          ∀ left right : RatPoly,
            quaternionHaarRow blocks first
                (left ++ right) ≈
              quaternionHaarRow blocks first left +
                quaternionHaarRow blocks first right := by
        intro left right
        induction left with
        | nil =>
            exact Q'.eqv_symm
              (QPoly.q_zero_add_eqv _)
        | cons term tail induction =>
            change
              (first.2 * term.2) *
                    quaternionHaarMono blocks
                      (monoMul first.1 term.1) +
                  quaternionHaarRow blocks first
                    (tail ++ right) ≈
                ((first.2 * term.2) *
                      quaternionHaarMono blocks
                        (monoMul first.1 term.1) +
                    quaternionHaarRow blocks first tail) +
                  quaternionHaarRow blocks first right
            exact Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_left _ _ _ induction)
              (Q'.eqv_symm
                (Q'.add_assoc_eqv _ _ _))
      refine Q'.eqv_trans _
        (quaternionHaarRow blocks first
              (third.map fun term =>
                (monoMul second.1 term.1,
                  second.2 * term.2)) +
          quaternionHaarRow blocks first
            (polyMul rest third)) _
        (hrowAppend _ _) ?_
      exact QPoly.q_add_congr
        (quaternionHaarRow_map_right
          blocks first second third)
        (quaternionHaarRow_polyMul_right
          blocks first rest third)

private theorem quaternionHaarBilinear_polyMul_right
    (blocks : Nat) :
    ∀ first second third : RatPoly,
      quaternionHaarBilinear blocks first
          (polyMul second third) ≈
        quaternionHaarTriple
          blocks first second third
  | [], _, _ => Q'.eqv_refl 0
  | first :: rest, second, third => by
      exact QPoly.q_add_congr
        (quaternionHaarRow_polyMul_right
          blocks first second third)
        (quaternionHaarBilinear_polyMul_right
          blocks rest second third)

private theorem quaternionHaarTripleCell_swap_last
    (blocks : Nat)
    (first second third : RatTerm) :
    quaternionHaarTripleCell blocks first second third ≈
      quaternionHaarTripleCell blocks first third second := by
  unfold quaternionHaarTripleCell
  have hmonomial :
      monoMul (monoMul first.1 second.1) third.1 =
        monoMul (monoMul first.1 third.1) second.1 := by
    rw [
      YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.monoMul_assoc,
      YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.monoMul_comm
        second.1 third.1,
      ← YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.monoMul_assoc]
  rw [hmonomial]
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  refine Q'.eqv_trans _
    (first.2 * (second.2 * third.2)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (first.2 * (third.2 * second.2)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv _ _ _)

private theorem quaternionHaarTripleMiddle_nil_right
    (blocks : Nat) (first : RatTerm) :
    ∀ second : RatPoly,
      quaternionHaarTripleMiddle blocks first second [] ≈ 0
  | [] => Q'.eqv_refl 0
  | _ :: rest =>
      Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr_left 0 _ _
          (quaternionHaarTripleMiddle_nil_right
            blocks first rest))
        (QPoly.q_zero_add_eqv 0)

private theorem quaternionHaarTripleMiddle_swap
    (blocks : Nat) (first : RatTerm) :
    ∀ second third : RatPoly,
      quaternionHaarTripleMiddle
          blocks first second third ≈
        quaternionHaarTripleMiddle
          blocks first third second
  | [], third =>
      Q'.eqv_symm
        (quaternionHaarTripleMiddle_nil_right
          blocks first third)
  | _ :: _, [] =>
      quaternionHaarTripleMiddle_nil_right
        blocks first _
  | second :: secondRest, third :: thirdRest => by
      change
        (quaternionHaarTripleCell
              blocks first second third +
            quaternionHaarTripleLast
              blocks first second thirdRest) +
          quaternionHaarTripleMiddle
            blocks first secondRest
              (third :: thirdRest) ≈
        (quaternionHaarTripleCell
              blocks first third second +
            quaternionHaarTripleLast
              blocks first third secondRest) +
          quaternionHaarTripleMiddle
            blocks first thirdRest
              (second :: secondRest)
      refine Q'.eqv_trans _
        ((quaternionHaarTripleCell
                blocks first second third +
              quaternionHaarTripleLast
                blocks first second thirdRest) +
          (quaternionHaarTripleLast
                blocks first third secondRest +
            quaternionHaarTripleMiddle
              blocks first thirdRest secondRest)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (by
            simpa [quaternionHaarTripleMiddle] using
              quaternionHaarTripleMiddle_swap
                blocks first secondRest
                  (third :: thirdRest))
      · refine Q'.eqv_trans _
          ((quaternionHaarTripleCell
                  blocks first third second +
                quaternionHaarTripleLast
                  blocks first second thirdRest) +
            (quaternionHaarTripleLast
                  blocks first third secondRest +
              quaternionHaarTripleMiddle
                blocks first secondRest thirdRest)) _ ?_ ?_
        · exact QPoly.q_add_congr
            (Q'.add_eqv_congr_right _ _ _
              (quaternionHaarTripleCell_swap_last
                blocks first second third))
            (Q'.add_eqv_congr_left _ _ _
              (Q'.eqv_symm
                (quaternionHaarTripleMiddle_swap
                  blocks first secondRest thirdRest)))
        · refine Q'.eqv_trans _
            ((quaternionHaarTripleCell
                    blocks first third second +
                  quaternionHaarTripleLast
                    blocks first third secondRest) +
              (quaternionHaarTripleLast
                    blocks first second thirdRest +
                quaternionHaarTripleMiddle
                  blocks first secondRest thirdRest)) _ ?_ ?_
          · exact QPoly.q_interchange _ _ _ _
          · exact Q'.add_eqv_congr_left _ _ _
              (by
                simpa [quaternionHaarTripleMiddle] using
                  quaternionHaarTripleMiddle_swap
                    blocks first (second :: secondRest)
                      thirdRest)

private theorem quaternionHaarTriple_swap_last
    (blocks : Nat) :
    ∀ first second third : RatPoly,
      quaternionHaarTriple blocks first second third ≈
        quaternionHaarTriple blocks first third second
  | [], _, _ => Q'.eqv_refl 0
  | first :: rest, second, third =>
      QPoly.q_add_congr
        (quaternionHaarTripleMiddle_swap
          blocks first second third)
        (quaternionHaarTriple_swap_last
          blocks rest second third)

/-- The last two factors of a triple product may be exchanged under exact
product Haar for an arbitrary number of retained quaternion blocks. -/
theorem quaternionHaar_polyMul_middle_comm
    (blocks : Nat) (first second third : RatPoly) :
    quaternionHaar blocks
        (polyMul first (polyMul second third)) ≈
      quaternionHaar blocks
        (polyMul first (polyMul third second)) := by
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks first
      (polyMul second third)) _
    (quaternionHaar_polyMul
      blocks first (polyMul second third)) ?_
  refine Q'.eqv_trans _
    (quaternionHaarTriple blocks first second third) _
    (quaternionHaarBilinear_polyMul_right
      blocks first second third) ?_
  refine Q'.eqv_trans _
    (quaternionHaarTriple blocks first third second) _
    (quaternionHaarTriple_swap_last
      blocks first second third) ?_
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks first
      (polyMul third second)) _
    (Q'.eqv_symm
      (quaternionHaarBilinear_polyMul_right
        blocks first third second)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul
      blocks first (polyMul third second))

/-- Associativity of the polynomial product under arbitrary-product Haar. -/
theorem quaternionHaar_polyMul_assoc
    (blocks : Nat) (first second third : RatPoly) :
    quaternionHaar blocks
        (polyMul (polyMul first second) third) ≈
      quaternionHaar blocks
        (polyMul first (polyMul second third)) := by
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks
      (polyMul first second) third) _
    (quaternionHaar_polyMul
      blocks (polyMul first second) third) ?_
  refine Q'.eqv_trans _
    (quaternionHaarTriple
      blocks first second third) _
    (quaternionHaarBilinear_polyMul_left
      blocks first second third) ?_
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks first
      (polyMul second third)) _
    (Q'.eqv_symm
      (quaternionHaarBilinear_polyMul_right
        blocks first second third)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul
      blocks first (polyMul second third))

/-- Repeated multiplication by the radius polynomial of one block. -/
def quaternionRadiusIter
    (block : Nat) : Nat → RatPoly → RatPoly
  | 0, polynomial => polynomial
  | count + 1, polynomial =>
      polyMul
        (quaternionRadiusIter block count polynomial)
        (quaternionRadiusPolynomial block)

theorem quaternionHaar_radiusIter
    (blocks block : Nat) (hblock : block < blocks)
    (polynomial : RatPoly) :
    ∀ count,
      quaternionHaar blocks
          (quaternionRadiusIter
            block count polynomial) ≈
        quaternionHaar blocks polynomial
  | 0 => Q'.eqv_refl _
  | count + 1 =>
      Q'.eqv_trans _ _ _
        (quaternionHaar_mul_radius
          blocks block hblock
          (quaternionRadiusIter
            block count polynomial))
        (quaternionHaar_radiusIter
          blocks block hblock polynomial count)

theorem quaternionHaar_radiusIter_pair_right
    (blocks block : Nat) (hblock : block < blocks)
    (left right : RatPoly) :
    ∀ count,
      quaternionHaar blocks
          (polyMul left
            (quaternionRadiusIter
              block count right)) ≈
        quaternionHaar blocks
          (polyMul left right)
  | 0 => Q'.eqv_refl _
  | count + 1 => by
      unfold quaternionRadiusIter
      refine Q'.eqv_trans _
        (quaternionHaar blocks
          (polyMul
            (polyMul left
              (quaternionRadiusIter
                block count right))
            (quaternionRadiusPolynomial block))) _
        (Q'.eqv_symm
          (quaternionHaar_polyMul_assoc
            blocks left
            (quaternionRadiusIter
              block count right)
            (quaternionRadiusPolynomial block))) ?_
      refine Q'.eqv_trans _
        (quaternionHaar blocks
          (polyMul left
            (quaternionRadiusIter
              block count right))) _
        (quaternionHaar_mul_radius
          blocks block hblock _) ?_
      exact quaternionHaar_radiusIter_pair_right
        blocks block hblock left right count

theorem quaternionHaar_radiusIter_pair_left
    (blocks block : Nat) (hblock : block < blocks)
    (left right : RatPoly) (count : Nat) :
    quaternionHaar blocks
        (polyMul
          (quaternionRadiusIter
            block count left) right) ≈
      quaternionHaar blocks
        (polyMul left right) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul right
        (quaternionRadiusIter
          block count left))) _
    (quaternionHaar_polyMul_comm
      blocks
      (quaternionRadiusIter
        block count left) right) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul right left)) _
    (quaternionHaar_radiusIter_pair_right
      blocks block hblock right left count) ?_
  exact quaternionHaar_polyMul_comm
    blocks right left

/-! ## Block-degree and parity bookkeeping -/

private theorem exponentAt_monoMul
    (left right : List Nat) (index : Nat) :
    exponentAt (monoMul left right) index =
      exponentAt left index + exponentAt right index := by
  induction left generalizing right index with
  | nil => simp [monoMul, exponentAt]
  | cons x xs induction =>
      cases right with
      | nil => simp [monoMul, exponentAt]
      | cons y ys =>
          cases index with
          | zero => simp [monoMul, exponentAt]
          | succ index =>
              change exponentAt (monoMul xs ys) index =
                exponentAt xs index + exponentAt ys index
              exact induction ys index

private theorem monoMul_drop_of_length_le
    (left right : List Nat) (coordinates : Nat)
    (hright : right.length ≤ coordinates) :
    (monoMul left right).drop coordinates =
      left.drop coordinates := by
  induction coordinates generalizing left right with
  | zero =>
      cases right with
      | nil => cases left <;> rfl
      | cons y ys => simp at hright
  | succ coordinates induction =>
      cases left with
      | nil =>
          simp only [monoMul]
          exact List.drop_eq_nil_of_le hright
      | cons x xs =>
          cases right with
          | nil => simp [monoMul]
          | cons y ys =>
              simp only [List.length_cons] at hright
              simp [monoMul,
                induction xs ys (by omega)]

private theorem monoMul_length_le
    {left right : List Nat} {coordinates : Nat}
    (hleft : left.length ≤ coordinates)
    (hright : right.length ≤ coordinates) :
    (monoMul left right).length ≤ coordinates := by
  apply List.drop_eq_nil_iff.mp
  rw [monoMul_drop_of_length_le
    left right coordinates hright]
  exact List.drop_eq_nil_of_le hleft

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
  obtain ⟨leftTerm, hleft, hterm⟩ := hterm
  rw [List.mem_map] at hterm
  obtain ⟨rightTerm, hright, rfl⟩ := hterm
  exact ⟨leftTerm, hleft,
    rightTerm, hright, rfl⟩

private theorem quaternionBlockDegree_monoMul
    (left right : List Nat) (block : Nat) :
    quaternionBlockDegree
        (monoMul left right) block =
      quaternionBlockDegree left block +
        quaternionBlockDegree right block := by
  unfold quaternionBlockDegree
  simp only [exponentAt_monoMul]
  omega

private theorem coordinateSquareMono_blockDegree
    (radiusBlock coordinateOffset block : Nat)
    (hoffset : coordinateOffset < 4) :
    quaternionBlockDegree
        (coordinateSquareMono
          (4 * radiusBlock + coordinateOffset))
        block =
      if block = radiusBlock then 2 else 0 := by
  unfold quaternionBlockDegree
  simp only [exponentAt_coordinateSquareMono]
  by_cases hblock : block = radiusBlock
  · subst block
    have hoffsetCases :
        coordinateOffset = 0 ∨
          coordinateOffset = 1 ∨
          coordinateOffset = 2 ∨
          coordinateOffset = 3 := by
      omega
    rcases hoffsetCases with rfl | rfl | rfl | rfl
    · have h1 :
          4 * radiusBlock + 1 ≠
            4 * radiusBlock := by omega
      have h2 :
          4 * radiusBlock + 2 ≠
            4 * radiusBlock := by omega
      have h3 :
          4 * radiusBlock + 3 ≠
            4 * radiusBlock := by omega
      simp only [if_true, if_neg h1,
        if_neg h2, if_neg h3, Nat.add_zero]
    · have h0 :
          4 * radiusBlock ≠
            4 * radiusBlock + 1 := by omega
      have h2 :
          4 * radiusBlock + 2 ≠
            4 * radiusBlock + 1 := by omega
      have h3 :
          4 * radiusBlock + 3 ≠
            4 * radiusBlock + 1 := by omega
      simp only [if_true, if_neg h0,
        if_neg h2, if_neg h3,
        Nat.zero_add, Nat.add_zero]
    · have h0 :
          4 * radiusBlock ≠
            4 * radiusBlock + 2 := by omega
      have h1 :
          4 * radiusBlock + 1 ≠
            4 * radiusBlock + 2 := by omega
      have h3 :
          4 * radiusBlock + 3 ≠
            4 * radiusBlock + 2 := by omega
      simp only [if_true, if_neg h0,
        if_neg h1, if_neg h3,
        Nat.zero_add, Nat.add_zero]
    · have h0 :
          4 * radiusBlock ≠
            4 * radiusBlock + 3 := by omega
      have h1 :
          4 * radiusBlock + 1 ≠
            4 * radiusBlock + 3 := by omega
      have h2 :
          4 * radiusBlock + 2 ≠
            4 * radiusBlock + 3 := by omega
      simp only [if_true, if_neg h0,
        if_neg h1, if_neg h2,
        Nat.zero_add, Nat.add_zero]
  · simp only [if_neg hblock]
    have h0 :
        4 * block ≠
          4 * radiusBlock + coordinateOffset := by
      omega
    have h1 :
        4 * block + 1 ≠
          4 * radiusBlock + coordinateOffset := by
      omega
    have h2 :
        4 * block + 2 ≠
          4 * radiusBlock + coordinateOffset := by
      omega
    have h3 :
        4 * block + 3 ≠
          4 * radiusBlock + coordinateOffset := by
      omega
    simp only [if_neg h0, if_neg h1,
      if_neg h2, if_neg h3, Nat.zero_add]

theorem quaternionRadiusPolynomial_supported
    (blocks block : Nat) (hblock : block < blocks) :
    SupportedQuaternionBlocks blocks
      (quaternionRadiusPolynomial block) := by
  intro term hterm
  simp only [quaternionRadiusPolynomial,
    List.mem_cons, List.not_mem_nil,
    or_false] at hterm
  rcases hterm with rfl | rfl | rfl | rfl
  all_goals
    rw [coordinateSquareMono_length]
    omega

private theorem quaternionRadiusPolynomial_degree
    (radiusBlock block : Nat) :
    ∀ term, term ∈
        quaternionRadiusPolynomial radiusBlock →
      quaternionBlockDegree term.1 block =
        if block = radiusBlock then 2 else 0 := by
  intro term hterm
  simp only [quaternionRadiusPolynomial,
    List.mem_cons, List.not_mem_nil,
    or_false] at hterm
  rcases hterm with rfl | rfl | rfl | rfl
  · exact coordinateSquareMono_blockDegree
      radiusBlock 0 block (by omega)
  · exact coordinateSquareMono_blockDegree
      radiusBlock 1 block (by omega)
  · exact coordinateSquareMono_blockDegree
      radiusBlock 2 block (by omega)
  · exact coordinateSquareMono_blockDegree
      radiusBlock 3 block (by omega)

private theorem sameQuaternionParity_refl
    (blocks : Nat) (monomial : List Nat) :
    SameQuaternionParity blocks monomial monomial := by
  intro index hindex
  rfl

private theorem sameQuaternionParity_symm
    {blocks : Nat} {left right : List Nat}
    (hparity :
      SameQuaternionParity blocks left right) :
    SameQuaternionParity blocks right left := by
  intro index hindex
  exact (hparity index hindex).symm

private theorem sameQuaternionParity_trans
    {blocks : Nat} {first second third : List Nat}
    (hfirst :
      SameQuaternionParity blocks first second)
    (hsecond :
      SameQuaternionParity blocks second third) :
    SameQuaternionParity blocks first third := by
  intro index hindex
  exact (hfirst index hindex).trans
    (hsecond index hindex)

private theorem sameQuaternionParity_mul_radiusTerm
    (blocks : Nat) (monomial : List Nat)
    (radiusBlock : Nat) :
    ∀ term, term ∈
        quaternionRadiusPolynomial radiusBlock →
      SameQuaternionParity blocks monomial
        (monoMul monomial term.1) := by
  intro term hterm index hindex
  simp only [quaternionRadiusPolynomial,
    List.mem_cons, List.not_mem_nil,
    or_false] at hterm
  rcases hterm with rfl | rfl | rfl | rfl
  all_goals
    rw [exponentAt_monoMul,
      exponentAt_coordinateSquareMono]
    split <;> omega

private theorem supported_polyMul
    {blocks : Nat} {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks blocks left)
    (hright : SupportedQuaternionBlocks blocks right) :
    SupportedQuaternionBlocks blocks
      (polyMul left right) := by
  intro term hterm
  obtain ⟨leftTerm, hleftTerm,
      rightTerm, hrightTerm, rfl⟩ :=
    mem_polyMul hterm
  exact monoMul_length_le
    (hleft leftTerm hleftTerm)
    (hright rightTerm hrightTerm)

private theorem radiusIter_supported
    (blocks block : Nat) (hblock : block < blocks)
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial) :
    ∀ count,
      SupportedQuaternionBlocks blocks
        (quaternionRadiusIter
          block count polynomial)
  | 0 => hsupport
  | count + 1 =>
      supported_polyMul
        (radiusIter_supported
          blocks block hblock polynomial
          hsupport count)
        (quaternionRadiusPolynomial_supported
          blocks block hblock)

private theorem radiusIter_parity
    (blocks block : Nat) (reference : List Nat)
    (polynomial : RatPoly)
    (hparity :
      ∀ term, term ∈ polynomial →
        SameQuaternionParity
          blocks reference term.1) :
    ∀ count,
      ∀ term, term ∈
          quaternionRadiusIter
            block count polynomial →
        SameQuaternionParity
          blocks reference term.1
  | 0 => hparity
  | count + 1 => by
      intro term hterm
      obtain ⟨leftTerm, hleft,
          radiusTerm, hradius, rfl⟩ :=
        mem_polyMul hterm
      exact sameQuaternionParity_trans
        (radiusIter_parity
          blocks block reference polynomial
          hparity count leftTerm hleft)
        (sameQuaternionParity_mul_radiusTerm
          blocks leftTerm.1 block
          radiusTerm hradius)

private theorem radiusIter_degree
    (radiusBlock block degree : Nat)
    (polynomial : RatPoly)
    (hdegree :
      ∀ term, term ∈ polynomial →
        quaternionBlockDegree term.1 block =
          degree) :
    ∀ count,
      ∀ term, term ∈
          quaternionRadiusIter
            radiusBlock count polynomial →
        quaternionBlockDegree term.1 block =
          degree +
            count *
              (if block = radiusBlock
                then 2 else 0)
  | 0 => by
      intro term hterm
      simpa using hdegree term hterm
  | count + 1 => by
      intro term hterm
      obtain ⟨leftTerm, hleft,
          radiusTerm, hradius, rfl⟩ :=
        mem_polyMul hterm
      rw [quaternionBlockDegree_monoMul,
        radiusIter_degree radiusBlock block degree
          polynomial hdegree count
          leftTerm hleft,
        quaternionRadiusPolynomial_degree
          radiusBlock block radiusTerm hradius]
      by_cases hblock : block = radiusBlock
      · simp only [if_pos hblock]
        omega
      · simp only [if_neg hblock]
        omega

/-! ## Computed blockwise homogenization -/

def quaternionRaiseCount
    (targetDegrees : Nat → Nat)
    (block : Nat) (term : RatTerm) : Nat :=
  (targetDegrees block -
    quaternionBlockDegree term.1 block) / 2

/-- Homogenize one term in blocks `0,...,blocks-1`. -/
def homogenizeQuaternionTerm
    (targetDegrees : Nat → Nat) :
    Nat → RatTerm → RatPoly
  | 0, term => [term]
  | blocks + 1, term =>
      quaternionRadiusIter blocks
        (quaternionRaiseCount
          targetDegrees blocks term)
        (homogenizeQuaternionTerm
          targetDegrees blocks term)

/-- Concatenate the independently homogenized expansions of all terms. -/
def homogenizeQuaternionPolynomial
    (targetDegrees : Nat → Nat)
    (blocks : Nat) : RatPoly → RatPoly
  | [] => []
  | term :: rest =>
      homogenizeQuaternionTerm
          targetDegrees blocks term ++
        homogenizeQuaternionPolynomial
          targetDegrees blocks rest

private theorem singleton_supported
    {blocks : Nat} {term : RatTerm}
    (hterm : term.1.length ≤ 4 * blocks) :
    SupportedQuaternionBlocks blocks [term] := by
  intro other hother
  have heq : other = term := by
    simpa using hother
  subst other
  exact hterm

theorem homogenizeQuaternionTerm_supported
    (targetDegrees : Nat → Nat)
    (totalBlocks : Nat) (term : RatTerm)
    (hterm : term.1.length ≤ 4 * totalBlocks) :
    ∀ processedBlocks,
      processedBlocks ≤ totalBlocks →
      SupportedQuaternionBlocks totalBlocks
        (homogenizeQuaternionTerm
          targetDegrees processedBlocks term)
  | 0, _ => singleton_supported hterm
  | processedBlocks + 1, hprocessed => by
      unfold homogenizeQuaternionTerm
      exact radiusIter_supported
        totalBlocks processedBlocks (by omega) _
        (homogenizeQuaternionTerm_supported
          targetDegrees totalBlocks term hterm
          processedBlocks (by omega))
        (quaternionRaiseCount
          targetDegrees processedBlocks term)

theorem homogenizeQuaternionTerm_parity
    (targetDegrees : Nat → Nat)
    (totalBlocks : Nat) (term : RatTerm) :
    ∀ processedBlocks,
      processedBlocks ≤ totalBlocks →
      ∀ output, output ∈
          homogenizeQuaternionTerm
            targetDegrees processedBlocks term →
        SameQuaternionParity
          totalBlocks term.1 output.1
  | 0, _ => by
      intro output houtput
      have heq : output = term := by
        simpa [homogenizeQuaternionTerm] using houtput
      subst output
      exact sameQuaternionParity_refl
        totalBlocks term.1
  | processedBlocks + 1, hprocessed => by
      intro output houtput
      unfold homogenizeQuaternionTerm at houtput
      exact radiusIter_parity
        totalBlocks processedBlocks term.1 _
        (fun intermediate hintermediate =>
          homogenizeQuaternionTerm_parity
            targetDegrees totalBlocks term
            processedBlocks (by omega)
            intermediate hintermediate)
        (quaternionRaiseCount
          targetDegrees processedBlocks term)
        output houtput

private theorem singleton_degree
    (term : RatTerm) (block : Nat) :
    ∀ output, output ∈ [term] →
      quaternionBlockDegree output.1 block =
        quaternionBlockDegree term.1 block := by
  intro output houtput
  have heq : output = term := by
    simpa using houtput
  subst output
  rfl

theorem homogenizeQuaternionTerm_degree
    (targetDegrees : Nat → Nat)
    (processedBlocks : Nat) (term : RatTerm)
    (block : Nat) :
    ∀ output, output ∈
        homogenizeQuaternionTerm
          targetDegrees processedBlocks term →
      quaternionBlockDegree output.1 block =
        quaternionBlockDegree term.1 block +
          if block < processedBlocks then
            quaternionRaiseCount
              targetDegrees block term * 2
          else 0 := by
  induction processedBlocks with
  | zero =>
      intro output houtput
      simp only [Nat.not_lt_zero, if_false,
        Nat.add_zero]
      exact singleton_degree term block
        output (by
          simpa [homogenizeQuaternionTerm]
            using houtput)
  | succ processedBlocks induction =>
      intro output houtput
      unfold homogenizeQuaternionTerm at houtput
      have hdegree :=
        radiusIter_degree
          processedBlocks block
          (quaternionBlockDegree term.1 block +
            if block < processedBlocks then
              quaternionRaiseCount
                targetDegrees block term * 2
            else 0)
          (homogenizeQuaternionTerm
            targetDegrees processedBlocks term)
          (fun intermediate hintermediate =>
            induction intermediate hintermediate)
          (quaternionRaiseCount
            targetDegrees processedBlocks term)
          output houtput
      rw [hdegree]
      by_cases hless : block < processedBlocks
      · have hneq : block ≠ processedBlocks := by
          omega
        simp only [if_pos hless, if_neg hneq,
          if_pos (by omega :
            block < processedBlocks + 1),
          Nat.mul_zero, Nat.add_zero]
      · by_cases heq : block = processedBlocks
        · subst block
          simp only [Nat.lt_irrefl, if_false,
            Nat.lt_succ_self, if_true]
          omega
        · have hgreater :
              ¬ block < processedBlocks + 1 := by
            omega
          simp only [if_neg hless, if_neg heq,
            if_neg hgreater, Nat.mul_zero,
            Nat.add_zero]

theorem homogenizeQuaternionTerm_target_degree
    (targetDegrees : Nat → Nat)
    (blocks : Nat) (term : RatTerm)
    (block : Nat) (hblock : block < blocks)
    (hle :
      quaternionBlockDegree term.1 block ≤
        targetDegrees block)
    (heven :
      (targetDegrees block -
        quaternionBlockDegree term.1 block) % 2 = 0) :
    ∀ output, output ∈
        homogenizeQuaternionTerm
          targetDegrees blocks term →
      quaternionBlockDegree output.1 block =
        targetDegrees block := by
  intro output houtput
  rw [homogenizeQuaternionTerm_degree
    targetDegrees blocks term block
    output houtput, if_pos hblock]
  unfold quaternionRaiseCount
  omega

private theorem supported_append
    {blocks : Nat} {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks blocks left)
    (hright : SupportedQuaternionBlocks blocks right) :
    SupportedQuaternionBlocks blocks
      (left ++ right) := by
  intro term hterm
  simp only [List.mem_append] at hterm
  rcases hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

theorem homogenizeQuaternionPolynomial_supported
    (targetDegrees : Nat → Nat)
    (blocks : Nat) :
    ∀ polynomial,
      SupportedQuaternionBlocks blocks polynomial →
      SupportedQuaternionBlocks blocks
        (homogenizeQuaternionPolynomial
          targetDegrees blocks polynomial)
  | [], _ => by
      intro term hterm
      simp [homogenizeQuaternionPolynomial] at hterm
  | term :: rest, hsupport => by
      unfold homogenizeQuaternionPolynomial
      exact supported_append
        (homogenizeQuaternionTerm_supported
          targetDegrees blocks term
          (hsupport term (by simp))
          blocks (Nat.le_refl _))
        (homogenizeQuaternionPolynomial_supported
          targetDegrees blocks rest
          (fun other hother =>
            hsupport other (by simp [hother])))

private theorem mem_homogenizeQuaternionPolynomial
    (targetDegrees : Nat → Nat) (blocks : Nat) :
    ∀ {polynomial output},
      output ∈
        homogenizeQuaternionPolynomial
          targetDegrees blocks polynomial →
      ∃ source, source ∈ polynomial ∧
        output ∈
          homogenizeQuaternionTerm
            targetDegrees blocks source
  | [], _, houtput => by
      simp [homogenizeQuaternionPolynomial] at houtput
  | source :: rest, output, houtput => by
      simp only [homogenizeQuaternionPolynomial,
        List.mem_append] at houtput
      rcases houtput with houtput | houtput
      · exact ⟨source, by simp, houtput⟩
      · obtain ⟨origin, horigin, houtput⟩ :=
          mem_homogenizeQuaternionPolynomial
            targetDegrees blocks houtput
        exact ⟨origin, by simp [horigin], houtput⟩

theorem homogenizeQuaternionPolynomial_parity
    (targetDegrees : Nat → Nat)
    (blocks : Nat) (polynomial : RatPoly)
    (hparity :
      ∀ left, left ∈ polynomial →
        ∀ right, right ∈ polynomial →
          SameQuaternionParity
            blocks left.1 right.1) :
    ∀ left, left ∈
        homogenizeQuaternionPolynomial
          targetDegrees blocks polynomial →
      ∀ right, right ∈
          homogenizeQuaternionPolynomial
            targetDegrees blocks polynomial →
        SameQuaternionParity
          blocks left.1 right.1 := by
  intro left hleft right hright
  obtain ⟨leftSource, hleftSource,
      hleftGenerated⟩ :=
    mem_homogenizeQuaternionPolynomial
      targetDegrees blocks hleft
  obtain ⟨rightSource, hrightSource,
      hrightGenerated⟩ :=
    mem_homogenizeQuaternionPolynomial
      targetDegrees blocks hright
  exact sameQuaternionParity_trans
      (sameQuaternionParity_symm
        (homogenizeQuaternionTerm_parity
          targetDegrees blocks leftSource
          blocks (Nat.le_refl _)
          left hleftGenerated))
    (sameQuaternionParity_trans
      (hparity leftSource hleftSource
        rightSource hrightSource)
      (homogenizeQuaternionTerm_parity
        targetDegrees blocks rightSource
        blocks (Nat.le_refl _)
        right hrightGenerated))

theorem homogenizeQuaternionPolynomial_degrees
    (targetDegrees : Nat → Nat)
    (blocks : Nat) (polynomial : RatPoly)
    (hle :
      ∀ term, term ∈ polynomial →
        ∀ block, block < blocks →
          quaternionBlockDegree term.1 block ≤
            targetDegrees block)
    (heven :
      ∀ term, term ∈ polynomial →
        ∀ block, block < blocks →
          (targetDegrees block -
            quaternionBlockDegree term.1 block) % 2 = 0) :
    ∀ output, output ∈
        homogenizeQuaternionPolynomial
          targetDegrees blocks polynomial →
      HasQuaternionBlockDegrees
        blocks targetDegrees output.1 := by
  intro output houtput
  obtain ⟨source, hsource, hgenerated⟩ :=
    mem_homogenizeQuaternionPolynomial
      targetDegrees blocks houtput
  intro block hblock
  exact homogenizeQuaternionTerm_target_degree
    targetDegrees blocks source block hblock
    (hle source hsource block hblock)
    (heven source hsource block hblock)
    output hgenerated

/-! ## Haar preservation of the computed homogenization -/

private theorem quaternionHaar_append
    (blocks : Nat) :
    ∀ left right : RatPoly,
      quaternionHaar blocks (left ++ right) ≈
        quaternionHaar blocks left +
          quaternionHaar blocks right
  | [], right =>
      Q'.eqv_symm
        (QPoly.q_zero_add_eqv _)
  | term :: rest, right => by
      change
        term.2 * quaternionHaarMono blocks term.1 +
            quaternionHaar blocks (rest ++ right) ≈
          (term.2 * quaternionHaarMono blocks term.1 +
              quaternionHaar blocks rest) +
            quaternionHaar blocks right
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (quaternionHaar_append
            blocks rest right))
        (Q'.eqv_symm
          (Q'.add_assoc_eqv _ _ _))

private theorem quaternionHaar_polyMul_append_left
    (blocks : Nat) (left right third : RatPoly) :
    quaternionHaar blocks
        (polyMul (left ++ right) third) ≈
      quaternionHaar blocks
          (polyMul left third) +
        quaternionHaar blocks
          (polyMul right third) := by
  simp only [polyMul, List.flatMap_append]
  exact quaternionHaar_append blocks _ _

private theorem quaternionHaar_polyMul_append_right
    (blocks : Nat) (first left right : RatPoly) :
    quaternionHaar blocks
        (polyMul first (left ++ right)) ≈
      quaternionHaar blocks
          (polyMul first left) +
        quaternionHaar blocks
          (polyMul first right) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (left ++ right) first)) _
    (quaternionHaar_polyMul_comm
      blocks first (left ++ right)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
          (polyMul left first) +
      quaternionHaar blocks
          (polyMul right first)) _
    (quaternionHaar_polyMul_append_left
      blocks left right first) ?_
  exact QPoly.q_add_congr
    (quaternionHaar_polyMul_comm
      blocks left first)
    (quaternionHaar_polyMul_comm
      blocks right first)

private theorem polyMul_nil_right
    (polynomial : RatPoly) :
    polyMul polynomial [] = [] := by
  induction polynomial with
  | nil => rfl
  | cons term rest induction =>
      simp [polyMul]

private theorem quaternionHaar_homogenizeTerm_pair
    (totalBlocks : Nat)
    (targetDegrees : Nat → Nat)
    (left right : RatTerm) :
    ∀ processedBlocks,
      processedBlocks ≤ totalBlocks →
      quaternionHaar totalBlocks
          (polyMul
            (homogenizeQuaternionTerm
              targetDegrees processedBlocks left)
            (homogenizeQuaternionTerm
              targetDegrees processedBlocks right)) ≈
        quaternionHaar totalBlocks
          (polyMul [left] [right])
  | 0, _ => Q'.eqv_refl _
  | processedBlocks + 1, hprocessed => by
      unfold homogenizeQuaternionTerm
      refine Q'.eqv_trans _
        (quaternionHaar totalBlocks
          (polyMul
            (homogenizeQuaternionTerm
              targetDegrees processedBlocks left)
            (quaternionRadiusIter processedBlocks
              (quaternionRaiseCount
                targetDegrees processedBlocks right)
              (homogenizeQuaternionTerm
                targetDegrees processedBlocks right)))) _
        (quaternionHaar_radiusIter_pair_left
          totalBlocks processedBlocks
          (by omega) _ _
          (quaternionRaiseCount
            targetDegrees processedBlocks left)) ?_
      refine Q'.eqv_trans _
        (quaternionHaar totalBlocks
          (polyMul
            (homogenizeQuaternionTerm
              targetDegrees processedBlocks left)
            (homogenizeQuaternionTerm
              targetDegrees processedBlocks right))) _
        (quaternionHaar_radiusIter_pair_right
          totalBlocks processedBlocks
          (by omega) _ _
          (quaternionRaiseCount
            targetDegrees processedBlocks right)) ?_
      exact quaternionHaar_homogenizeTerm_pair
        totalBlocks targetDegrees left right
        processedBlocks (by omega)

private theorem quaternionHaar_homogenizeTerm_right
    (blocks : Nat) (targetDegrees : Nat → Nat)
    (left : RatTerm) :
    ∀ right : RatPoly,
      quaternionHaar blocks
          (polyMul
            (homogenizeQuaternionTerm
              targetDegrees blocks left)
            (homogenizeQuaternionPolynomial
              targetDegrees blocks right)) ≈
        quaternionHaar blocks
          (polyMul [left] right)
  | [] => by
      rw [homogenizeQuaternionPolynomial,
        polyMul_nil_right, polyMul_nil_right]
      exact Q'.eqv_refl 0
  | right :: rest => by
      unfold homogenizeQuaternionPolynomial
      refine Q'.eqv_trans _
        (quaternionHaar blocks
              (polyMul
                (homogenizeQuaternionTerm
                  targetDegrees blocks left)
                (homogenizeQuaternionTerm
                  targetDegrees blocks right)) +
          quaternionHaar blocks
              (polyMul
                (homogenizeQuaternionTerm
                  targetDegrees blocks left)
                (homogenizeQuaternionPolynomial
                  targetDegrees blocks rest))) _
        (quaternionHaar_polyMul_append_right
          blocks _ _ _) ?_
      refine Q'.eqv_trans _
        (quaternionHaar blocks
              (polyMul [left] [right]) +
          quaternionHaar blocks
              (polyMul [left] rest)) _
        (QPoly.q_add_congr
          (quaternionHaar_homogenizeTerm_pair
            blocks targetDegrees left right
            blocks (Nat.le_refl _))
          (quaternionHaar_homogenizeTerm_right
            blocks targetDegrees left rest)) ?_
      exact Q'.eqv_symm
        (quaternionHaar_polyMul_append_right
          blocks [left] [right] rest)

theorem quaternionHaar_homogenizePolynomial_pair
    (blocks : Nat) (targetDegrees : Nat → Nat) :
    ∀ left right : RatPoly,
      quaternionHaar blocks
          (polyMul
            (homogenizeQuaternionPolynomial
              targetDegrees blocks left)
            (homogenizeQuaternionPolynomial
              targetDegrees blocks right)) ≈
        quaternionHaar blocks
          (polyMul left right)
  | [], right => by
      simp [homogenizeQuaternionPolynomial,
        polyMul]
      exact Q'.eqv_refl 0
  | left :: rest, right => by
      unfold homogenizeQuaternionPolynomial
      have hright :
          (match right with
            | [] => []
            | term :: tail =>
                homogenizeQuaternionTerm
                    targetDegrees blocks term ++
                  homogenizeQuaternionPolynomial
                    targetDegrees blocks tail) =
            homogenizeQuaternionPolynomial
              targetDegrees blocks right := by
        cases right <;> rfl
      rw [hright]
      change
        quaternionHaar blocks
            (polyMul
              (homogenizeQuaternionTerm
                  targetDegrees blocks left ++
                homogenizeQuaternionPolynomial
                  targetDegrees blocks rest)
              (homogenizeQuaternionPolynomial
                targetDegrees blocks right)) ≈
          quaternionHaar blocks
            (polyMul (left :: rest) right)
      refine Q'.eqv_trans _
        (quaternionHaar blocks
              (polyMul
                (homogenizeQuaternionTerm
                  targetDegrees blocks left)
                (homogenizeQuaternionPolynomial
                  targetDegrees blocks right)) +
          quaternionHaar blocks
              (polyMul
                (homogenizeQuaternionPolynomial
                  targetDegrees blocks rest)
                (homogenizeQuaternionPolynomial
                  targetDegrees blocks right))) _
        (quaternionHaar_polyMul_append_left
          blocks _ _ _) ?_
      refine Q'.eqv_trans _
        (quaternionHaar blocks
              (polyMul [left] right) +
          quaternionHaar blocks
              (polyMul rest right)) _
        (QPoly.q_add_congr
          (quaternionHaar_homogenizeTerm_right
            blocks targetDegrees left right)
          (quaternionHaar_homogenizePolynomial_pair
            blocks targetDegrees rest right)) ?_
      exact Q'.eqv_symm
        (quaternionHaar_polyMul_append_left
          blocks [left] rest right)

/-! ## Computed target degrees inside one parity sector -/

def quaternionBlockDegreeSum
    (block : Nat) : RatPoly → Nat
  | [] => 0
  | term :: rest =>
      quaternionBlockDegree term.1 block +
        quaternionBlockDegreeSum block rest

def targetQuaternionBlockDegree
    (block : Nat) : RatPoly → Nat
  | [] => 0
  | term :: rest =>
      quaternionBlockDegree term.1 block +
        2 * quaternionBlockDegreeSum block rest

private theorem quaternionBlockDegree_le_sum
    (block : Nat) {term : RatTerm} :
    ∀ {polynomial : RatPoly},
      term ∈ polynomial →
      quaternionBlockDegree term.1 block ≤
        quaternionBlockDegreeSum block polynomial
  | [], hterm => by simp at hterm
  | head :: rest, hterm => by
      simp only [List.mem_cons] at hterm
      rcases hterm with rfl | hterm
      · simp [quaternionBlockDegreeSum]
      · have induction :=
          quaternionBlockDegree_le_sum
            block hterm
        simp only [quaternionBlockDegreeSum]
        omega

theorem quaternionBlockDegree_le_target
    (block : Nat) {term : RatTerm} :
    ∀ {polynomial : RatPoly},
      term ∈ polynomial →
      quaternionBlockDegree term.1 block ≤
        targetQuaternionBlockDegree block polynomial
  | [], hterm => by simp at hterm
  | head :: rest, hterm => by
      simp only [List.mem_cons] at hterm
      rcases hterm with rfl | hterm
      · simp [targetQuaternionBlockDegree]
      · have hsum :=
          quaternionBlockDegree_le_sum
            block hterm
        simp only [targetQuaternionBlockDegree]
        omega

private theorem quaternionBlockDegree_mod_two_eq_of_parity
    {blocks block : Nat} {left right : List Nat}
    (hblock : block < blocks)
    (hparity :
      SameQuaternionParity blocks left right) :
    quaternionBlockDegree left block % 2 =
      quaternionBlockDegree right block % 2 := by
  have h0 := hparity (4 * block) (by omega)
  have h1 := hparity (4 * block + 1) (by omega)
  have h2 := hparity (4 * block + 2) (by omega)
  have h3 := hparity (4 * block + 3) (by omega)
  unfold quaternionBlockDegree
  omega

theorem targetQuaternionBlockDegree_even_gap
    {blocks block : Nat}
    {term : RatTerm} {polynomial : RatPoly}
    (hblock : block < blocks)
    (hterm : term ∈ polynomial)
    (hparity :
      ∀ left, left ∈ polynomial →
        ∀ right, right ∈ polynomial →
          SameQuaternionParity
            blocks left.1 right.1) :
    (targetQuaternionBlockDegree block polynomial -
      quaternionBlockDegree term.1 block) % 2 = 0 := by
  cases polynomial with
  | nil => simp at hterm
  | cons head rest =>
      have hmod :=
        quaternionBlockDegree_mod_two_eq_of_parity
          hblock
          (hparity head (by simp)
            term hterm)
      have hle :=
        quaternionBlockDegree_le_target
          block hterm
      simp only [targetQuaternionBlockDegree]
      omega

/-- Positivity for every finite polynomial contained in one arbitrary-product
coordinate-parity sector.  The common block degrees are computed from the
input and inserted by exact sphere-radius identities. -/
theorem quaternionHaar_square_nonnegative_of_parity
    (blocks : Nat) (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial)
    (hparity :
      ∀ left, left ∈ polynomial →
        ∀ right, right ∈ polynomial →
          SameQuaternionParity
            blocks left.1 right.1) :
    (0 : Q') ≤
      quaternionHaar blocks
        (polyMul polynomial polynomial) := by
  let targetDegrees :=
    fun block =>
      targetQuaternionBlockDegree
        block polynomial
  let homogeneous :=
    homogenizeQuaternionPolynomial
      targetDegrees blocks polynomial
  have hhomogeneousSupport :
      SupportedQuaternionBlocks
        blocks homogeneous :=
    homogenizeQuaternionPolynomial_supported
      targetDegrees blocks polynomial hsupport
  have hhomogeneousParity :
      ∀ left, left ∈ homogeneous →
        ∀ right, right ∈ homogeneous →
          SameQuaternionParity
            blocks left.1 right.1 :=
    homogenizeQuaternionPolynomial_parity
      targetDegrees blocks polynomial hparity
  have hhomogeneousDegree :
      ∀ term, term ∈ homogeneous →
        HasQuaternionBlockDegrees
          blocks targetDegrees term.1 :=
    homogenizeQuaternionPolynomial_degrees
      targetDegrees blocks polynomial
      (fun term hterm block hblock =>
        quaternionBlockDegree_le_target
          block hterm)
      (fun term hterm block hblock =>
        targetQuaternionBlockDegree_even_gap
          hblock hterm hparity)
  have hnonnegative :=
    quaternionHaar_square_nonnegative_of_fixed_sector
      blocks targetDegrees homogeneous
      hhomogeneousSupport
      hhomogeneousParity
      hhomogeneousDegree
  exact Q'.le_trans' _ _ _ hnonnegative
    (Q'.le_of_eqv
      (quaternionHaar_homogenizePolynomial_pair
        blocks targetDegrees
        polynomial polynomial))

end YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization.quaternionHaar_polyMul_comm
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization.quaternionHaar_polyMul_middle_comm
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization.quaternionHaar_polyMul_assoc
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization.quaternionHaar_radiusIter_pair_left
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization.homogenizeQuaternionTerm_target_degree
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization.quaternionHaar_homogenizePolynomial_pair
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization.quaternionHaar_square_nonnegative_of_parity
