/-
# Sphere-ideal descent for an arbitrary product of quaternion Haar factors

The earlier sphere-ideal development was specialized to two quaternion
blocks.  The BF4 endpoint carrier has ten blocks.  This file proves the same
radius-square descent uniformly in the block count:

* `quaternionRadiusPolynomial b` is the four-coordinate polynomial
  `x_(4b)^2 + ... + x_(4b+3)^2`;
* multiplication by this polynomial does not change the exact normalized
  `quaternionHaar blocks` functional whenever `b < blocks`;
* the statement is proved first for one monomial and then by finite
  linearity, with no appeal to a measure or an unproved positivity axiom.

These identities are the algebraic engine for blockwise homogenization of a
forty-coordinate BF4 polynomial.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
import YMGap.Continuum.SU2QuaternionHaarSphereIdeal

namespace YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

local infix:50 " ≈ " => Q'.eqv

/-- The exponent vector of the square of coordinate `coordinate`. -/
def coordinateSquareMono : Nat → List Nat
  | 0 => [2]
  | coordinate + 1 => 0 :: coordinateSquareMono coordinate

theorem coordinateSquareMono_length (coordinate : Nat) :
    (coordinateSquareMono coordinate).length = coordinate + 1 := by
  induction coordinate with
  | zero => rfl
  | succ coordinate induction =>
      simp [coordinateSquareMono, induction]

theorem exponentAt_coordinateSquareMono
    (coordinate index : Nat) :
    exponentAt (coordinateSquareMono coordinate) index =
      if index = coordinate then 2 else 0 := by
  induction coordinate generalizing index with
  | zero =>
      cases index with
      | zero => rfl
      | succ index =>
          change
            ([2].getD (index + 1) 0) =
              if index + 1 = 0 then 2 else 0
          rw [List.getD_cons_succ, List.getD_nil]
          rw [if_neg (Nat.succ_ne_zero index)]
  | succ coordinate induction =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [coordinateSquareMono, exponentAt]
          change
            exponentAt (coordinateSquareMono coordinate) index =
              if index + 1 = coordinate + 1 then 2 else 0
          rw [induction index]
          by_cases hindex : index = coordinate
          · have hsucc :
                index + 1 = coordinate + 1 :=
              congrArg (fun value => value + 1) hindex
            simp only [if_pos hindex, if_pos hsucc]
          · have hsucc :
                index + 1 ≠ coordinate + 1 := by
              intro equality
              exact hindex
                (Nat.add_right_cancel equality)
            simp only [if_neg hindex, if_neg hsucc]

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

private theorem exponentAt_drop
    (monomial : List Nat) :
    ∀ (offset index : Nat),
      exponentAt (monomial.drop offset) index =
        exponentAt monomial (offset + index)
  | 0, index => by
      simp [exponentAt]
  | offset + 1, index => by
      cases monomial with
      | nil => simp [exponentAt]
      | cons exponent rest =>
          have hindex :
              offset + 1 + index =
                (offset + index) + 1 := by
            omega
          rw [hindex]
          simp only [List.drop_succ_cons]
          unfold exponentAt
          simp only [List.getD_cons_succ]
          exact exponentAt_drop rest offset index

/-- The literal radius-square polynomial for quaternion block `block`. -/
def quaternionRadiusPolynomial (block : Nat) : RatPoly :=
  [ (coordinateSquareMono (4 * block), 1),
    (coordinateSquareMono (4 * block + 1), 1),
    (coordinateSquareMono (4 * block + 2), 1),
    (coordinateSquareMono (4 * block + 3), 1) ]

private theorem quaternionHaarRange_square_before
    (monomial : List Nat) :
    ∀ (start blocks coordinate : Nat),
      coordinate < start →
      quaternionHaarRange start blocks
          (monoMul monomial
            (coordinateSquareMono coordinate)) =
        quaternionHaarRange start blocks monomial
  | _, 0, _, _ => rfl
  | start, blocks + 1, coordinate, hcoordinate => by
      unfold quaternionHaarRange
      have h0 : start ≠ coordinate := by omega
      have h1 : start + 1 ≠ coordinate := by omega
      have h2 : start + 2 ≠ coordinate := by omega
      have h3 : start + 3 ≠ coordinate := by omega
      rw [exponentAt_monoMul, exponentAt_monoMul,
        exponentAt_monoMul, exponentAt_monoMul,
        exponentAt_coordinateSquareMono,
        exponentAt_coordinateSquareMono,
        exponentAt_coordinateSquareMono,
        exponentAt_coordinateSquareMono,
        if_neg h0, if_neg h1, if_neg h2, if_neg h3]
      simp only [Nat.add_zero]
      rw [quaternionHaarRange_square_before
        monomial (start + 4) blocks coordinate
        (by omega)]

private theorem four_left_factor
    (head a b c d : Q') :
    head * a + (head * b + (head * c + head * d)) ≈
      head * (a + (b + (c + d))) := by
  refine Q'.eqv_trans _
    (head * a +
      (head * b + head * (c + d))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (Q'.mul_add_eqv head c d)))
  · refine Q'.eqv_trans _
      (head * a +
        head * (b + (c + d))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (Q'.mul_add_eqv head b (c + d)))
    · exact Q'.eqv_symm
        (Q'.mul_add_eqv head a (b + (c + d)))

private theorem four_right_factor
    (a b c d tail : Q') :
    a * tail + (b * tail + (c * tail + d * tail)) ≈
      (a + (b + (c + d))) * tail := by
  refine Q'.eqv_trans _
    (a * tail +
      (b * tail + (c + d) * tail)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (Q'.add_mul_eqv c d tail)))
  · refine Q'.eqv_trans _
      (a * tail +
        (b + (c + d)) * tail) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (Q'.add_mul_eqv b (c + d) tail))
    · exact Q'.eqv_symm
        (Q'.add_mul_eqv a (b + (c + d)) tail)

private theorem sphereMoment4_monoMul_square_after
    (monomial : List Nat) (start coordinate : Nat)
    (hcoordinate : start + 4 ≤ coordinate) :
    sphereMoment4
          (exponentAt
            (monoMul monomial
              (coordinateSquareMono coordinate)) start)
          (exponentAt
            (monoMul monomial
              (coordinateSquareMono coordinate)) (start + 1))
          (exponentAt
            (monoMul monomial
              (coordinateSquareMono coordinate)) (start + 2))
          (exponentAt
            (monoMul monomial
              (coordinateSquareMono coordinate)) (start + 3)) =
      sphereMoment4
          (exponentAt monomial start)
          (exponentAt monomial (start + 1))
          (exponentAt monomial (start + 2))
          (exponentAt monomial (start + 3)) := by
  have h0 : start ≠ coordinate := by omega
  have h1 : start + 1 ≠ coordinate := by omega
  have h2 : start + 2 ≠ coordinate := by omega
  have h3 : start + 3 ≠ coordinate := by omega
  simp only [exponentAt_monoMul,
    exponentAt_coordinateSquareMono,
    if_neg h0, if_neg h1, if_neg h2, if_neg h3,
    Nat.add_zero]

private theorem quaternionHaarRange_mul_radius
    (monomial : List Nat) :
    ∀ (start blocks block : Nat),
      block < blocks →
      quaternionHaarRange start blocks
          (monoMul monomial
            (coordinateSquareMono
              (start + 4 * block))) +
        (quaternionHaarRange start blocks
            (monoMul monomial
              (coordinateSquareMono
                (start + 4 * block + 1))) +
          (quaternionHaarRange start blocks
              (monoMul monomial
                (coordinateSquareMono
                  (start + 4 * block + 2))) +
            quaternionHaarRange start blocks
              (monoMul monomial
                (coordinateSquareMono
                  (start + 4 * block + 3))))) ≈
        quaternionHaarRange start blocks monomial
  | _, 0, _, hblock => by omega
  | start, blocks + 1, 0, _ => by
      unfold quaternionHaarRange
      simp only [Nat.mul_zero, Nat.add_zero,
        exponentAt_monoMul,
        exponentAt_coordinateSquareMono]
      have htail0 :=
        quaternionHaarRange_square_before
          monomial (start + 4) blocks start
          (by omega)
      have htail1 :=
        quaternionHaarRange_square_before
          monomial (start + 4) blocks (start + 1)
          (by omega)
      have htail2 :=
        quaternionHaarRange_square_before
          monomial (start + 4) blocks (start + 2)
          (by omega)
      have htail3 :=
        quaternionHaarRange_square_before
          monomial (start + 4) blocks (start + 3)
          (by omega)
      simp only [if_neg (by omega : start + 1 ≠ start),
        if_neg (by omega : start + 2 ≠ start),
        if_neg (by omega : start + 3 ≠ start),
        if_neg (by omega : start ≠ start + 1),
        if_neg (by omega : start + 2 ≠ start + 1),
        if_neg (by omega : start + 3 ≠ start + 1),
        if_neg (by omega : start ≠ start + 2),
        if_neg (by omega : start + 1 ≠ start + 2),
        if_neg (by omega : start + 3 ≠ start + 2),
        if_neg (by omega : start ≠ start + 3),
        if_neg (by omega : start + 1 ≠ start + 3),
        if_neg (by omega : start + 2 ≠ start + 3),
        Nat.add_zero] at *
      rw [htail0, htail1, htail2, htail3]
      refine Q'.eqv_trans _
        ((sphereMoment4
              (exponentAt monomial start + 2)
              (exponentAt monomial (start + 1))
              (exponentAt monomial (start + 2))
              (exponentAt monomial (start + 3)) +
            (sphereMoment4
                (exponentAt monomial start)
                (exponentAt monomial (start + 1) + 2)
                (exponentAt monomial (start + 2))
                (exponentAt monomial (start + 3)) +
              (sphereMoment4
                  (exponentAt monomial start)
                  (exponentAt monomial (start + 1))
                  (exponentAt monomial (start + 2) + 2)
                  (exponentAt monomial (start + 3)) +
                sphereMoment4
                  (exponentAt monomial start)
                  (exponentAt monomial (start + 1))
                  (exponentAt monomial (start + 2))
                  (exponentAt monomial (start + 3) + 2)))) *
          quaternionHaarRange
            (start + 4) blocks monomial) _
        (four_right_factor _ _ _ _ _) ?_
      exact Q'.mul_eqv_congr_right _ _ _
        (sphereMoment4_radius
          (exponentAt monomial start)
          (exponentAt monomial (start + 1))
          (exponentAt monomial (start + 2))
          (exponentAt monomial (start + 3)))
  | start, blocks + 1, block + 1, hblock => by
      unfold quaternionHaarRange
      rw [sphereMoment4_monoMul_square_after
          monomial start
          (start + 4 * (block + 1)) (by omega),
        sphereMoment4_monoMul_square_after
          monomial start
          (start + 4 * (block + 1) + 1) (by omega),
        sphereMoment4_monoMul_square_after
          monomial start
          (start + 4 * (block + 1) + 2) (by omega),
        sphereMoment4_monoMul_square_after
          monomial start
          (start + 4 * (block + 1) + 3) (by omega)]
      have hcoordinate :
          start + 4 * (block + 1) =
            start + 4 + 4 * block := by omega
      rw [hcoordinate]
      let head :=
        sphereMoment4
          (exponentAt monomial start)
          (exponentAt monomial (start + 1))
          (exponentAt monomial (start + 2))
          (exponentAt monomial (start + 3))
      let tail0 :=
        quaternionHaarRange (start + 4) blocks
          (monoMul monomial
            (coordinateSquareMono
              (start + 4 + 4 * block)))
      let tail1 :=
        quaternionHaarRange (start + 4) blocks
          (monoMul monomial
            (coordinateSquareMono
              (start + 4 + 4 * block + 1)))
      let tail2 :=
        quaternionHaarRange (start + 4) blocks
          (monoMul monomial
            (coordinateSquareMono
              (start + 4 + 4 * block + 2)))
      let tail3 :=
        quaternionHaarRange (start + 4) blocks
          (monoMul monomial
            (coordinateSquareMono
              (start + 4 + 4 * block + 3)))
      let tail :=
        quaternionHaarRange
          (start + 4) blocks monomial
      change
        head * tail0 +
            (head * tail1 +
              (head * tail2 + head * tail3)) ≈
          head * tail
      refine Q'.eqv_trans _
        (head * (tail0 + (tail1 + (tail2 + tail3)))) _
        (four_left_factor _ _ _ _ _) ?_
      have htail :=
        quaternionHaarRange_mul_radius
          monomial (start + 4) blocks block
          (by omega)
      exact Q'.mul_eqv_congr_left _ _ _ htail

private theorem quaternionHaarPrefix_drop_eq_range
    (monomial : List Nat) :
    ∀ (start blocks : Nat),
      quaternionHaarPrefix blocks
          (monomial.drop start) ≈
        quaternionHaarRange start blocks monomial
  | _, 0 => Q'.eqv_refl 1
  | start, blocks + 1 => by
      unfold quaternionHaarPrefix quaternionHaarRange
      rw [exponentAt_drop monomial start 0,
        exponentAt_drop monomial start 1,
        exponentAt_drop monomial start 2,
        exponentAt_drop monomial start 3]
      simp only [Nat.add_zero]
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      have induction :=
        quaternionHaarPrefix_drop_eq_range
          monomial (start + 4) blocks
      simpa [List.drop_drop, Nat.add_assoc] using induction

private theorem quaternionHaarPrefix_eq_range
    (monomial : List Nat) (blocks : Nat) :
    quaternionHaarPrefix blocks monomial ≈
      quaternionHaarRange 0 blocks monomial := by
  simpa using
    quaternionHaarPrefix_drop_eq_range
      monomial 0 blocks

/-- Monomial-level descent through the radius relation in any retained
quaternion block. -/
theorem quaternionHaarMono_mul_radius
    (blocks block : Nat) (hblock : block < blocks)
    (monomial : List Nat) :
    quaternionHaarMono blocks
        (monoMul monomial
          (coordinateSquareMono (4 * block))) +
      (quaternionHaarMono blocks
          (monoMul monomial
            (coordinateSquareMono (4 * block + 1))) +
        (quaternionHaarMono blocks
            (monoMul monomial
              (coordinateSquareMono (4 * block + 2))) +
          quaternionHaarMono blocks
            (monoMul monomial
              (coordinateSquareMono (4 * block + 3))))) ≈
      quaternionHaarMono blocks monomial := by
  have hs0 :
      (coordinateSquareMono (4 * block)).length ≤
        4 * blocks := by
    rw [coordinateSquareMono_length]
    omega
  have hs1 :
      (coordinateSquareMono (4 * block + 1)).length ≤
        4 * blocks := by
    rw [coordinateSquareMono_length]
    omega
  have hs2 :
      (coordinateSquareMono (4 * block + 2)).length ≤
        4 * blocks := by
    rw [coordinateSquareMono_length]
    omega
  have hs3 :
      (coordinateSquareMono (4 * block + 3)).length ≤
        4 * blocks := by
    rw [coordinateSquareMono_length]
    omega
  have hdrop0 :=
    monoMul_drop_of_length_le monomial
      (coordinateSquareMono (4 * block))
      (4 * blocks) hs0
  have hdrop1 :=
    monoMul_drop_of_length_le monomial
      (coordinateSquareMono (4 * block + 1))
      (4 * blocks) hs1
  have hdrop2 :=
    monoMul_drop_of_length_le monomial
      (coordinateSquareMono (4 * block + 2))
      (4 * blocks) hs2
  have hdrop3 :=
    monoMul_drop_of_length_le monomial
      (coordinateSquareMono (4 * block + 3))
      (4 * blocks) hs3
  unfold quaternionHaarMono
  rw [hdrop0, hdrop1, hdrop2, hdrop3]
  split
  next htail =>
    let range0 :=
      quaternionHaarRange 0 blocks
        (monoMul monomial
          (coordinateSquareMono (4 * block)))
    let range1 :=
      quaternionHaarRange 0 blocks
        (monoMul monomial
          (coordinateSquareMono (4 * block + 1)))
    let range2 :=
      quaternionHaarRange 0 blocks
        (monoMul monomial
          (coordinateSquareMono (4 * block + 2)))
    let range3 :=
      quaternionHaarRange 0 blocks
        (monoMul monomial
          (coordinateSquareMono (4 * block + 3)))
    refine Q'.eqv_trans _
      (range0 + (range1 + (range2 + range3))) _ ?_ ?_
    · exact QPoly.q_add_congr
        (quaternionHaarPrefix_eq_range _ blocks)
        (QPoly.q_add_congr
          (quaternionHaarPrefix_eq_range _ blocks)
          (QPoly.q_add_congr
            (quaternionHaarPrefix_eq_range _ blocks)
            (quaternionHaarPrefix_eq_range _ blocks)))
    · have hradius :=
        quaternionHaarRange_mul_radius
          monomial 0 blocks block hblock
      refine Q'.eqv_trans _
        (quaternionHaarRange 0 blocks monomial) _ ?_ ?_
      · simpa [range0, range1, range2, range3] using
          hradius
      · exact
        (Q'.eqv_symm
          (quaternionHaarPrefix_eq_range
            monomial blocks))
  next htail =>
    have h00 :
        (0 : Q') + 0 ≈ 0 :=
      QPoly.q_zero_add_eqv 0
    have h000 :
        (0 : Q') + (0 + 0) ≈ 0 :=
      Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr_left 0 _ _ h00)
        h00
    exact Q'.eqv_trans _ (0 + 0) _
      (Q'.add_eqv_congr_left 0 _ _ h000)
      h00

private theorem quaternionHaar_append
    (blocks : Nat) :
    ∀ left right : RatPoly,
      quaternionHaar blocks (left ++ right) ≈
        quaternionHaar blocks left +
          quaternionHaar blocks right
  | [], right =>
      Q'.eqv_symm
        (QPoly.q_zero_add_eqv
          (quaternionHaar blocks right))
  | term :: rest, right => by
      change
        term.2 * quaternionHaarMono blocks term.1 +
            quaternionHaar blocks (rest ++ right) ≈
          (term.2 * quaternionHaarMono blocks term.1 +
              quaternionHaar blocks rest) +
            quaternionHaar blocks right
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (quaternionHaar_append blocks rest right)) ?_
      exact Q'.eqv_symm
        (Q'.add_assoc_eqv _ _ _)

private theorem scaled_four_radius
    (coefficient a b c d value : Q')
    (hradius : a + (b + (c + d)) ≈ value) :
    (coefficient * 1) * a +
        ((coefficient * 1) * b +
          ((coefficient * 1) * c +
            (coefficient * 1) * d)) ≈
      coefficient * value := by
  have hone :
      coefficient * 1 ≈ coefficient :=
    Q'.mul_one_eqv coefficient
  refine Q'.eqv_trans _
    (coefficient * a +
      (coefficient * b +
        (coefficient * c +
          coefficient * d))) _ ?_ ?_
  · exact QPoly.q_add_congr
      (Q'.mul_eqv_congr_right _ _ _ hone)
      (QPoly.q_add_congr
        (Q'.mul_eqv_congr_right _ _ _ hone)
        (QPoly.q_add_congr
          (Q'.mul_eqv_congr_right _ _ _ hone)
          (Q'.mul_eqv_congr_right _ _ _ hone)))
  · exact Q'.eqv_trans _
      (coefficient * (a + (b + (c + d)))) _
      (four_left_factor _ _ _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ hradius)

private theorem quaternionHaar_mul_radius_single
    (blocks block : Nat) (hblock : block < blocks)
    (monomial : List Nat) (coefficient : Q') :
    quaternionHaar blocks
        (polyMul [(monomial, coefficient)]
          (quaternionRadiusPolynomial block)) ≈
      quaternionHaar blocks [(monomial, coefficient)] := by
  change
    (coefficient * 1) *
          quaternionHaarMono blocks
            (monoMul monomial
              (coordinateSquareMono (4 * block))) +
      ((coefficient * 1) *
            quaternionHaarMono blocks
              (monoMul monomial
                (coordinateSquareMono
                  (4 * block + 1))) +
        ((coefficient * 1) *
              quaternionHaarMono blocks
                (monoMul monomial
                  (coordinateSquareMono
                    (4 * block + 2))) +
          ((coefficient * 1) *
                quaternionHaarMono blocks
                  (monoMul monomial
                    (coordinateSquareMono
                      (4 * block + 3))) +
            0))) ≈
      coefficient *
          quaternionHaarMono blocks monomial +
        0
  rw [Q'.add_zero', Q'.add_zero']
  exact scaled_four_radius _ _ _ _ _ _
    (quaternionHaarMono_mul_radius
      blocks block hblock monomial)

/-- Multiplication by the radius-square polynomial of any retained block is
the identity under exact product Haar. -/
theorem quaternionHaar_mul_radius
    (blocks block : Nat) (hblock : block < blocks) :
    ∀ polynomial : RatPoly,
      quaternionHaar blocks
          (polyMul polynomial
            (quaternionRadiusPolynomial block)) ≈
        quaternionHaar blocks polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      have hmul :
          polyMul (term :: rest)
              (quaternionRadiusPolynomial block) =
            polyMul [term]
                (quaternionRadiusPolynomial block) ++
              polyMul rest
                (quaternionRadiusPolynomial block) := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (quaternionHaar blocks
              (polyMul [term]
                (quaternionRadiusPolynomial block)) +
          quaternionHaar blocks
              (polyMul rest
                (quaternionRadiusPolynomial block))) _
        (quaternionHaar_append blocks _ _) ?_
      refine Q'.eqv_trans _
        (quaternionHaar blocks [term] +
          quaternionHaar blocks rest) _
        (QPoly.q_add_congr
          (quaternionHaar_mul_radius_single
            blocks block hblock term.1 term.2)
          (quaternionHaar_mul_radius
            blocks block hblock rest)) ?_
      change
        quaternionHaar blocks [term] +
            quaternionHaar blocks rest ≈
          quaternionHaar blocks ([term] ++ rest)
      exact Q'.eqv_symm
        (quaternionHaar_append
          blocks [term] rest)

end YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal

#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal.exponentAt_coordinateSquareMono
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal.quaternionHaarMono_mul_radius
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal.quaternionHaar_mul_radius
