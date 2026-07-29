/-
# Four-factor permutation under arbitrary-product quaternion Haar

The finite Wilson SOS layer already contained the two-block identity

  H((p q)(r s)) = H((p r)(q s)).

This file proves the same statement for `quaternionHaar blocks`, with no
restriction on the number of retained `SU(2)` factors.  The proof expands
the four finite polynomial lists, swaps the middle two summations, and uses
commutativity of rational coefficients and exponent-vector addition in each
cell.  It is the exact Fubini step needed to turn `P² L²` into `(P L)²`.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

namespace YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

local infix:50 " ≈ " => Q'.eqv

private theorem monoMul_four_swap
    (a b c d : List Nat) :
    monoMul (monoMul a b) (monoMul c d) =
      monoMul (monoMul a c) (monoMul b d) := by
  calc
    monoMul (monoMul a b) (monoMul c d) =
        monoMul a (monoMul b (monoMul c d)) :=
      YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.monoMul_assoc
        a b (monoMul c d)
    _ = monoMul a (monoMul (monoMul b c) d) := by
      rw [
        YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.monoMul_assoc
          b c d]
    _ = monoMul a (monoMul (monoMul c b) d) := by
      rw [
        YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.monoMul_comm
          b c]
    _ = monoMul a (monoMul c (monoMul b d)) := by
      rw [
        YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.monoMul_assoc
          c b d]
    _ = monoMul (monoMul a c) (monoMul b d) := by
      rw [
        YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.monoMul_assoc
          a c (monoMul b d)]

private def termMul (a b : RatTerm) : RatTerm :=
  (monoMul a.1 b.1, a.2 * b.2)

private def haarQuadCell
    (blocks : Nat) (a b c d : RatTerm) : Q' :=
  ((a.2 * b.2) * (c.2 * d.2)) *
    quaternionHaarMono blocks
      (monoMul (monoMul a.1 b.1)
        (monoMul c.1 d.1))

private def haarQuadLast
    (blocks : Nat) (a b c : RatTerm) :
    RatPoly → Q'
  | [] => 0
  | d :: rest =>
      haarQuadCell blocks a b c d +
        haarQuadLast blocks a b c rest

private def haarQuadThird
    (blocks : Nat) (a b : RatTerm) :
    RatPoly → RatPoly → Q'
  | [], _ => 0
  | c :: rest, fourth =>
      haarQuadLast blocks a b c fourth +
        haarQuadThird blocks a b rest fourth

private def haarQuadSecond
    (blocks : Nat) (a : RatTerm) :
    RatPoly → RatPoly → RatPoly → Q'
  | [], _, _ => 0
  | b :: rest, third, fourth =>
      haarQuadThird blocks a b third fourth +
        haarQuadSecond blocks a rest third fourth

private def haarQuad
    (blocks : Nat) :
    RatPoly → RatPoly → RatPoly → RatPoly → Q'
  | [], _, _, _ => 0
  | a :: rest, second, third, fourth =>
      haarQuadSecond blocks a second third fourth +
        haarQuad blocks rest second third fourth

private theorem quaternionHaarRow_append
    (blocks : Nat) (a : RatTerm) :
    ∀ left right : RatPoly,
      quaternionHaarRow blocks a (left ++ right) ≈
        quaternionHaarRow blocks a left +
          quaternionHaarRow blocks a right
  | [], right =>
      Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | b :: left, right => by
      change
        _ + quaternionHaarRow blocks a
              (left ++ right) ≈
          (_ + quaternionHaarRow blocks a left) +
            quaternionHaarRow blocks a right
      refine Q'.eqv_trans _
        (_ + (quaternionHaarRow blocks a left +
          quaternionHaarRow blocks a right)) _
        (Q'.add_eqv_congr_left _ _ _
          (quaternionHaarRow_append
            blocks a left right)) ?_
      exact Q'.eqv_symm
        (Q'.add_assoc_eqv _ _ _)

private theorem quaternionHaarBilinear_append_left
    (blocks : Nat) :
    ∀ left right third : RatPoly,
      quaternionHaarBilinear blocks
          (left ++ right) third ≈
        quaternionHaarBilinear blocks left third +
          quaternionHaarBilinear blocks right third
  | [], right, third =>
      Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | a :: left, right, third => by
      change
        quaternionHaarRow blocks a third +
            quaternionHaarBilinear blocks
              (left ++ right) third ≈
          (quaternionHaarRow blocks a third +
              quaternionHaarBilinear blocks
                left third) +
            quaternionHaarBilinear blocks right third
      refine Q'.eqv_trans _
        (quaternionHaarRow blocks a third +
          (quaternionHaarBilinear blocks left third +
            quaternionHaarBilinear blocks right third)) _
        (Q'.add_eqv_congr_left _ _ _
          (quaternionHaarBilinear_append_left
            blocks left right third)) ?_
      exact Q'.eqv_symm
        (Q'.add_assoc_eqv _ _ _)

private theorem quaternionHaarRow_single_polyMul
    (blocks : Nat) (a b c : RatTerm) :
    ∀ fourth : RatPoly,
      quaternionHaarRow blocks (termMul a b)
          (polyMul [c] fourth) ≈
        haarQuadLast blocks a b c fourth
  | [] => Q'.eqv_refl 0
  | d :: rest => by
      change
        haarQuadCell blocks a b c d +
            quaternionHaarRow blocks
              (termMul a b) (polyMul [c] rest) ≈
          haarQuadCell blocks a b c d +
            haarQuadLast blocks a b c rest
      exact Q'.add_eqv_congr_left _ _ _
        (quaternionHaarRow_single_polyMul
          blocks a b c rest)

private theorem quaternionHaarRow_polyMul
    (blocks : Nat) (a b : RatTerm) :
    ∀ third fourth : RatPoly,
      quaternionHaarRow blocks (termMul a b)
          (polyMul third fourth) ≈
        haarQuadThird blocks a b third fourth
  | [], _ => Q'.eqv_refl 0
  | c :: rest, fourth => by
      have hmul :
          polyMul (c :: rest) fourth =
            polyMul [c] fourth ++
              polyMul rest fourth := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (quaternionHaarRow blocks
              (termMul a b) (polyMul [c] fourth) +
          quaternionHaarRow blocks
              (termMul a b) (polyMul rest fourth)) _
        (quaternionHaarRow_append
          blocks _ _ _) ?_
      exact QPoly.q_add_congr
        (quaternionHaarRow_single_polyMul
          blocks a b c fourth)
        (quaternionHaarRow_polyMul
          blocks a b rest fourth)

private theorem quaternionHaarBilinear_single_polyMul
    (blocks : Nat) (a : RatTerm) :
    ∀ second third fourth : RatPoly,
      quaternionHaarBilinear blocks
          (polyMul [a] second)
          (polyMul third fourth) ≈
        haarQuadSecond blocks a second third fourth
  | [], _, _ => Q'.eqv_refl 0
  | b :: rest, third, fourth => by
      change
        quaternionHaarRow blocks
              (termMul a b) (polyMul third fourth) +
            quaternionHaarBilinear blocks
              (polyMul [a] rest)
              (polyMul third fourth) ≈
          haarQuadThird blocks a b third fourth +
            haarQuadSecond blocks a rest third fourth
      exact QPoly.q_add_congr
        (quaternionHaarRow_polyMul
          blocks a b third fourth)
        (quaternionHaarBilinear_single_polyMul
          blocks a rest third fourth)

private theorem quaternionHaarBilinear_polyMul_both
    (blocks : Nat) :
    ∀ first second third fourth : RatPoly,
      quaternionHaarBilinear blocks
          (polyMul first second)
          (polyMul third fourth) ≈
        haarQuad blocks first second third fourth
  | [], _, _, _ => Q'.eqv_refl 0
  | a :: rest, second, third, fourth => by
      have hmul :
          polyMul (a :: rest) second =
            polyMul [a] second ++
              polyMul rest second := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (quaternionHaarBilinear blocks
              (polyMul [a] second)
              (polyMul third fourth) +
          quaternionHaarBilinear blocks
              (polyMul rest second)
              (polyMul third fourth)) _
        (quaternionHaarBilinear_append_left
          blocks _ _ _) ?_
      exact QPoly.q_add_congr
        (quaternionHaarBilinear_single_polyMul
          blocks a second third fourth)
        (quaternionHaarBilinear_polyMul_both
          blocks rest second third fourth)

private theorem quaternionHaarFour_eq_quad
    (blocks : Nat) (first second third fourth : RatPoly) :
    quaternionHaar blocks
        (polyMul (polyMul first second)
          (polyMul third fourth)) ≈
      haarQuad blocks first second third fourth := by
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul
      blocks (polyMul first second)
        (polyMul third fourth))
    (quaternionHaarBilinear_polyMul_both
      blocks first second third fourth)

private theorem haarQuadCell_swap
    (blocks : Nat) (a b c d : RatTerm) :
    haarQuadCell blocks a b c d ≈
      haarQuadCell blocks a c b d := by
  unfold haarQuadCell
  rw [monoMul_four_swap a.1 b.1 c.1 d.1]
  exact Q'.mul_eqv_congr_right _ _ _
    (q_mul4_swap a.2 b.2 c.2 d.2)

private theorem haarQuadLast_swap
    (blocks : Nat) (a b c : RatTerm) :
    ∀ fourth : RatPoly,
      haarQuadLast blocks a b c fourth ≈
        haarQuadLast blocks a c b fourth
  | [] => Q'.eqv_refl 0
  | d :: rest =>
      QPoly.q_add_congr
        (haarQuadCell_swap blocks a b c d)
        (haarQuadLast_swap blocks a b c rest)

private theorem haarQuadThird_single
    (blocks : Nat) (a b c : RatTerm)
    (fourth : RatPoly) :
    haarQuadThird blocks a b [c] fourth ≈
      haarQuadLast blocks a b c fourth := by
  change
    haarQuadLast blocks a b c fourth + 0 ≈
      haarQuadLast blocks a b c fourth
  exact QPoly.q_add_zero_eqv _

private theorem haarQuadThird_append
    (blocks : Nat) (a b : RatTerm) :
    ∀ left right fourth : RatPoly,
      haarQuadThird blocks a b
          (left ++ right) fourth ≈
        haarQuadThird blocks a b left fourth +
          haarQuadThird blocks a b right fourth
  | [], right, fourth =>
      Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | c :: left, right, fourth => by
      change
        haarQuadLast blocks a b c fourth +
            haarQuadThird blocks a b
              (left ++ right) fourth ≈
          (haarQuadLast blocks a b c fourth +
              haarQuadThird blocks a b left fourth) +
            haarQuadThird blocks a b right fourth
      refine Q'.eqv_trans _
        (haarQuadLast blocks a b c fourth +
          (haarQuadThird blocks a b left fourth +
            haarQuadThird blocks a b right fourth)) _
        (Q'.add_eqv_congr_left _ _ _
          (haarQuadThird_append
            blocks a b left right fourth)) ?_
      exact Q'.eqv_symm
        (Q'.add_assoc_eqv _ _ _)

private theorem q_add4_swap (a b c d : Q') :
    (a + b) + (c + d) ≈
      (a + c) + (b + d) := by
  refine Q'.eqv_trans _
    (a + (b + (c + d))) _
    (Q'.add_assoc_eqv a b (c + d)) ?_
  refine Q'.eqv_trans _
    (a + ((b + c) + d)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _
    (a + ((c + b) + d)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_comm_eqv b c))) ?_
  refine Q'.eqv_trans _
    (a + (c + (b + d))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm
    (Q'.add_assoc_eqv a c (b + d))

private theorem haarQuadSecond_third_append
    (blocks : Nat) (a : RatTerm) :
    ∀ second left right fourth : RatPoly,
      haarQuadSecond blocks a second
          (left ++ right) fourth ≈
        haarQuadSecond blocks a second left fourth +
          haarQuadSecond blocks a second right fourth
  | [], _, _, _ =>
      Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | b :: rest, left, right, fourth => by
      refine Q'.eqv_trans _
        ((haarQuadThird blocks a b left fourth +
            haarQuadThird blocks a b right fourth) +
          (haarQuadSecond blocks a rest left fourth +
            haarQuadSecond blocks a rest right fourth)) _
        (QPoly.q_add_congr
          (haarQuadThird_append
            blocks a b left right fourth)
          (haarQuadSecond_third_append
            blocks a rest left right fourth)) ?_
      exact q_add4_swap _ _ _ _

private theorem haarQuadThird_swap_to_second
    (blocks : Nat) (a b : RatTerm) :
    ∀ third fourth : RatPoly,
      haarQuadThird blocks a b third fourth ≈
        haarQuadSecond blocks a third [b] fourth
  | [], _ => Q'.eqv_refl 0
  | c :: rest, fourth => by
      refine Q'.eqv_trans _
        (haarQuadLast blocks a c b fourth +
          haarQuadSecond blocks a rest [b] fourth) _
        (QPoly.q_add_congr
          (haarQuadLast_swap blocks a b c fourth)
          (haarQuadThird_swap_to_second
            blocks a b rest fourth)) ?_
      exact Q'.eqv_symm
        (QPoly.q_add_congr
          (haarQuadThird_single
            blocks a c b fourth)
          (Q'.eqv_refl _))

private theorem haarQuadSecond_third_nil
    (blocks : Nat) (a : RatTerm) :
    ∀ third fourth : RatPoly,
      haarQuadSecond blocks a third [] fourth ≈ 0
  | [], _ => Q'.eqv_refl 0
  | _ :: rest, fourth => by
      change
        0 +
            haarQuadSecond blocks a rest [] fourth ≈ 0
      refine Q'.eqv_trans _
        (haarQuadSecond blocks a rest [] fourth) _
        (QPoly.q_zero_add_eqv _) ?_
      exact haarQuadSecond_third_nil
        blocks a rest fourth

private theorem haarQuadSecond_swap
    (blocks : Nat) (a : RatTerm) :
    ∀ second third fourth : RatPoly,
      haarQuadSecond blocks a second third fourth ≈
        haarQuadSecond blocks a third second fourth
  | [], third, fourth =>
      Q'.eqv_symm
        (haarQuadSecond_third_nil
          blocks a third fourth)
  | b :: rest, third, fourth => by
      refine Q'.eqv_trans _
        (haarQuadSecond blocks a third [b] fourth +
          haarQuadSecond blocks a third rest fourth) _
        (QPoly.q_add_congr
          (haarQuadThird_swap_to_second
            blocks a b third fourth)
          (haarQuadSecond_swap
            blocks a rest third fourth)) ?_
      exact Q'.eqv_symm
        (haarQuadSecond_third_append
          blocks a third [b] rest fourth)

private theorem haarQuad_swap
    (blocks : Nat) :
    ∀ first second third fourth : RatPoly,
      haarQuad blocks first second third fourth ≈
        haarQuad blocks first third second fourth
  | [], _, _, _ => Q'.eqv_refl 0
  | a :: rest, second, third, fourth =>
      QPoly.q_add_congr
        (haarQuadSecond_swap
          blocks a second third fourth)
        (haarQuad_swap
          blocks rest second third fourth)

/-- Four-factor Fubini permutation under exact product Haar. -/
theorem quaternionHaar_polyMul_four_swap
    (blocks : Nat) (first second third fourth : RatPoly) :
    quaternionHaar blocks
        (polyMul (polyMul first second)
          (polyMul third fourth)) ≈
      quaternionHaar blocks
        (polyMul (polyMul first third)
          (polyMul second fourth)) := by
  exact Q'.eqv_trans _ _ _
    (quaternionHaarFour_eq_quad
      blocks first second third fourth)
    (Q'.eqv_trans _ _ _
      (haarQuad_swap
        blocks first second third fourth)
      (Q'.eqv_symm
        (quaternionHaarFour_eq_quad
          blocks first third second fourth)))

end YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap

#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap.quaternionHaar_polyMul_four_swap
