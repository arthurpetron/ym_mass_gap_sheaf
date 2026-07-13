/-
# Exact Dirichlet identity for the arbitrary-cutoff fused correlation

Write `c_a = coeffW w a`,

    A_N = sum_{a<N} c_a c_{a+1},    D_N = sum_{a<=N} c_a^2.

The all-window retune problem is a quantitative discrete Poincare problem.
This module proves the exact cutoff-uniform summation-by-parts identity

    2 (D_N - A_N)
      = c_0^2 + c_N^2 + sum_{a<N} (c_a-c_{a+1})^2.

Thus no endpoint or moving-cutoff term is lost: the terminal square is part of
the exact energy.  The desired comparison `A_N <= r^3 D_N` follows from the
single explicit Dirichlet lower bound

    2 (1-r^3) D_N
      <= c_0^2 + c_N^2 + sum_{a<N} (c_a-c_{a+1})^2.

The module also records the exact residual recurrence.  These identities are
symbolic in `N`, use no finite-case enumeration, and introduce no analytic
hypothesis or frontier inhabitant.
-/

import YMGap.Continuum.ArbitraryTruncationRetuneCorr
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.AllWindowCorrDirichlet

set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private def q2 : Q' := Q'.ofNat 2

/-- Expanded edge square, arranged as four atomic monomials so cutoff
telescoping is purely associative/commutative. -/
def dirichletTerm (x y : Q') : Q' :=
  (y * y + (-(x * y))) + (x * x + (-(x * y)))

/-- The finite Dirichlet energy of the coefficient string. -/
def dirichletEnergy (w : Q') (N : Nat) : Q' :=
  fsum (fun a => dirichletTerm (coeffW w a) (coeffW w (a + 1))) N

/-- The exact cross-multiplied retune residual. -/
def corrResidual (w : Q') (N : Nat) : Q' :=
  retuneCube w * coordNormSq w N + (-adjCorr w N)

/-- The adjacent correlation gains precisely its new terminal edge. -/
theorem adjCorr_succ (w : Q') (N : Nat) :
    adjCorr w (N + 1) ≈
      adjCorr w N + coeffW w N * coeffW w (N + 1) := by
  exact Q'.eqv_refl _

/-- The squared norm gains precisely the new terminal vertex. -/
theorem coordNormSq_succ (w : Q') (N : Nat) :
    coordNormSq w (N + 1) ≈
      coordNormSq w N + coeffW w (N + 1) * coeffW w (N + 1) := by
  exact Q'.eqv_refl _

/-- Exact cutoff recurrence for the retune residual.  Its increment has no
hidden normalization:

`R_(N+1)-R_N = c_(N+1) (r^3 c_(N+1)-c_N)`.
-/
theorem corrResidual_succ (w : Q') (N : Nat) :
    corrResidual w (N + 1) ≈
      corrResidual w N +
        coeffW w (N + 1) *
          (retuneCube w * coeffW w (N + 1) + (-coeffW w N)) := by
  unfold corrResidual
  change
    retuneCube w *
        (coordNormSq w N + coeffW w (N + 1) * coeffW w (N + 1)) +
          -(adjCorr w N + coeffW w N * coeffW w (N + 1)) ≈
      (retuneCube w * coordNormSq w N + -adjCorr w N) +
        coeffW w (N + 1) *
          (retuneCube w * coeffW w (N + 1) + -coeffW w N)
  ring_qeqv

/-- The expanded edge term is exactly a square. -/
theorem dirichletTerm_eqv_sq (x y : Q') :
    dirichletTerm x y ≈ (x + (-y)) * (x + (-y)) := by
  unfold dirichletTerm
  let expanded := (x * x + x * (-y)) + (((-y) * x) + (-y) * (-y))
  let canonical := (x * x + (-(x * y))) + ((-(x * y)) + y * y)
  have hexpand : (x + (-y)) * (x + (-y)) ≈ expanded := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv x (-y) (x + (-y))) ?_
    exact Q'.add_eqv_congr'
      (Q'.mul_add_eqv x x (-y)) (Q'.mul_add_eqv (-y) x (-y))
  have hxy : (x * (-y)) ≈ (-(x * y)) := Q'.mul_neg_eqv x y
  have hyx : ((-y) * x) ≈ (-(x * y)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y x) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv y x)
  have hyy : ((-y) * (-y)) ≈ y * y := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y (-y)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv y y)) ?_
    exact Q'.neg_neg_eqv (y * y)
  have hcanon : expanded ≈ canonical := by
    unfold expanded canonical
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl (x * x)) hxy)
      (Q'.add_eqv_congr' hyx hyy)
  refine Q'.eqv_trans _ canonical _ ?_ ?_
  · unfold canonical
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv (y * y) (-(x * y)))
  · exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcanon) (Q'.eqv_symm hexpand)

/-- Every finite Dirichlet energy is nonnegative. -/
theorem dirichletEnergy_nonneg (w : Q') (N : Nat) :
    (0 : Q') ≤ dirichletEnergy w N := by
  unfold dirichletEnergy
  exact fsum_nonneg (fun a => Q'.le_trans' _ _ _
    (q_mul_self_nonneg (coeffW w a + (-coeffW w (a + 1))))
    (Q'.le_of_eqv (Q'.eqv_symm
      (dirichletTerm_eqv_sq (coeffW w a) (coeffW w (a + 1)))))) N

/-- **Exact finite-path Dirichlet/SOS identity.**

This is the recurrence/telescoping invariant needed by an all-window proof.
It retains both boundary squares, including the moving-cutoff tail.
-/
theorem twice_norm_sub_corr_eq_boundary_dirichlet (w : Q') : ∀ N : Nat,
    q2 * (coordNormSq w N + (-adjCorr w N)) ≈
      coeffW w 0 * coeffW w 0 +
        coeffW w N * coeffW w N + dirichletEnergy w N
  | 0 => by
      unfold coordNormSq adjCorr dirichletEnergy q2
      change Q'.ofNat 2 *
          ((0 + coeffW w 0 * coeffW w 0) + -0) ≈
        coeffW w 0 * coeffW w 0 + coeffW w 0 * coeffW w 0 + 0
      ring_qeqv
  | N + 1 => by
      have ih := twice_norm_sub_corr_eq_boundary_dirichlet w N
      let D := coordNormSq w N
      let A := adjCorr w N
      let E := dirichletEnergy w N
      let x := coeffW w N
      let y := coeffW w (N + 1)
      let inc := q2 * (y * y + (-(x * y)))
      have hD : coordNormSq w (N + 1) ≈ D + y * y := by
        exact coordNormSq_succ w N
      have hA : adjCorr w (N + 1) ≈ A + x * y := by
        exact adjCorr_succ w N
      have hraw : q2 *
          (coordNormSq w (N + 1) + (-adjCorr w (N + 1))) ≈
          q2 * ((D + y * y) + (-(A + x * y))) := by
        exact Q'.mul_eqv_congr_left q2 _ _
          (Q'.add_eqv_congr' hD (Q'.neg_eqv_congr _ _ hA))
      have hsplit : q2 * ((D + y * y) + (-(A + x * y))) ≈
          q2 * (D + (-A)) + inc := by
        unfold inc q2
        ring_qeqv
      have hih : q2 * (D + (-A)) ≈
          coeffW w 0 * coeffW w 0 + x * x + E := ih
      have hinc : inc ≈
          (y * y + (-(x * y))) + (y * y + (-(x * y))) := by
        unfold inc
        exact CubeRatioBounds.ofNat_two_mul_eqv _
      have hfinal :
          (coeffW w 0 * coeffW w 0 + x * x + E) +
              ((y * y + (-(x * y))) + (y * y + (-(x * y)))) ≈
            coeffW w 0 * coeffW w 0 + y * y +
              (E + dirichletTerm x y) := by
        let C := coeffW w 0 * coeffW w 0
        let X := x * x
        let Y := y * y
        let n := -(x * y)
        change ((C + X) + E) + ((Y + n) + (Y + n)) ≈
          (C + Y) + (E + ((Y + n) + (X + n)))
        refine Q'.eqv_trans _ _ _
          (Q'.add_swap_inner (C + X) E (Y + n) (Y + n)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ (E + (Y + n))
            (Q'.add_swap_inner C X Y n)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv (C + Y) (X + n) (E + (Y + n))) ?_
        refine Q'.add_eqv_congr_left (C + Y) _ _ ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_comm_eqv (X + n) (E + (Y + n))) ?_
        exact Q'.add_assoc_eqv E (Y + n) (X + n)
      refine Q'.eqv_trans _ _ _ hraw ?_
      refine Q'.eqv_trans _ _ _ hsplit ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hih hinc) ?_
      exact hfinal

/-- Universal finite-path Rayleigh bound `A_N ≤ D_N`.  Unlike the sharper
retune comparison, this needs no restriction on `w`; it is the immediate
nonnegative-energy consequence of the exact SOS identity. -/
theorem adjCorr_le_coordNormSq (w : Q') (N : Nat) :
    adjCorr w N ≤ coordNormSq w N := by
  have h0 : (0 : Q') ≤ coeffW w 0 * coeffW w 0 :=
    q_mul_self_nonneg (coeffW w 0)
  have hN : (0 : Q') ≤ coeffW w N * coeffW w N :=
    q_mul_self_nonneg (coeffW w N)
  have hE : (0 : Q') ≤ dirichletEnergy w N := dirichletEnergy_nonneg w N
  have hR : (0 : Q') ≤
      coeffW w 0 * coeffW w 0 +
        coeffW w N * coeffW w N + dirichletEnergy w N :=
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ h0 hN) hE
  have hid := twice_norm_sub_corr_eq_boundary_dirichlet w N
  have htwice : (0 : Q') ≤
      q2 * (coordNormSq w N + (-adjCorr w N)) :=
    Q'.le_trans' _ _ _ hR (Q'.le_of_eqv (Q'.eqv_symm hid))
  have hscaled : q2 * (0 : Q') ≤
      q2 * (coordNormSq w N + (-adjCorr w N)) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv q2))) htwice
  have hdiff : (0 : Q') ≤ coordNormSq w N + (-adjCorr w N) :=
    Q'.le_of_mul_le_mul_left hscaled (by decide : (0 : Q') < q2)
  exact Q'.le_of_sub_nonneg hdiff

end YMGap.Continuum.AllWindowCorrDirichlet

#print axioms YMGap.Continuum.AllWindowCorrDirichlet.corrResidual_succ
#print axioms YMGap.Continuum.AllWindowCorrDirichlet.dirichletEnergy_nonneg
#print axioms YMGap.Continuum.AllWindowCorrDirichlet.twice_norm_sub_corr_eq_boundary_dirichlet
#print axioms YMGap.Continuum.AllWindowCorrDirichlet.adjCorr_le_coordNormSq
