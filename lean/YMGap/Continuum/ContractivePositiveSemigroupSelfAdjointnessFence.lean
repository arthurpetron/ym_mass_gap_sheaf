/-
# A finite exact fence: contraction and positivity do not imply symmetry

This two-dimensional exact-rational model is an additive time semigroup whose
one-step map contracts the Euclidean quadratic form, contracts all squared
distances, and has a nonnegative diagonal transfer form.  Nevertheless the
one-step map is not self-adjoint.  It is a permanent machine-checked fence
against inferring the missing strict-cylinder bilinear symmetry from the
already proved semigroup, contraction, distance-contraction, and diagonal
positivity statements.

The map is a half-scaled quarter turn,

`(x,y) |-> ((x-y)/2, (x+y)/2)`.

All calculations are exact in `Q'`; no measured constant is used.
-/

import YMGap.Constructive.HalfPow
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.RegularCReal
import YMGap.Constructive.SumOfSquares
import YMGap.Continuum.OSReconstructionProgress

namespace YMGap.Continuum.ContractivePositiveSemigroupSelfAdjointnessFence

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/- A small exact rational ring normalizer for the closed algebraic identities
in this file. -/
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero];
             ac_rfl))

abbrev FenceVector := Q' × Q'

def fenceInner (left right : FenceVector) : Q' :=
  left.1 * right.1 + left.2 * right.2

def fenceNormSq (vector : FenceVector) : Q' :=
  fenceInner vector vector

def fenceDifference (left right : FenceVector) : FenceVector :=
  (left.1 + (-right.1), left.2 + (-right.2))

def fenceDistSq (left right : FenceVector) : Q' :=
  fenceNormSq (fenceDifference left right)

def fenceStep (vector : FenceVector) : FenceVector :=
  (HalfPow.half * vector.1 + (-(HalfPow.half * vector.2)),
    HalfPow.half * vector.1 + HalfPow.half * vector.2)

def fenceTime : Nat → FenceVector → FenceVector
  | 0, vector => vector
  | step + 1, vector => fenceStep (fenceTime step vector)

def FenceVectorEquivalent (left right : FenceVector) : Prop :=
  left.1 ≈ right.1 ∧ left.2 ≈ right.2

theorem fenceNormSq_nonnegative (vector : FenceVector) :
    (0 : Q') ≤ fenceNormSq vector := by
  unfold fenceNormSq fenceInner
  exact Q'.zero_le_add _ _
    (SumOfSquares.q_mul_self_nonneg vector.1)
    (SumOfSquares.q_mul_self_nonneg vector.2)

private theorem square_add_expand (u v : Q') :
    ((u + v) * (u + v)) ≈
      ((u * u + v * v) + (u * v + u * v)) := by
  refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul u v (u + v)) ?_
  have hright : v * (u + v) ≈ u * v + v * v := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv v u v) ?_
    exact QPoly.q_add_congr (Q'.mul_comm_eqv v u) (Q'.eqv_refl (v * v))
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (Q'.mul_add_eqv u u v) hright) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + u * v) (u * v + v * v)
      (v * v + u * v) (Q'.add_comm_eqv (u * v) (v * v))) ?_
  exact Q'.add_swap_inner (u * u) (u * v) (v * v) (u * v)

private theorem square_neg_eqv (v : Q') :
    ((-v) * (-v)) ≈ v * v := by
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv v (-v)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr (v * (-v)) (-(v * v)) (Q'.mul_neg_eqv v v)) ?_
  exact Q'.neg_neg_eqv (v * v)

private theorem square_sub_expand (u v : Q') :
    ((u + -v) * (u + -v)) ≈
      ((u * u + v * v) + -(u * v + u * v)) := by
  refine Q'.eqv_trans _ _ _ (square_add_expand u (-v)) ?_
  refine QPoly.q_add_congr ?_ ?_
  · exact QPoly.q_add_congr (Q'.eqv_refl (u * u)) (square_neg_eqv v)
  · refine Q'.eqv_trans _ _ _
      (QPoly.q_add_congr (Q'.mul_neg_eqv u v) (Q'.mul_neg_eqv u v)) ?_
    exact Q'.eqv_symm (Q'.neg_add_eqv (u * v) (u * v))

private theorem parallelogram_eqv (u v : Q') :
    ((u + -v) * (u + -v) + (u + v) * (u + v)) ≈
      ((u * u + v * v) + (u * u + v * v)) := by
  let S : Q' := u * u + v * v
  let C : Q' := u * v + u * v
  refine Q'.eqv_trans _ ((S + -C) + (S + C)) _
    (QPoly.q_add_congr (square_sub_expand u v) (square_add_expand u v)) ?_
  refine Q'.eqv_trans _ ((S + S) + (-C + C)) _
    (Q'.add_swap_inner S (-C) S C) ?_
  refine Q'.eqv_trans _ ((S + S) + 0) _
    (Q'.add_eqv_congr_left (S + S) (-C + C) 0
      (Q'.neg_add_self_eqv C)) ?_
  exact QPoly.q_add_zero_eqv (S + S)

private theorem square_scaled_eqv (scale value : Q') :
    ((scale * value) * (scale * value)) ≈
      (scale * scale) * (value * value) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv scale value (scale * value)) ?_
  refine Q'.eqv_trans _ (scale * (scale * (value * value))) _ ?_ ?_
  · refine Q'.mul_eqv_congr_left scale _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv value scale value)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (value * scale) (scale * value) value
        (Q'.mul_comm_eqv value scale)) ?_
    exact Q'.mul_assoc_eqv scale value value
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv scale scale (value * value))

/-- Algebraic expansion of the one-step norm before evaluating the half
coefficient. -/
theorem fenceStep_normSq_factor_eqv (vector : FenceVector) :
    fenceNormSq (fenceStep vector) ≈
      (HalfPow.half * HalfPow.half + HalfPow.half * HalfPow.half) *
        fenceNormSq vector := by
  unfold fenceNormSq fenceInner fenceStep
  let u : Q' := HalfPow.half * vector.1
  let v : Q' := HalfPow.half * vector.2
  let hsq : Q' := HalfPow.half * HalfPow.half
  let sourceSq : Q' := vector.1 * vector.1 + vector.2 * vector.2
  refine Q'.eqv_trans _ ((u * u + v * v) + (u * u + v * v)) _
    (parallelogram_eqv u v) ?_
  have hsource : (u * u + v * v) ≈ hsq * sourceSq := by
    refine Q'.eqv_trans _
      (hsq * (vector.1 * vector.1) + hsq * (vector.2 * vector.2)) _
      (QPoly.q_add_congr
        (square_scaled_eqv HalfPow.half vector.1)
        (square_scaled_eqv HalfPow.half vector.2)) ?_
    exact Q'.eqv_symm
      (Q'.mul_add_eqv hsq (vector.1 * vector.1) (vector.2 * vector.2))
  refine Q'.eqv_trans _ ((hsq * sourceSq) + (hsq * sourceSq)) _
    (QPoly.q_add_congr hsource hsource) ?_
  exact Q'.eqv_symm (QPoly.q_add_mul hsq hsq sourceSq)

/-- The one-step norm is exactly one half of the source norm. -/
theorem fenceStep_normSq_eqv (vector : FenceVector) :
    fenceNormSq (fenceStep vector) ≈
      HalfPow.half * fenceNormSq vector := by
  exact Q'.eqv_trans _ _ _
    (fenceStep_normSq_factor_eqv vector)
    (Q'.mul_eqv_congr_right _ _ _
      (ExpNeg.two_halves HalfPow.half))

/-- Hence the one-step map is a contraction. -/
theorem fenceStep_normSq_le (vector : FenceVector) :
    fenceNormSq (fenceStep vector) ≤ fenceNormSq vector := by
  have hscaled : HalfPow.half * fenceNormSq vector ≤
      (1 : Q') * fenceNormSq vector :=
    Q'.mul_le_mul_of_nonneg_right HalfPow.half 1
      (fenceNormSq vector) (by decide)
      (fenceNormSq_nonnegative vector)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (fenceStep_normSq_eqv vector))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.one_mul_eqv (fenceNormSq vector))))

/-- The diagonal transfer form is exactly half the norm square. -/
theorem fenceStep_diagonal_eqv (vector : FenceVector) :
    fenceInner (fenceStep vector) vector ≈
      HalfPow.half * fenceNormSq vector := by
  unfold fenceNormSq fenceInner fenceStep
  let hx : Q' := HalfPow.half * vector.1
  let hy : Q' := HalfPow.half * vector.2
  refine Q'.eqv_trans _
    ((hx * vector.1 + -(hy * vector.1)) +
      (hx * vector.2 + hy * vector.2)) _ ?_ ?_
  · exact QPoly.q_add_congr
      (Q'.eqv_trans _ _ _ (QPoly.q_add_mul hx (-hy) vector.1)
        (QPoly.q_add_congr (Q'.eqv_refl (hx * vector.1))
          (Q'.neg_mul_eqv hy vector.1)))
      (QPoly.q_add_mul hx hy vector.2)
  · have hcross : hy * vector.1 ≈ hx * vector.2 := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv HalfPow.half vector.2 vector.1) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left HalfPow.half _ _
          (Q'.mul_comm_eqv vector.2 vector.1)) ?_
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv HalfPow.half vector.1 vector.2)
    have hcancel : (-(hy * vector.1) + hx * vector.2) ≈ 0 := by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (-(hy * vector.1)) (-(hx * vector.2))
          (hx * vector.2)
          (Q'.neg_eqv_congr _ _ hcross))
        (Q'.neg_add_self_eqv (hx * vector.2))
    refine Q'.eqv_trans _
      ((hx * vector.1 + -(hy * vector.1)) +
        (hy * vector.2 + hx * vector.2)) _
      (Q'.add_eqv_congr_left (hx * vector.1 + -(hy * vector.1))
        (hx * vector.2 + hy * vector.2)
        (hy * vector.2 + hx * vector.2)
        (Q'.add_comm_eqv (hx * vector.2) (hy * vector.2))) ?_
    refine Q'.eqv_trans _
      ((hx * vector.1 + hy * vector.2) +
        (-(hy * vector.1) + hx * vector.2)) _
      (Q'.add_swap_inner (hx * vector.1) (-(hy * vector.1))
        (hy * vector.2) (hx * vector.2)) ?_
    refine Q'.eqv_trans _ ((hx * vector.1 + hy * vector.2) + 0) _
      (Q'.add_eqv_congr_left (hx * vector.1 + hy * vector.2)
        (-(hy * vector.1) + hx * vector.2) 0 hcancel) ?_
    refine Q'.eqv_trans _ (hx * vector.1 + hy * vector.2) _
      (QPoly.q_add_zero_eqv _) ?_
    refine Q'.eqv_trans _
      (HalfPow.half * (vector.1 * vector.1) +
        HalfPow.half * (vector.2 * vector.2)) _
      (QPoly.q_add_congr
        (Q'.mul_assoc_eqv HalfPow.half vector.1 vector.1)
        (Q'.mul_assoc_eqv HalfPow.half vector.2 vector.2)) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv HalfPow.half
      (vector.1 * vector.1) (vector.2 * vector.2))

/-- In particular, the transfer form is nonnegative on every diagonal. -/
theorem fenceStep_diagonal_nonnegative (vector : FenceVector) :
    (0 : Q') ≤ fenceInner (fenceStep vector) vector := by
  have hscaled : (0 : Q') ≤
      HalfPow.half * fenceNormSq vector :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (fenceNormSq_nonnegative vector)
  exact le_of_le_eqv hscaled
    (Q'.eqv_symm (fenceStep_diagonal_eqv vector))

/-- The recursively defined time maps obey the exact additive semigroup law. -/
theorem fenceTime_add (first second : Nat) (vector : FenceVector) :
    fenceTime (first + second) vector =
      fenceTime second (fenceTime first vector) := by
  induction second with
  | zero => rfl
  | succ second inductionHypothesis =>
      rw [Nat.add_succ]
      change fenceStep (fenceTime (first + second) vector) =
        fenceStep (fenceTime second (fenceTime first vector))
      exact congrArg fenceStep inductionHypothesis

/-- Every iterate remains norm-contractive. -/
theorem fenceTime_normSq_le (shift : Nat) (vector : FenceVector) :
    fenceNormSq (fenceTime shift vector) ≤ fenceNormSq vector := by
  induction shift with
  | zero => exact Q'.le_refl' _
  | succ shift inductionHypothesis =>
      exact Q'.le_trans' _ _ _
        (fenceStep_normSq_le (fenceTime shift vector))
        inductionHypothesis

theorem fenceNormSq_equiv_of_vectorEquivalent
    {left right : FenceVector}
    (h : FenceVectorEquivalent left right) :
    fenceNormSq left ≈ fenceNormSq right := by
  have hfirst : left.1 * left.1 ≈ right.1 * right.1 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right left.1 right.1 left.1 h.1)
      (Q'.mul_eqv_congr_left right.1 left.1 right.1 h.1)
  have hsecond : left.2 * left.2 ≈ right.2 * right.2 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right left.2 right.2 left.2 h.2)
      (Q'.mul_eqv_congr_left right.2 left.2 right.2 h.2)
  exact QPoly.q_add_congr hfirst hsecond

/-- Difference commutes with the step map up to exact-rational equivalence. -/
theorem fenceDifference_step_equiv (left right : FenceVector) :
    FenceVectorEquivalent
      (fenceDifference (fenceStep left) (fenceStep right))
      (fenceStep (fenceDifference left right)) := by
  constructor <;>
    unfold fenceDifference fenceStep <;>
    dsimp only <;>
    ring_qeqv

/-- The one-step map contracts squared distances, not merely source norms. -/
theorem fenceStep_distSq_le (left right : FenceVector) :
    fenceDistSq (fenceStep left) (fenceStep right) ≤
      fenceDistSq left right := by
  have hrewrite := fenceNormSq_equiv_of_vectorEquivalent
    (fenceDifference_step_equiv left right)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite)
    (fenceStep_normSq_le (fenceDifference left right))

/-- Every semigroup iterate contracts squared distances. -/
theorem fenceTime_distSq_le
    (shift : Nat) (left right : FenceVector) :
    fenceDistSq (fenceTime shift left) (fenceTime shift right) ≤
      fenceDistSq left right := by
  induction shift with
  | zero => exact Q'.le_refl' _
  | succ shift inductionHypothesis =>
      exact Q'.le_trans' _ _ _
        (fenceStep_distSq_le
          (fenceTime shift left) (fenceTime shift right))
        inductionHypothesis

def fenceFirstBasis : FenceVector := (1, 0)

def fenceSecondBasis : FenceVector := (0, 1)

/-- The two off-diagonal matrix coefficients have opposite signs. -/
theorem fenceStep_cross_not_eqv :
    ¬ fenceInner (fenceStep fenceFirstBasis) fenceSecondBasis ≈
      fenceInner fenceFirstBasis (fenceStep fenceSecondBasis) := by
  unfold fenceInner fenceStep fenceFirstBasis fenceSecondBasis HalfPow.half
  decide

/-- Final fence: exact semigroup, positivity, norm contraction and pairwise
distance contraction still do not imply self-adjointness. -/
theorem fenceStep_not_selfAdjoint :
    ¬ ∀ left right : FenceVector,
      fenceInner (fenceStep left) right ≈
        fenceInner left (fenceStep right) := by
  intro hselfAdjoint
  exact fenceStep_cross_not_eqv
    (hselfAdjoint fenceFirstBasis fenceSecondBasis)

#print axioms fenceStep_normSq_le
#print axioms fenceStep_diagonal_nonnegative
#print axioms fenceTime_add
#print axioms fenceTime_normSq_le
#print axioms fenceStep_distSq_le
#print axioms fenceTime_distSq_le
#print axioms fenceStep_not_selfAdjoint

end YMGap.Continuum.ContractivePositiveSemigroupSelfAdjointnessFence
