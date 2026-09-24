/-
# Squared seminorm of the literal-width all-nome Wilson form

The distance is the actual all-nome reflected form evaluated on the literal
intrinsic difference.  Bilinearity, positivity, and the radical theorem give
the squared triangle law and null descent directly on `IntrinsicExpression`;
no small-nome spatial limit or replacement carrier is used.

This constructs a seminorm only.  Completion, continuity, time contraction,
and changing-spacing control are separate obligations.
-/

import YMGap.Continuum.BF4WilsonAllNomeFormLaws
import YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz
import YMGap.Continuum.CRealSeminormCompletion

namespace YMGap.Continuum.BF4WilsonAllNomeSeminorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (sum difference)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (intrinsicForm intrinsicForm_symm intrinsicForm_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
open YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

local notation "F" => intrinsicForm hw0 hw1

/-- Squared distance of two actual intrinsic Wilson expressions. -/
def distSq {width : Nat} (x y : IntrinsicExpression width) : CReal :=
  F (difference x y) (difference x y)

local notation "D" => distSq hw0 hw1

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) :=
  Equiv_add ha (neg_congr hc)

theorem distSq_refl {width : Nat} (x : IntrinsicExpression width) :
    Equiv (D x x) czero :=
  (intrinsicForm_difference_left hw0 hw1 x x (difference x x)).trans
    (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.add_neg_self_eqv ((F x (difference x x)).approx n)))

theorem distSq_symm {width : Nat} (x y : IntrinsicExpression width) :
    Equiv (D x y) (D y x) := by
  refine (intrinsicForm_difference_diagonal hw0 hw1 x y).trans
    (Equiv.trans ?_ (intrinsicForm_difference_diagonal hw0 hw1 y x).symm)
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
    (.add (.add (.var 3) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 0)))))
    (by decide) (fun
      | 0 => (F x x).approx n
      | 1 => (F x y).approx n
      | 2 => (F y x).approx n
      | _ => (F y y).approx n)

theorem distSq_nonnegative {width : Nat} (x y : IntrinsicExpression width) :
    leEv czero (D x y) :=
  intrinsicForm_nonnegative hw0 hw1 (difference x y)

/-- The parallelogram estimate is derived from positivity of the literal
difference, rather than postulated as a metric axiom. -/
theorem pairing_sum_bound {width : Nat} (x y : IntrinsicExpression width) :
    leEv (F (sum x y) (sum x y))
      (add (add (F x x) (F x x)) (add (F y y) (F y y))) := by
  have hsum := (intrinsicForm_sum_left hw0 hw1 x y (sum x y)).trans
    (Equiv_add (intrinsicForm_sum_right hw0 hw1 x x y)
      (intrinsicForm_sum_right hw0 hw1 y x y))
  have hpar : Equiv
      (add (F (sum x y) (sum x y)) (F (difference x y) (difference x y)))
      (add (add (F x x) (F x x)) (add (F y y) (F y y))) := by
    refine (Equiv_add hsum (intrinsicForm_difference_diagonal hw0 hw1 x y)).trans ?_
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3))))))
      (.add (.add (.var 0) (.var 0)) (.add (.var 3) (.var 3))) (by decide)
      (fun
        | 0 => (F x x).approx n
        | 1 => (F x y).approx n
        | 2 => (F y x).approx n
        | _ => (F y y).approx n)
  have hzero : Equiv (add (F (sum x y) (sum x y)) czero) (F (sum x y) (sum x y)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => QPoly.q_add_zero_eqv _)
  exact leEv_trans (leEv_of_equiv hzero.symm)
    (leEv_trans (leEv_add (leEv_refl _) (distSq_nonnegative hw0 hw1 x y))
      (leEv_of_equiv hpar))

private theorem difference_chain {width : Nat} (x y z u : IntrinsicExpression width) :
    Equiv (F (sum (difference x y) (difference y z)) u) (F (difference x z) u) := by
  refine (intrinsicForm_sum_left hw0 hw1 (difference x y) (difference y z) u).trans
    ((Equiv_add (intrinsicForm_difference_left hw0 hw1 x y u)
      (intrinsicForm_difference_left hw0 hw1 y z u)).trans
        (Equiv.trans ?_ (intrinsicForm_difference_left hw0 hw1 x z u).symm))
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
    (.add (.var 0) (.neg (.var 2))) (by decide)
    (fun | 0 => (F x u).approx n | 1 => (F y u).approx n | _ => (F z u).approx n)

theorem distSq_triangle {width : Nat} (x y z : IntrinsicExpression width) :
    leEv (D x z)
      (add (add (D x y) (D x y)) (add (D y z) (D y z))) := by
  let s := sum (difference x y) (difference y z)
  let d := difference x z
  have hpin : Equiv (F s s) (F d d) :=
    (difference_chain hw0 hw1 x y z s).trans
      ((intrinsicForm_symm hw0 hw1 d s).trans (difference_chain hw0 hw1 x y z d))
  exact leEv_trans (leEv_of_equiv hpin.symm)
    (pairing_sum_bound hw0 hw1 (difference x y) (difference y z))

theorem pairing_null_left {width : Nat} {x x' : IntrinsicExpression width}
    (hx : Equiv (D x x') czero) (y : IntrinsicExpression width) :
    Equiv (F x y) (F x' y) := by
  have hz := intrinsicForm_radical_zero hw0 hw1 (difference x x') y hx
  exact Equiv_of_sub_eqv_zero
    ((intrinsicForm_difference_left hw0 hw1 x x' y).symm.trans hz)

theorem pairing_null_congr {width : Nat} {x x' y y' : IntrinsicExpression width}
    (hx : Equiv (D x x') czero) (hy : Equiv (D y y') czero) :
    Equiv (F x y) (F x' y') :=
  (pairing_null_left hw0 hw1 hx y).trans
    ((intrinsicForm_symm hw0 hw1 x' y).trans
      ((pairing_null_left hw0 hw1 hy x').trans (intrinsicForm_symm hw0 hw1 y' x')))

theorem distSq_null_congr {width : Nat} {x x' y y' : IntrinsicExpression width}
    (hx : Equiv (D x x') czero) (hy : Equiv (D y y') czero) :
    Equiv (D x y) (D x' y') :=
  (intrinsicForm_difference_diagonal hw0 hw1 x y).trans
    ((sub_congr
      (sub_congr (pairing_null_congr hw0 hw1 hx hx)
        (pairing_null_congr hw0 hw1 hx hy))
      (sub_congr (pairing_null_congr hw0 hw1 hy hx)
        (pairing_null_congr hw0 hw1 hy hy))).trans
      (intrinsicForm_difference_diagonal hw0 hw1 x' y').symm)

/-- The actual all-nome Wilson squared seminorm at a fixed literal width. -/
def seminorm {width : Nat} : SquaredSeminorm where
  Carrier := IntrinsicExpression width
  distSq := D
  distSq_refl := distSq_refl hw0 hw1
  distSq_symm := distSq_symm hw0 hw1
  distSq_nonneg := distSq_nonnegative hw0 hw1
  distSq_triangle := distSq_triangle hw0 hw1
  null_congr := distSq_null_congr hw0 hw1

#print axioms distSq_refl
#print axioms distSq_symm
#print axioms distSq_nonnegative
#print axioms pairing_sum_bound
#print axioms distSq_triangle
#print axioms pairing_null_congr
#print axioms distSq_null_congr
#print axioms seminorm

end YMGap.Continuum.BF4WilsonAllNomeSeminorm
