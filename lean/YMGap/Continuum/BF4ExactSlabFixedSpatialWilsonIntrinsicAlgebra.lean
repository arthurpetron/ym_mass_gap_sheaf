/-
# Dense rational algebra on the actual intrinsic Wilson carrier

Scalar multiplication retains the recorded radius and every original loop;
zero is the zero multiple of the literal unit expression. Common centered
charts transport the already proved finite-horizon limiting form laws to
these intrinsic expressions. The distance-to-zero identity therefore ties
the SAME squared seminorm to its actual pairing diagonal.

This supplies dense algebra for explicit rational-approximation streams and
completed norm separation. It does not postulate completed linearity, full
Hilbert completeness, a strict bound on this enlarged carrier, or a physical
spacing/continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

def smul {base : Nat} (c : Q') (x : IntrinsicExpression base) : IntrinsicExpression base :=
  ⟨x.radius, .smul c x.expression, x.within⟩

def zero (base : Nat) : IntrinsicExpression base := smul 0 (unit base)

theorem chart_smul {base : Nat} (H : Nat) (c : Q') (x : IntrinsicExpression base) :
    chart H (smul c x) = .smul c (chart H x) := rfl

theorem chart_zero (base H : Nat) : chart H (zero base) = .smul 0 .one := rfl

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

local notation "F" => intrinsicForm hw0 hw1 hsmall hd hs hb

attribute [local irreducible] intrinsicForm form

theorem intrinsicForm_sum_left (x y z : IntrinsicExpression base) :
    Equiv (F (sum x y) z) (add (F x z) (F y z)) := by
  let H := max (max x.radius y.radius) z.radius
  have hx : x.radius ≤ H := by dsimp [H]; omega
  have hy : y.radius ≤ H := by dsimp [H]; omega
  have hz : z.radius ≤ H := by dsimp [H]; omega
  have hsum : (sum x y).radius ≤ H := Nat.max_le.mpr ⟨hx, hy⟩
  have hp := intrinsicForm_chart hw0 hw1 hsmall hd hs hb (sum x y) z H hsum hz
  have hlin := form_add_left hw0 hw1 hsmall hd hs hb H (chart H x) (chart H y) (chart H z)
    (chart_within H x hx) (chart_within H y hy) (chart_within H z hz)
  refine Equiv.trans ?_ (hlin.trans (Equiv_add
    (intrinsicForm_chart hw0 hw1 hsmall hd hs hb x z H hx hz).symm
    (intrinsicForm_chart hw0 hw1 hsmall hd hs hb y z H hy hz).symm))
  simpa only [chart_sum H x y hx hy] using hp

theorem intrinsicForm_sum_right (x y z : IntrinsicExpression base) :
    Equiv (F x (sum y z)) (add (F x y) (F x z)) :=
  (intrinsicForm_symm hw0 hw1 hsmall hd hs hb x (sum y z)).trans
    ((intrinsicForm_sum_left hw0 hw1 hsmall hd hs hb y z x).trans
      (Equiv_add (intrinsicForm_symm hw0 hw1 hsmall hd hs hb y x)
        (intrinsicForm_symm hw0 hw1 hsmall hd hs hb z x)))

theorem intrinsicForm_smul_left (c : Q') (x y : IntrinsicExpression base) :
    Equiv (F (smul c x) y) (mul (ofQ' c) (F x y)) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  have hp := intrinsicForm_chart hw0 hw1 hsmall hd hs hb (smul c x) y H hx hy
  have hlin := form_smul_left hw0 hw1 hsmall hd hs hb H c (chart H x) (chart H y)
    (chart_within H x hx) (chart_within H y hy)
  refine Equiv.trans ?_ (hlin.trans
    (Pivot2.mul_congr_right (intrinsicForm_chart hw0 hw1 hsmall hd hs hb x y H hx hy).symm))
  simpa only [chart_smul] using hp

theorem intrinsicForm_smul_right (c : Q') (x y : IntrinsicExpression base) :
    Equiv (F x (smul c y)) (mul (ofQ' c) (F x y)) :=
  (intrinsicForm_symm hw0 hw1 hsmall hd hs hb x (smul c y)).trans
    ((intrinsicForm_smul_left hw0 hw1 hsmall hd hs hb c y x).trans
      (Pivot2.mul_congr_right (intrinsicForm_symm hw0 hw1 hsmall hd hs hb y x)))

theorem intrinsicForm_difference_left (x y z : IntrinsicExpression base) :
    Equiv (F (difference x y) z) (sub (F x z) (F y z)) := by
  let H := max (max x.radius y.radius) z.radius
  have hx : x.radius ≤ H := by dsimp [H]; omega
  have hy : y.radius ≤ H := by dsimp [H]; omega
  have hz : z.radius ≤ H := by dsimp [H]; omega
  have hdiff : (difference x y).radius ≤ H := Nat.max_le.mpr ⟨hx, hy⟩
  have hp := intrinsicForm_chart hw0 hw1 hsmall hd hs hb (difference x y) z H hdiff hz
  have hlin := form_difference_left hw0 hw1 hsmall hd hs hb H
    (chart H x) (chart H y) (chart H z)
    (chart_within H x hx) (chart_within H y hy) (chart_within H z hz)
  refine Equiv.trans ?_ (hlin.trans (Equiv_add
    (intrinsicForm_chart hw0 hw1 hsmall hd hs hb x z H hx hz).symm
    (neg_congr (intrinsicForm_chart hw0 hw1 hsmall hd hs hb y z H hy hz).symm)))
  simpa only [chart_difference H x y hx hy] using hp

theorem intrinsicForm_difference_right (x y z : IntrinsicExpression base) :
    Equiv (F x (difference y z)) (sub (F x y) (F x z)) :=
  (intrinsicForm_symm hw0 hw1 hsmall hd hs hb x (difference y z)).trans
    ((intrinsicForm_difference_left hw0 hw1 hsmall hd hs hb y z x).trans
      (Equiv_add (intrinsicForm_symm hw0 hw1 hsmall hd hs hb y x)
        (neg_congr (intrinsicForm_symm hw0 hw1 hsmall hd hs hb z x))))

theorem intrinsicForm_difference_diagonal (x y : IntrinsicExpression base) :
    Equiv (F (difference x y) (difference x y))
      (sub (sub (F x x) (F x y)) (sub (F y x) (F y y))) :=
  (intrinsicForm_difference_left hw0 hw1 hsmall hd hs hb x y (difference x y)).trans
    (Equiv_add (intrinsicForm_difference_right hw0 hw1 hsmall hd hs hb x x y)
      (neg_congr (intrinsicForm_difference_right hw0 hw1 hsmall hd hs hb y x y)))

/-- The actual seminorm distance has the four-term original form expansion. -/
theorem distSq_diagonal (x y : IntrinsicExpression base) :
    Equiv (distSq hw0 hw1 hsmall hd hs hb x y)
      (sub (sub (F x x) (F x y)) (sub (F y x) (F y y))) :=
  intrinsicForm_difference_diagonal hw0 hw1 hsmall hd hs hb x y

theorem intrinsicForm_zero_left (x : IntrinsicExpression base) :
    Equiv (F (zero base) x) czero :=
  (intrinsicForm_smul_left hw0 hw1 hsmall hd hs hb 0 (unit base) x).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv ((F (unit base) x).approx n)))

theorem intrinsicForm_zero_right (x : IntrinsicExpression base) :
    Equiv (F x (zero base)) czero :=
  (intrinsicForm_symm hw0 hw1 hsmall hd hs hb x (zero base)).trans
    (intrinsicForm_zero_left hw0 hw1 hsmall hd hs hb x)

/-- This identity connects the existing squared distance to its SAME form
diagonal; it is the input consumed by generic completed positive definiteness. -/
theorem distSq_zero (x : IntrinsicExpression base) :
    Equiv (distSq hw0 hw1 hsmall hd hs hb x (zero base)) (F x x) := by
  have h := distSq_diagonal hw0 hw1 hsmall hd hs hb x (zero base)
  have hclean : Equiv
      (sub (sub (F x x) (F x (zero base))) (sub (F (zero base) x) (F (zero base) (zero base))))
      (sub (sub (F x x) czero) (sub czero czero)) :=
    Equiv_add
      (Equiv_add (Equiv.refl _) (neg_congr (intrinsicForm_zero_right hw0 hw1 hsmall hd hs hb x)))
      (neg_congr (Equiv_add (intrinsicForm_zero_left hw0 hw1 hsmall hd hs hb x)
        (neg_congr (intrinsicForm_zero_left hw0 hw1 hsmall hd hs hb (zero base)))))
  refine h.trans (hclean.trans ?_)
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.const 0)))
      (.neg (.add (.const 0) (.neg (.const 0)))))
    (.var 0) (by decide) (fun _ => (F x x).approx n)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.chart_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.chart_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.intrinsicForm_sum_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.intrinsicForm_sum_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.intrinsicForm_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.intrinsicForm_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.intrinsicForm_difference_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.intrinsicForm_difference_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.intrinsicForm_difference_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.distSq_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.intrinsicForm_zero_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.intrinsicForm_zero_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.distSq_zero
