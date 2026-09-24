/- # Algebra of the literal all-nome Wilson reflected form

Only existing Wilson syntax and the original fixed-width joint functional are
used.  This supplies no new carrier, completion, or analytic input. -/

import YMGap.Continuum.BF4WilsonAllNomeReflectedForm
import YMGap.Continuum.BF4WilsonJointFunctionalLaws
import YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra

namespace YMGap.Continuum.BF4WilsonAllNomeFormLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (sum difference chart_sum chart_difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
  (smul zero chart_smul)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (joint_congr joint_add)
open YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz (joint_smul)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

local notation "F" => commonForm hw0 hw1
local notation "I" => BF4WilsonAllNomeReflectedForm.intrinsicForm hw0 hw1

theorem commonForm_add_left {width H : Nat} (e f g : WindowExpression width)
    (he : Within H e) (hf : Within H f) (hg : Within H g) :
    Equiv (F H (.add e f) g ⟨he, hf⟩ hg)
      (add (F H e g he hg) (F H f g hf hg)) := by
  have heg : Within (2*H) (.mul (mirror H e) g) :=
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) g hg⟩
  have hfg : Within (2*H) (.mul (mirror H f) g) :=
    ⟨mirror_within H f, within_mono (by omega : H ≤ 2*H) g hg⟩
  refine (joint_congr hw0 hw1 (2*H)
    (.mul (mirror H (.add e f)) g)
    (.add (.mul (mirror H e) g) (.mul (mirror H f) g)) _ ⟨heg, hfg⟩ ?_).trans
      (joint_add hw0 hw1 (2*H) _ _ heg hfg)
  change RatPolyCoeffEqv
    (polyMul (polyAdd (sourcePolynomial (mirror H e))
      (sourcePolynomial (mirror H f))) (sourcePolynomial g)) _
  rw [polyMul_add_left_exact]
  exact RatPolyCoeffEqv.refl _

theorem commonForm_add_right {width H : Nat} (e f g : WindowExpression width)
    (he : Within H e) (hf : Within H f) (hg : Within H g) :
    Equiv (F H e (.add f g) he ⟨hf, hg⟩)
      (add (F H e f he hf) (F H e g he hg)) :=
  (commonForm_symm hw0 hw1 H e (.add f g) he ⟨hf, hg⟩).trans
    ((commonForm_add_left hw0 hw1 f g e hf hg he).trans
      (Equiv_add (commonForm_symm hw0 hw1 H f e hf he)
        (commonForm_symm hw0 hw1 H g e hg he)))

theorem commonForm_smul_left {width H : Nat} (c : Q') (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) :
    Equiv (F H (.smul c e) f he hf) (mul (ofQ' c) (F H e f he hf)) := by
  have hef : Within (2*H) (.mul (mirror H e) f) :=
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩
  refine (joint_congr hw0 hw1 (2*H) (.mul (mirror H (.smul c e)) f)
    (.smul c (.mul (mirror H e) f)) _ hef ?_).trans
      (joint_smul hw0 hw1 (2*H) _ hef c)
  exact RatPolyCoeffEqv.polyMul_smul_left c _ _

theorem commonForm_smul_right {width H : Nat} (c : Q') (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) :
    Equiv (F H e (.smul c f) he hf) (mul (ofQ' c) (F H e f he hf)) :=
  (commonForm_symm hw0 hw1 H e (.smul c f) he hf).trans
    ((commonForm_smul_left hw0 hw1 c f e hf he).trans
      (Pivot2.mul_congr_right (commonForm_symm hw0 hw1 H f e hf he)))

private theorem negative_one_mul (A : CReal) : Equiv (mul (ofQ' (-1)) A) (neg A) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n))))

theorem commonForm_difference_left {width H : Nat} (e f g : WindowExpression width)
    (he : Within H e) (hf : Within H f) (hg : Within H g) :
    Equiv (F H (.add e (.smul (-1) f)) g ⟨he, hf⟩ hg)
      (sub (F H e g he hg) (F H f g hf hg)) :=
  (commonForm_add_left hw0 hw1 e (.smul (-1) f) g he hf hg).trans
    (CReal.add_congr_right
      ((commonForm_smul_left hw0 hw1 (-1) f g hf hg).trans
        (negative_one_mul (F H f g hf hg))))

theorem commonForm_difference_right {width H : Nat} (e f g : WindowExpression width)
    (he : Within H e) (hf : Within H f) (hg : Within H g) :
    Equiv (F H e (.add f (.smul (-1) g)) he ⟨hf, hg⟩)
      (sub (F H e f he hf) (F H e g he hg)) :=
  (commonForm_add_right hw0 hw1 e f (.smul (-1) g) he hf hg).trans
    (CReal.add_congr_right
      ((commonForm_smul_right hw0 hw1 (-1) e g he hg).trans
        (negative_one_mul (F H e g he hg))))

theorem intrinsicForm_sum_left {width : Nat} (x y z : IntrinsicExpression width) :
    Equiv (I (sum x y) z) (add (I x z) (I y z)) := by
  let H := max (max x.radius y.radius) z.radius
  have hx : x.radius ≤ H := by dsimp [H]; omega
  have hy : y.radius ≤ H := by dsimp [H]; omega
  have hz : z.radius ≤ H := by dsimp [H]; omega
  have hs : (sum x y).radius ≤ H := Nat.max_le.mpr ⟨hx, hy⟩
  have hp := intrinsicForm_chart hw0 hw1 (sum x y) z H hs hz
  refine Equiv.trans ?_ ((commonForm_add_left hw0 hw1 (chart H x) (chart H y) (chart H z)
    (chart_within H x hx) (chart_within H y hy) (chart_within H z hz)).trans
    (Equiv_add (intrinsicForm_chart hw0 hw1 x z H hx hz).symm
      (intrinsicForm_chart hw0 hw1 y z H hy hz).symm))
  simpa only [chart_sum H x y hx hy] using hp

theorem intrinsicForm_sum_right {width : Nat} (x y z : IntrinsicExpression width) :
    Equiv (I x (sum y z)) (add (I x y) (I x z)) :=
  (intrinsicForm_symm hw0 hw1 x (sum y z)).trans
    ((intrinsicForm_sum_left hw0 hw1 y z x).trans
      (Equiv_add (intrinsicForm_symm hw0 hw1 y x) (intrinsicForm_symm hw0 hw1 z x)))

theorem intrinsicForm_smul_left {width : Nat} (c : Q')
    (x y : IntrinsicExpression width) :
    Equiv (I (smul c x) y) (mul (ofQ' c) (I x y)) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  have hp := intrinsicForm_chart hw0 hw1 (smul c x) y H hx hy
  refine Equiv.trans ?_ ((commonForm_smul_left hw0 hw1 c (chart H x) (chart H y)
    (chart_within H x hx) (chart_within H y hy)).trans
    (Pivot2.mul_congr_right (intrinsicForm_chart hw0 hw1 x y H hx hy).symm))
  simpa only [chart_smul] using hp

theorem intrinsicForm_smul_right {width : Nat} (c : Q')
    (x y : IntrinsicExpression width) :
    Equiv (I x (smul c y)) (mul (ofQ' c) (I x y)) :=
  (intrinsicForm_symm hw0 hw1 x (smul c y)).trans
    ((intrinsicForm_smul_left hw0 hw1 c y x).trans
      (Pivot2.mul_congr_right (intrinsicForm_symm hw0 hw1 y x)))

theorem intrinsicForm_difference_left {width : Nat} (x y z : IntrinsicExpression width) :
    Equiv (I (difference x y) z) (sub (I x z) (I y z)) := by
  let H := max (max x.radius y.radius) z.radius
  have hx : x.radius ≤ H := by dsimp [H]; omega
  have hy : y.radius ≤ H := by dsimp [H]; omega
  have hz : z.radius ≤ H := by dsimp [H]; omega
  have hd : (difference x y).radius ≤ H := Nat.max_le.mpr ⟨hx, hy⟩
  have hp := intrinsicForm_chart hw0 hw1 (difference x y) z H hd hz
  refine Equiv.trans ?_ ((commonForm_difference_left hw0 hw1 (chart H x) (chart H y) (chart H z)
    (chart_within H x hx) (chart_within H y hy) (chart_within H z hz)).trans
    (Equiv_add (intrinsicForm_chart hw0 hw1 x z H hx hz).symm
      (neg_congr (intrinsicForm_chart hw0 hw1 y z H hy hz).symm)))
  simpa only [chart_difference H x y hx hy] using hp

theorem intrinsicForm_difference_right {width : Nat} (x y z : IntrinsicExpression width) :
    Equiv (I x (difference y z)) (sub (I x y) (I x z)) :=
  (intrinsicForm_symm hw0 hw1 x (difference y z)).trans
    ((intrinsicForm_difference_left hw0 hw1 y z x).trans
      (Equiv_add (intrinsicForm_symm hw0 hw1 y x)
        (neg_congr (intrinsicForm_symm hw0 hw1 z x))))

theorem intrinsicForm_difference_diagonal {width : Nat} (x y : IntrinsicExpression width) :
    Equiv (I (difference x y) (difference x y))
      (sub (sub (I x x) (I x y)) (sub (I y x) (I y y))) :=
  (intrinsicForm_difference_left hw0 hw1 x y (difference x y)).trans
    (Equiv_add (intrinsicForm_difference_right hw0 hw1 x x y)
      (neg_congr (intrinsicForm_difference_right hw0 hw1 y x y)))

theorem intrinsicForm_zero_left {width : Nat} (x : IntrinsicExpression width) :
    Equiv (I (zero width) x) czero :=
  (intrinsicForm_smul_left hw0 hw1 0 (unit width) x).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv ((I (unit width) x).approx n)))

theorem intrinsicForm_zero_right {width : Nat} (x : IntrinsicExpression width) :
    Equiv (I x (zero width)) czero :=
  (intrinsicForm_symm hw0 hw1 x (zero width)).trans (intrinsicForm_zero_left hw0 hw1 x)

private theorem joint_one {width L : Nat} :
    Equiv (originalJointLimit hw0 hw1 L (.one : WindowExpression width) True.intro) (ofQ' 1) :=
  Equiv_of_limit_of_equal
    (fun stage => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _
        (originalWindowScalar_pin hw0 hw1 L .one True.intro stage stage stage)
        (windowRatio_one hw0 hw1 _ _ _ stage L stage)))
    (originalJoint_diagonal_converges hw0 hw1 L .one True.intro)
    (convergesTo_const (ofQ' 1))

theorem intrinsicForm_unit_unit {width : Nat} :
    Equiv (I (unit width) (unit width)) (ofQ' 1) := by
  unfold BF4WilsonAllNomeReflectedForm.intrinsicForm commonForm
  refine (joint_congr hw0 hw1 0 (.mul (mirror 0 .one) .one) .one _ True.intro ?_).trans
    (joint_one hw0 hw1)
  exact BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.RatPolyCoeffEqv.one_mul _

end YMGap.Continuum.BF4WilsonAllNomeFormLaws

#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.commonForm_add_left
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.commonForm_add_right
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.commonForm_smul_left
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.commonForm_smul_right
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.commonForm_difference_left
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.commonForm_difference_right
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.intrinsicForm_sum_left
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.intrinsicForm_sum_right
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.intrinsicForm_smul_left
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.intrinsicForm_smul_right
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.intrinsicForm_difference_left
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.intrinsicForm_difference_right
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.intrinsicForm_difference_diagonal
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.intrinsicForm_zero_left
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.intrinsicForm_zero_right
#print axioms YMGap.Continuum.BF4WilsonAllNomeFormLaws.intrinsicForm_unit_unit
