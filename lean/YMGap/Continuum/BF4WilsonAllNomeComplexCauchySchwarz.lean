/-
# Sharp complex Cauchy--Schwarz for the original all-nome Wilson completion

The rational finite inequality is transported through the original joint
cutoff/time limit and the existing represented Wilson pairing. Both components
retain the literal source width and original action. No quotient-real
representative or additional analytic bound is selected.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexification
import YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz
import YMGap.Continuum.CRealSeminormPairingCompletionLimit
import YMGap.Continuum.ArctanTrigConvergesProof

namespace YMGap.Continuum.BF4WilsonAllNomeComplexCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
  (originalWindowScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeComplexification
open YMGap.Continuum.CRealSeminormPairingCompletion
  (representativeInner pairSequence_converges)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

private theorem mul_congr {a b c d : CReal} (hab : Equiv a b) (hcd : Equiv c d) :
    Equiv (mul a c) (mul b d) :=
  Equiv.trans (CReal.mul_congr_left hab) (TrigSignedAdd.mul_congr_right hcd)

private theorem sub_congr {a b c d : CReal} (hab : Equiv a b) (hcd : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add hab (neg_congr hcd)

private def commonRe (H : Nat) (x y : WindowExpression width × WindowExpression width)
    (hx1 : Within H x.1) (hx2 : Within H x.2)
    (hy1 : Within H y.1) (hy2 : Within H y.2) : CReal :=
  add (commonForm hw0 hw1 H x.1 y.1 hx1 hy1)
    (commonForm hw0 hw1 H x.2 y.2 hx2 hy2)

private def commonIm (H : Nat) (x y : WindowExpression width × WindowExpression width)
    (hx1 : Within H x.1) (hx2 : Within H x.2)
    (hy1 : Within H y.1) (hy2 : Within H y.2) : CReal :=
  sub (commonForm hw0 hw1 H x.1 y.2 hx1 hy2)
    (commonForm hw0 hw1 H x.2 y.1 hx2 hy1)

private def commonNorm (H : Nat) (x : WindowExpression width × WindowExpression width)
    (hx1 : Within H x.1) (hx2 : Within H x.2) : CReal :=
  add (commonForm hw0 hw1 H x.1 x.1 hx1 hx1)
    (commonForm hw0 hw1 H x.2 x.2 hx2 hx2)

private theorem common_pair_converges (H : Nat) (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) :
    ConvergesTo
      (fun stage => ofQ' (originalWindowScalar hw0 hw1 (2*H)
        (.mul (mirror H e) f) stage stage stage))
      (commonForm hw0 hw1 H e f he hf) :=
  originalJoint_diagonal_converges hw0 hw1 (2*H) (.mul (mirror H e) f)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩

/-- The sharp finite bound survives the actual joint diagonal limit, before
any intrinsic source chart or completion quotient is used. -/
theorem common_complex_cauchySchwarz (H : Nat)
    (x y : WindowExpression width × WindowExpression width)
    (hx1 : Within H x.1) (hx2 : Within H x.2)
    (hy1 : Within H y.1) (hy2 : Within H y.2) :
    leEv
      (add
        (mul (commonRe hw0 hw1 width H x y hx1 hx2 hy1 hy2)
          (commonRe hw0 hw1 width H x y hx1 hx2 hy1 hy2))
        (mul (commonIm hw0 hw1 width H x y hx1 hx2 hy1 hy2)
          (commonIm hw0 hw1 width H x y hx1 hx2 hy1 hy2)))
      (mul (commonNorm hw0 hw1 width H x hx1 hx2)
        (commonNorm hw0 hw1 width H y hy1 hy2)) := by
  have h11 := common_pair_converges hw0 hw1 width H x.1 y.1 hx1 hy1
  have h22 := common_pair_converges hw0 hw1 width H x.2 y.2 hx2 hy2
  have h12 := common_pair_converges hw0 hw1 width H x.1 y.2 hx1 hy2
  have h21 := common_pair_converges hw0 hw1 width H x.2 y.1 hx2 hy1
  have hxx1 := common_pair_converges hw0 hw1 width H x.1 x.1 hx1 hx1
  have hxx2 := common_pair_converges hw0 hw1 width H x.2 x.2 hx2 hx2
  have hyy1 := common_pair_converges hw0 hw1 width H y.1 y.1 hy1 hy1
  have hyy2 := common_pair_converges hw0 hw1 width H y.2 y.2 hy2 hy2
  have hre := TrigAddCReal.convergesTo_add h11 h22
  have him := TrigAddCReal.convergesTo_add h12
    (TrigAddCReal.convergesTo_neg h21)
  have hxx := TrigAddCReal.convergesTo_add hxx1 hxx2
  have hyy := TrigAddCReal.convergesTo_add hyy1 hyy2
  unfold commonRe commonIm commonNorm
  refine leEv_of_convergesTo_le
    (TrigAddCReal.convergesTo_add
      (convergesTo_mul_general hre hre)
      (convergesTo_mul_general him him))
    (convergesTo_mul_general hxx hyy) ?_
  intro stage epsilon hepsilon
  refine ⟨0, fun _ _ => ?_⟩
  have hfinite := finiteWindowComplex_cauchySchwarz hw0 hw1 width H stage stage
    x y hx1 hx2 hy1 hy2
  change
    (originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H x.1) y.1) stage stage stage +
      originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H x.2) y.2) stage stage stage) *
      (originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H x.1) y.1) stage stage stage +
        originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H x.2) y.2) stage stage stage) +
    (originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H x.1) y.2) stage stage stage -
      originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H x.2) y.1) stage stage stage) *
      (originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H x.1) y.2) stage stage stage -
        originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H x.2) y.1) stage stage stage) ≤
    (originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H x.1) x.1) stage stage stage +
      originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H x.2) x.2) stage stage stage) *
      (originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H y.1) y.1) stage stage stage +
        originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H y.2) y.2) stage stage stage)
    at hfinite
  exact Q'.le_trans' _ _ _ hfinite
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

private def intrinsicRe (x y : IntrinsicExpression width × IntrinsicExpression width) : CReal :=
  add (intrinsicForm hw0 hw1 x.1 y.1) (intrinsicForm hw0 hw1 x.2 y.2)

private def intrinsicIm (x y : IntrinsicExpression width × IntrinsicExpression width) : CReal :=
  sub (intrinsicForm hw0 hw1 x.1 y.2) (intrinsicForm hw0 hw1 x.2 y.1)

private def intrinsicNorm (x : IntrinsicExpression width × IntrinsicExpression width) : CReal :=
  add (intrinsicForm hw0 hw1 x.1 x.1) (intrinsicForm hw0 hw1 x.2 x.2)

/-- Sharp complex Cauchy--Schwarz on the literal intrinsic Wilson source. -/
theorem intrinsic_complex_cauchySchwarz
    (x y : IntrinsicExpression width × IntrinsicExpression width) :
    leEv
      (add (mul (intrinsicRe hw0 hw1 width x y) (intrinsicRe hw0 hw1 width x y))
        (mul (intrinsicIm hw0 hw1 width x y) (intrinsicIm hw0 hw1 width x y)))
      (mul (intrinsicNorm hw0 hw1 width x) (intrinsicNorm hw0 hw1 width y)) := by
  let H := max (max x.1.radius x.2.radius) (max y.1.radius y.2.radius)
  have hx1 : x.1.radius ≤ H := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hx2 : x.2.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hy1 : y.1.radius ≤ H := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hy2 : y.2.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  let X : WindowExpression width × WindowExpression width := (chart H x.1,chart H x.2)
  let Y : WindowExpression width × WindowExpression width := (chart H y.1,chart H y.2)
  have hX1 : Within H X.1 := chart_within H x.1 hx1
  have hX2 : Within H X.2 := chart_within H x.2 hx2
  have hY1 : Within H Y.1 := chart_within H y.1 hy1
  have hY2 : Within H Y.2 := chart_within H y.2 hy2
  have h11 := intrinsicForm_chart hw0 hw1 x.1 y.1 H hx1 hy1
  have h22 := intrinsicForm_chart hw0 hw1 x.2 y.2 H hx2 hy2
  have h12 := intrinsicForm_chart hw0 hw1 x.1 y.2 H hx1 hy2
  have h21 := intrinsicForm_chart hw0 hw1 x.2 y.1 H hx2 hy1
  have hxx1 := intrinsicForm_chart hw0 hw1 x.1 x.1 H hx1 hx1
  have hxx2 := intrinsicForm_chart hw0 hw1 x.2 x.2 H hx2 hx2
  have hyy1 := intrinsicForm_chart hw0 hw1 y.1 y.1 H hy1 hy1
  have hyy2 := intrinsicForm_chart hw0 hw1 y.2 y.2 H hy2 hy2
  have hre : Equiv (intrinsicRe hw0 hw1 width x y)
      (commonRe hw0 hw1 width H X Y hX1 hX2 hY1 hY2) :=
    Equiv_add h11 h22
  have him : Equiv (intrinsicIm hw0 hw1 width x y)
      (commonIm hw0 hw1 width H X Y hX1 hX2 hY1 hY2) :=
    sub_congr h12 h21
  have hxx : Equiv (intrinsicNorm hw0 hw1 width x)
      (commonNorm hw0 hw1 width H X hX1 hX2) := Equiv_add hxx1 hxx2
  have hyy : Equiv (intrinsicNorm hw0 hw1 width y)
      (commonNorm hw0 hw1 width H Y hY1 hY2) := Equiv_add hyy1 hyy2
  exact leEv_trans
    (leEv_of_equiv
      (Equiv_add (mul_congr hre hre) (mul_congr him him)))
    (leEv_trans
      (common_complex_cauchySchwarz hw0 hw1 width H X Y hX1 hX2 hY1 hY2)
      (leEv_of_equiv (Equiv.symm (mul_congr hxx hyy))))

local notation "P" => pairingData hw0 hw1 (width := width)
local notation "D" => BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)
local notation "R" => representativeInner P
local notation "I" => inner hw0 hw1 width

/-- Both Cauchy coordinates use their original represented pairing limits. -/
theorem representative_complex_cauchySchwarz
    (X Y : (D).Cauchy × (D).Cauchy) :
    leEv
      (add
        (mul (add (R X.1 Y.1) (R X.2 Y.2))
          (add (R X.1 Y.1) (R X.2 Y.2)))
        (mul (sub (R X.1 Y.2) (R X.2 Y.1))
          (sub (R X.1 Y.2) (R X.2 Y.1))))
      (mul (add (R X.1 X.1) (R X.2 X.2))
        (add (R Y.1 Y.1) (R Y.2 Y.2))) := by
  have hre := TrigAddCReal.convergesTo_add
    (pairSequence_converges P X.1 Y.1) (pairSequence_converges P X.2 Y.2)
  have him := TrigAddCReal.convergesTo_add
    (pairSequence_converges P X.1 Y.2)
    (TrigAddCReal.convergesTo_neg (pairSequence_converges P X.2 Y.1))
  have hxx := TrigAddCReal.convergesTo_add
    (pairSequence_converges P X.1 X.1) (pairSequence_converges P X.2 X.2)
  have hyy := TrigAddCReal.convergesTo_add
    (pairSequence_converges P Y.1 Y.1) (pairSequence_converges P Y.2 Y.2)
  exact leEv_of_convergesTo_le
    (TrigAddCReal.convergesTo_add
      (convergesTo_mul_general hre hre)
      (convergesTo_mul_general him him))
    (convergesTo_mul_general hxx hyy)
    (fun n => intrinsic_complex_cauchySchwarz hw0 hw1 width
      (X.1.seq n,X.2.seq n) (Y.1.seq n,Y.2.seq n))

/-- Sharp complex Cauchy--Schwarz, with constant one, for the existing
all-nome Wilson complexification. -/
theorem inner_cauchySchwarz (x y : ComplexCarrier hw0 hw1 width) :
    RCle
      (RCadd (RCmul (I x y).1 (I x y).1) (RCmul (I x y).2 (I x y).2))
      (RCmul (I x x).1 (I y y).1) := by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  refine Quotient.inductionOn₂ x₁ x₂ ?_
  intro X₁ X₂
  refine Quotient.inductionOn₂ y₁ y₂ ?_
  intro Y₁ Y₂
  exact representative_complex_cauchySchwarz hw0 hw1 width (X₁,X₂) (Y₁,Y₂)

end YMGap.Continuum.BF4WilsonAllNomeComplexCauchySchwarz

#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexCauchySchwarz.common_complex_cauchySchwarz
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexCauchySchwarz.intrinsic_complex_cauchySchwarz
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexCauchySchwarz.representative_complex_cauchySchwarz
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexCauchySchwarz.inner_cauchySchwarz
