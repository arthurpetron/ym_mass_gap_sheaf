/-
# Signed linearity of the SAME original Wilson joint limit

Each identity is transported from the existing finite normalized window
functional along its actual diagonal sequence. The action, partition and
fixed width/nome remain the same. The four-term difference-product identity
is used by the original reflected moment-convexity argument; it is not a
factorization of interacting expectations or a new state construction.
-/
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws

namespace YMGap.Continuum.BF4WilsonJointFunctionalLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] originalWindowScalar originalJointLimit windowRatio

def difference {width : Nat} (e f : WindowExpression width) : WindowExpression width :=
  .add e (.smul (-1) f)

theorem difference_within {width L : Nat} {e f : WindowExpression width}
    (he : Within L e) (hf : Within L f) : Within L (difference e f) := ⟨he, hf⟩

theorem source_difference {width : Nat} (e f : WindowExpression width) :
    RatPolyCoeffEqv (sourcePolynomial (difference e f))
      (polyAdd (sourcePolynomial e) (polyNeg (sourcePolynomial f))) :=
  (RatPolyCoeffEqv.refl _).add
    ((cap_mul_left (-1) _).symm.trans
      (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => sourcePolynomial f)))

theorem equiv_add {a b c d : CReal} (h : Equiv a b) (k : Equiv c d) :
    Equiv (CReal.add a c) (CReal.add b d) :=
  Equiv.trans (add_congr_left h) (add_congr_right k)

theorem equiv_sub {a b c d : CReal} (h : Equiv a b) (k : Equiv c d) :
    Equiv (CReal.sub a c) (CReal.sub b d) := equiv_add h (neg_congr k)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

theorem joint_congr (L : Nat) (e f : WindowExpression width)
    (he : Within L e) (hf : Within L f)
    (h : RatPolyCoeffEqv (sourcePolynomial e) (sourcePolynomial f)) :
    Equiv (originalJointLimit hw0 hw1 L e he) (originalJointLimit hw0 hw1 L f hf) :=
  Equiv_of_limit_of_equal
    (fun stage => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _ (originalWindowScalar_pin hw0 hw1 L e he stage stage stage)
        (Q'.eqv_trans _ _ _ (windowRatio_congr hw0 hw1 _ width _ stage L stage h)
          (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L f hf stage stage stage)))))
    (originalJoint_diagonal_converges hw0 hw1 L e he)
    (originalJoint_diagonal_converges hw0 hw1 L f hf)

theorem joint_add (L : Nat) (e f : WindowExpression width)
    (he : Within L e) (hf : Within L f) :
    Equiv (originalJointLimit hw0 hw1 L (.add e f) ⟨he, hf⟩)
      (CReal.add (originalJointLimit hw0 hw1 L e he) (originalJointLimit hw0 hw1 L f hf)) :=
  Equiv_of_limit_of_equal
    (fun stage => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _ (originalWindowScalar_pin hw0 hw1 L (.add e f) ⟨he,hf⟩ stage stage stage)
        (Q'.eqv_trans _ _ _ (windowRatio_add hw0 hw1 _ width _ stage L stage _ _)
          (Q'.eqv_symm (Q'.add_eqv_congr'
            (originalWindowScalar_pin hw0 hw1 L e he stage stage stage)
            (originalWindowScalar_pin hw0 hw1 L f hf stage stage stage))))))
    (originalJoint_diagonal_converges hw0 hw1 L (.add e f) ⟨he,hf⟩)
    (TrigAddCReal.convergesTo_add
      (originalJoint_diagonal_converges hw0 hw1 L e he)
      (originalJoint_diagonal_converges hw0 hw1 L f hf))

private theorem negative_one_mul (q : Q') : (-1 : Q')*q ≈ -q :=
  poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
    (by decide) (fun _ => q)

theorem joint_negate (L : Nat) (e : WindowExpression width) (he : Within L e) :
    Equiv (originalJointLimit hw0 hw1 L (.smul (-1) e) he)
      (CReal.neg (originalJointLimit hw0 hw1 L e he)) := by
  apply Equiv_of_limit_of_equal ?_
    (originalJoint_diagonal_converges hw0 hw1 L (.smul (-1) e) he)
    (TrigAddCReal.convergesTo_neg (originalJoint_diagonal_converges hw0 hw1 L e he))
  intro stage
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  change originalWindowScalar hw0 hw1 L (.smul (-1) e) stage stage stage ≈
    -(originalWindowScalar hw0 hw1 L e stage stage stage)
  exact Q'.eqv_trans _ _ _ (originalWindowScalar_pin hw0 hw1 L (.smul (-1) e) he stage stage stage)
    (Q'.eqv_trans _ _ _ (windowRatio_smul hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) stage L stage (-1) (sourcePolynomial e))
      (Q'.eqv_trans _ _ _ (negative_one_mul _)
        (Q'.neg_eqv_congr _ _
          (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L e he stage stage stage)))))

theorem joint_difference (L : Nat) (e f : WindowExpression width)
    (he : Within L e) (hf : Within L f) :
    Equiv (originalJointLimit hw0 hw1 L (difference e f) (difference_within he hf))
      (CReal.sub (originalJointLimit hw0 hw1 L e he) (originalJointLimit hw0 hw1 L f hf)) :=
  Equiv.trans (joint_add hw0 hw1 L e (.smul (-1) f) he hf)
    (add_congr_right (joint_negate hw0 hw1 L f hf))

/-- Exact four-point expansion, keeping all signed cross terms of the SAME state. -/
theorem joint_difference_product (L : Nat) (a b c d : WindowExpression width)
    (ha : Within L a) (hb : Within L b) (hc : Within L c) (hd : Within L d) :
    Equiv (originalJointLimit hw0 hw1 L (.mul (difference a b) (difference c d))
      ⟨difference_within ha hb, difference_within hc hd⟩)
      (CReal.add
        (CReal.sub (originalJointLimit hw0 hw1 L (.mul a c) ⟨ha,hc⟩)
          (originalJointLimit hw0 hw1 L (.mul a d) ⟨ha,hd⟩))
        (CReal.sub (originalJointLimit hw0 hw1 L (.mul b d) ⟨hb,hd⟩)
          (originalJointLimit hw0 hw1 L (.mul b c) ⟨hb,hc⟩))) := by
  let e : WindowExpression width :=
    .add (difference (.mul a c) (.mul a d)) (difference (.mul b d) (.mul b c))
  have he : Within L e := ⟨⟨⟨ha,hc⟩,⟨ha,hd⟩⟩,⟨⟨hb,hd⟩,⟨hb,hc⟩⟩⟩
  have hp : RatPolyCoeffEqv
      (sourcePolynomial (.mul (difference a b) (difference c d))) (sourcePolynomial e) :=
    ((source_difference a b).mul (source_difference c d)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3))))
        (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 0) (.var 3))))
          (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 1) (.var 2)))))
        (by decide) (fun | 0 => sourcePolynomial a | 1 => sourcePolynomial b
                         | 2 => sourcePolynomial c | _ => sourcePolynomial d)).trans
        ((source_difference (.mul a c) (.mul a d)).add
          (source_difference (.mul b d) (.mul b c))).symm)
  exact Equiv.trans (joint_congr hw0 hw1 L _ e _ he hp)
    (Equiv.trans (joint_add hw0 hw1 L _ _ he.1 he.2)
      (equiv_add (joint_difference hw0 hw1 L (.mul a c) (.mul a d) ⟨ha,hc⟩ ⟨ha,hd⟩)
        (joint_difference hw0 hw1 L (.mul b d) (.mul b c) ⟨hb,hd⟩ ⟨hb,hc⟩)))

end YMGap.Continuum.BF4WilsonJointFunctionalLaws

#print axioms YMGap.Continuum.BF4WilsonJointFunctionalLaws.difference
#print axioms YMGap.Continuum.BF4WilsonJointFunctionalLaws.difference_within
#print axioms YMGap.Continuum.BF4WilsonJointFunctionalLaws.source_difference
#print axioms YMGap.Continuum.BF4WilsonJointFunctionalLaws.equiv_add
#print axioms YMGap.Continuum.BF4WilsonJointFunctionalLaws.equiv_sub
#print axioms YMGap.Continuum.BF4WilsonJointFunctionalLaws.joint_congr
#print axioms YMGap.Continuum.BF4WilsonJointFunctionalLaws.joint_add
#print axioms YMGap.Continuum.BF4WilsonJointFunctionalLaws.joint_negate
#print axioms YMGap.Continuum.BF4WilsonJointFunctionalLaws.joint_difference
#print axioms YMGap.Continuum.BF4WilsonJointFunctionalLaws.joint_difference_product
