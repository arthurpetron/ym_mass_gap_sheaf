/-
# Ordinary Cauchy--Schwarz in the original Wilson joint state

At every finite heat/time stage, the normalized original window functional is
positive on arbitrary supported polynomial squares. Applying the existing
rational pre-inner-form argument to products of two window expressions gives
sharp Cauchy--Schwarz with the SAME action and partition. The three products
then pass to the already constructed joint cutoff/time limits.

This is ordinary state positivity, not reflected OS positivity. Width and
nome remain fixed, and no spatial decay, scaling limit or mass gap is asserted.
-/

import YMGap.Continuum.BF4WilsonJointFunctionalLaws
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] originalWindowScalar originalJointLimit windowRatio

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private def finitePairing {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L stage : Nat) (e f : WindowExpression width) : Q' :=
  windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
    stage L stage (polyMul (sourcePolynomial e) (sourcePolynomial f))

private theorem finite_add_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L stage : Nat) (e f g : WindowExpression width) :
    finitePairing hw0 hw1 L stage (.add e f) g ≈
      finitePairing hw0 hw1 L stage e g + finitePairing hw0 hw1 L stage f g := by
  unfold finitePairing
  rw [sourcePolynomial, polyMul_add_left_exact]
  exact windowRatio_add hw0 hw1 _ width _ stage L stage _ _

private theorem finite_smul_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L stage : Nat) (c : Q') (e f : WindowExpression width) :
    finitePairing hw0 hw1 L stage (.smul c e) f ≈
      c * finitePairing hw0 hw1 L stage e f := by
  unfold finitePairing
  exact Q'.eqv_trans _ _ _
    (windowRatio_congr hw0 hw1 _ width _ stage L stage
      (RatPolyCoeffEqv.polyMul_smul_left c (sourcePolynomial e) (sourcePolynomial f)))
    (windowRatio_smul hw0 hw1 _ width _ stage L stage c _)

private theorem finite_symm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L stage : Nat) (e f : WindowExpression width) :
    finitePairing hw0 hw1 L stage e f ≈ finitePairing hw0 hw1 L stage f e := by
  unfold finitePairing
  exact windowRatio_congr hw0 hw1 _ width _ stage L stage (RatPolyCoeffEqv.mul_comm _ _)

private def guardedExpression (width L : Nat) :=
  {e : WindowExpression width // Within L e}

private def finitePreInnerForm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width L stage : Nat) : PreInnerForm (guardedExpression width L) where
  B := fun e f => finitePairing hw0 hw1 L stage e.val f.val
  nonnegQuad := by
    intro s r e f
    let combination : WindowExpression width := .add (.smul s e.val) (.smul r f.val)
    let B := finitePairing hw0 hw1 (width := width) L stage
    have hc : Within L combination := ⟨e.property, f.property⟩
    have hnonnegative : (0 : Q') ≤ B combination combination := by
      exact windowRatio_square_nonnegative hw0 hw1 _ width _ stage L stage
        (source_supported L combination hc)
    have he : B e.val combination ≈ s * B e.val e.val + r * B e.val f.val := by
      exact Q'.eqv_trans _ _ _ (finite_symm hw0 hw1 L stage e.val combination)
        (Q'.eqv_trans _ _ _
          (finite_add_left hw0 hw1 L stage (.smul s e.val) (.smul r f.val) e.val)
          (Q'.add_eqv_congr'
            (finite_smul_left hw0 hw1 L stage s e.val e.val)
            (Q'.eqv_trans _ _ _ (finite_smul_left hw0 hw1 L stage r f.val e.val)
              (Q'.mul_eqv_congr_left _ _ _ (finite_symm hw0 hw1 L stage f.val e.val)))))
    have hf : B f.val combination ≈ s * B e.val f.val + r * B f.val f.val := by
      exact Q'.eqv_trans _ _ _ (finite_symm hw0 hw1 L stage f.val combination)
        (Q'.eqv_trans _ _ _
          (finite_add_left hw0 hw1 L stage (.smul s e.val) (.smul r f.val) f.val)
          (Q'.add_eqv_congr'
            (finite_smul_left hw0 hw1 L stage s e.val f.val)
            (finite_smul_left hw0 hw1 L stage r f.val f.val)))
    have hs : B (.smul s e.val) combination ≈
        s * (s * B e.val e.val + r * B e.val f.val) :=
      Q'.eqv_trans _ _ _ (finite_smul_left hw0 hw1 L stage s e.val combination)
        (Q'.mul_eqv_congr_left _ _ _ he)
    have hr : B (.smul r f.val) combination ≈
        r * (s * B e.val f.val + r * B f.val f.val) :=
      Q'.eqv_trans _ _ _ (finite_smul_left hw0 hw1 L stage r f.val combination)
        (Q'.mul_eqv_congr_left _ _ _ hf)
    have hexpand : B combination combination ≈
        s * (s * B e.val e.val + r * B e.val f.val) +
          r * (s * B e.val f.val + r * B f.val f.val) :=
      Q'.eqv_trans _ _ _ (finite_add_left hw0 hw1 L stage (.smul s e.val) (.smul r f.val) combination)
        (Q'.add_eqv_congr' hs hr)
    have hquad : B combination combination ≈
        s*s*B e.val e.val + 2*(s*r)*B e.val f.val + r*r*B f.val f.val :=
      Q'.eqv_trans _ _ _ hexpand (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv s (s*B e.val e.val) (r*B e.val f.val))
          (Q'.mul_add_eqv r (s*B e.val f.val) (r*B f.val f.val)))
        (YMGap.Continuum.GNSQuotient.GNSData.quad_regroup s r
          (B e.val e.val) (B e.val f.val) (B f.val f.val)))
    exact Q'.le_trans' _ _ _ hnonnegative (Q'.le_of_eqv hquad)

private theorem finite_cauchySchwarz {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
    (L stage : Nat) (e f : WindowExpression width) (he : Within L e) (hf : Within L f) :
    finitePairing hw0 hw1 L stage e f * finitePairing hw0 hw1 L stage e f ≤
      finitePairing hw0 hw1 L stage e e * finitePairing hw0 hw1 L stage f f :=
  (finitePreInnerForm hw0 hw1 width L stage).cauchy_schwarz ⟨e, he⟩ ⟨f, hf⟩

/-- Positivity of an ordinary square in the SAME original joint state. -/
theorem joint_square_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
    (L : Nat) (e : WindowExpression width) (he : Within L e) :
    leEv (ofQ' 0) (originalJointLimit hw0 hw1 L (.mul e e) ⟨he, he⟩) := by
  apply leEv_of_convergesTo_le (convergesTo_const _)
    (originalJoint_diagonal_converges hw0 hw1 L (.mul e e) ⟨he, he⟩)
  intro stage
  apply leEv_ofQ'_of_approx_ge
  intro k
  exact Q'.le_trans' _ _ _
    (windowRatio_square_nonnegative hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) stage L stage (source_supported L e he))
    (Q'.le_of_eqv (Q'.eqv_symm
      (originalWindowScalar_pin hw0 hw1 L (.mul e e) ⟨he, he⟩ stage stage stage)))

/-- Sharp ordinary Cauchy--Schwarz after joint heat/time removal. -/
theorem joint_cauchySchwarz {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
    (L : Nat) (e f : WindowExpression width) (he : Within L e) (hf : Within L f) :
    leEv
      (mul (originalJointLimit hw0 hw1 L (.mul e f) ⟨he, hf⟩)
        (originalJointLimit hw0 hw1 L (.mul e f) ⟨he, hf⟩))
      (mul (originalJointLimit hw0 hw1 L (.mul e e) ⟨he, he⟩)
        (originalJointLimit hw0 hw1 L (.mul f f) ⟨hf, hf⟩)) := by
  apply leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (originalJoint_diagonal_converges hw0 hw1 L (.mul e f) ⟨he, hf⟩)
      (originalJoint_diagonal_converges hw0 hw1 L (.mul e f) ⟨he, hf⟩))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (originalJoint_diagonal_converges hw0 hw1 L (.mul e e) ⟨he, he⟩)
      (originalJoint_diagonal_converges hw0 hw1 L (.mul f f) ⟨hf, hf⟩))
  intro stage
  have h := finite_cauchySchwarz hw0 hw1 L stage e f he hf
  have hef := originalWindowScalar_pin hw0 hw1 L (.mul e f) ⟨he, hf⟩ stage stage stage
  have hee := originalWindowScalar_pin hw0 hw1 L (.mul e e) ⟨he, he⟩ stage stage stage
  have hff := originalWindowScalar_pin hw0 hw1 L (.mul f f) ⟨hf, hf⟩ stage stage stage
  have hs := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (qmul hef hef))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (Q'.eqv_symm (qmul hee hff))))
  intro epsilon hepsilon
  refine ⟨0, fun k _ => ?_⟩
  exact Q'.le_trans' _ _ _ hs (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon))

/-- Rational homogeneity of the SAME original joint limit. -/
theorem joint_smul {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
    (L : Nat) (e : WindowExpression width) (he : Within L e) (c : Q') :
    Equiv (originalJointLimit hw0 hw1 L (.smul c e) he)
      (mul (ofQ' c) (originalJointLimit hw0 hw1 L e he)) :=
  Equiv_of_limit_of_equal
    (fun stage => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _
        (originalWindowScalar_pin hw0 hw1 L (.smul c e) he stage stage stage)
        (Q'.eqv_trans _ _ _
          (windowRatio_smul hw0 hw1 (headCutoff w+stage) width
            (Nat.le_add_right _ _) stage L stage c (sourcePolynomial e))
          (Q'.eqv_symm (Q'.mul_eqv_congr_left c _ _
            (originalWindowScalar_pin hw0 hw1 L e he stage stage stage))))))
    (originalJoint_diagonal_converges hw0 hw1 L (.smul c e) he)
    (convergesTo_const_mul (ofQ' c) (originalJoint_diagonal_converges hw0 hw1 L e he))

end YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz

#print axioms YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz.joint_square_nonnegative
#print axioms YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz.joint_cauchySchwarz
#print axioms YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz.joint_smul
