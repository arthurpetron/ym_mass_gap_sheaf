/-
# Cauchy--Schwarz for the literal all-nome reflected Wilson form

The finite form is the actual original window functional at the literal
source width.  Reflected positivity and the finite linear laws give a
constructive `PreInnerForm`; its Cauchy--Schwarz inequality is then passed
through the existing joint diagonal limits.  No collared action, completion,
small-nome hypothesis or scaling claim is introduced.
-/

import YMGap.Continuum.BF4WilsonAllNomeReflectedForm
import YMGap.Continuum.BF4WilsonAllNomeFormLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
import YMGap.Continuum.RationalOrthogonalPairBessel
import YMGap.Continuum.BF4ExactSlabFixedSpatialFiniteComplexRealification

namespace YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within)
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

private def finitePairing {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H stage t : Nat) (e f : WindowExpression width) : Q' :=
  originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H e) f) stage t t

private theorem finite_add_left {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H stage t : Nat) (e f g : WindowExpression width)
    (he : Within H e) (hf : Within H f) (hg : Within H g) :
    finitePairing hw0 hw1 H stage t (.add e f) g ≈
      finitePairing hw0 hw1 H stage t e g + finitePairing hw0 hw1 H stage t f g := by
  unfold finitePairing
  have hsum := originalWindowScalar_pin hw0 hw1 (2*H)
    (.mul (mirror H (.add e f)) g)
    ⟨mirror_within H (.add e f), within_mono (by omega : H ≤ 2*H) g hg⟩ stage t t
  have h1 := originalWindowScalar_pin hw0 hw1 (2*H)
    (.mul (mirror H e) g)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) g hg⟩ stage t t
  have h2 := originalWindowScalar_pin hw0 hw1 (2*H)
    (.mul (mirror H f) g)
    ⟨mirror_within H f, within_mono (by omega : H ≤ 2*H) g hg⟩ stage t t
  have hc : RatPolyCoeffEqv
      (sourcePolynomial (.mul (mirror H (.add e f)) g))
      (polyAdd (sourcePolynomial (.mul (mirror H e) g))
        (sourcePolynomial (.mul (mirror H f) g))) := by
    change RatPolyCoeffEqv
      (polyMul (polyAdd (sourcePolynomial (mirror H e))
        (sourcePolynomial (mirror H f))) (sourcePolynomial g)) _
    rw [polyMul_add_left_exact]
    exact RatPolyCoeffEqv.refl _
  have hadd := windowRatio_add hw0 hw1 (headCutoff w+stage) width (by omega) t (2*H) t
    (sourcePolynomial (.mul (mirror H e) g))
    (sourcePolynomial (.mul (mirror H f) g))
  exact Q'.eqv_trans _ _ _ hsum
    (Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 (headCutoff w+stage) _ _ t (2*H) t hc)
      (Q'.eqv_trans _ _ _ hadd
      (Q'.add_eqv_congr' (Q'.eqv_symm h1) (Q'.eqv_symm h2)))
    )

private theorem finite_smul_left {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H stage t : Nat) (c : Q') (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) :
    finitePairing hw0 hw1 H stage t (.smul c e) f ≈
      c * finitePairing hw0 hw1 H stage t e f := by
  unfold finitePairing
  have hp := originalWindowScalar_pin hw0 hw1 (2*H)
    (.mul (mirror H (.smul c e)) f)
    ⟨mirror_within H (.smul c e), within_mono (by omega : H ≤ 2*H) f hf⟩ stage t t
  have hbase := originalWindowScalar_pin hw0 hw1 (2*H)
    (.mul (mirror H e) f)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩ stage t t
  exact Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 (headCutoff w+stage) _ _ t (2*H) t
        (RatPolyCoeffEqv.polyMul_smul_left c _ _))
      (Q'.eqv_trans _ _ _
        (windowRatio_smul hw0 hw1 (headCutoff w+stage) _ _ t (2*H) t c _)
        (Q'.eqv_symm (Q'.mul_eqv_congr_left _ _ _ hbase))))

private theorem finite_symm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H stage t : Nat) (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) :
    finitePairing hw0 hw1 H stage t e f ≈
      finitePairing hw0 hw1 H stage t f e :=
  originalWindowScalar_reflected_symm hw0 hw1 H e f he hf stage t

private def guardedExpression (width H : Nat) :=
  {e : WindowExpression width // Within H e}

private def finitePreInnerForm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width H stage t : Nat) : PreInnerForm (guardedExpression width H) where
  B := fun e f => finitePairing hw0 hw1 H stage t e.val f.val
  nonnegQuad := by
    intro s r e f
    let combination : WindowExpression width := .add (.smul s e.val) (.smul r f.val)
    have hc : Within H combination := ⟨e.property, f.property⟩
    let B := finitePairing hw0 hw1 (width := width) H stage t
    have hn := reflectedWindowRatio_nonnegative hw0 hw1 H combination hc stage t
    have hp := originalWindowScalar_pin hw0 hw1 (2*H)
      (.mul (mirror H combination) combination)
      ⟨mirror_within H combination,
        within_mono (by omega : H ≤ 2*H) combination hc⟩ stage t t
    have hnon : (0 : Q') ≤ finitePairing hw0 hw1 H stage t combination combination :=
      Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.eqv_symm hp))
    have hec : B e.val combination ≈ s * B e.val e.val + r * B e.val f.val := by
      exact Q'.eqv_trans _ _ _ (finite_symm hw0 hw1 H stage t e.val combination e.property hc)
        (Q'.eqv_trans _ _ _
          (finite_add_left hw0 hw1 H stage t (.smul s e.val) (.smul r f.val) e.val
            e.property f.property e.property)
          (Q'.add_eqv_congr'
            (finite_smul_left hw0 hw1 H stage t s e.val e.val e.property e.property)
            (Q'.eqv_trans _ _ _
              (finite_smul_left hw0 hw1 H stage t r f.val e.val f.property e.property)
              (Q'.mul_eqv_congr_left _ _ _
                (finite_symm hw0 hw1 H stage t f.val e.val f.property e.property)))))
    have hfc : B f.val combination ≈ s * B e.val f.val + r * B f.val f.val := by
      exact Q'.eqv_trans _ _ _ (finite_symm hw0 hw1 H stage t f.val combination f.property hc)
        (Q'.eqv_trans _ _ _
          (finite_add_left hw0 hw1 H stage t (.smul s e.val) (.smul r f.val) f.val
            e.property f.property f.property)
          (Q'.add_eqv_congr'
            (finite_smul_left hw0 hw1 H stage t s e.val f.val e.property f.property)
            (finite_smul_left hw0 hw1 H stage t r f.val f.val f.property f.property)))
    have hs : B (.smul s e.val) combination ≈
        s * (s * B e.val e.val + r * B e.val f.val) :=
      Q'.eqv_trans _ _ _
        (finite_smul_left hw0 hw1 H stage t s e.val combination e.property hc)
        (Q'.mul_eqv_congr_left _ _ _ hec)
    have hr : B (.smul r f.val) combination ≈
        r * (s * B e.val f.val + r * B f.val f.val) :=
      Q'.eqv_trans _ _ _
        (finite_smul_left hw0 hw1 H stage t r f.val combination f.property hc)
        (Q'.mul_eqv_congr_left _ _ _ hfc)
    have hexpand : B combination combination ≈
        s * (s * B e.val e.val + r * B e.val f.val) +
          r * (s * B e.val f.val + r * B f.val f.val) :=
      Q'.eqv_trans _ _ _
        (finite_add_left hw0 hw1 H stage t (.smul s e.val) (.smul r f.val) combination
          e.property f.property hc) (Q'.add_eqv_congr' hs hr)
    have hquad : B combination combination ≈
        s*s*B e.val e.val + 2*(s*r)*B e.val f.val + r*r*B f.val f.val :=
      Q'.eqv_trans _ _ _ hexpand (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv s (s*B e.val e.val) (r*B e.val f.val))
          (Q'.mul_add_eqv r (s*B e.val f.val) (r*B f.val f.val)))
        (YMGap.Continuum.GNSQuotient.GNSData.quad_regroup s r
          (B e.val e.val) (B e.val f.val) (B f.val f.val)))
    exact Q'.le_trans' _ _ _ hnon (Q'.le_of_eqv hquad)

theorem intrinsicForm_cauchySchwarz {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x y : IntrinsicExpression width) :
    leEv (mul (intrinsicForm hw0 hw1 x y) (intrinsicForm hw0 hw1 x y))
      (mul (intrinsicForm hw0 hw1 x x) (intrinsicForm hw0 hw1 y y)) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  have hxy := intrinsicForm_chart hw0 hw1 x y H hx hy
  have hxx := intrinsicForm_chart hw0 hw1 x x H hx hx
  have hyy := intrinsicForm_chart hw0 hw1 y y H hy hy
  let ex := chart H x
  let ey := chart H y
  have hex : Within H ex := chart_within H x hx
  have hey : Within H ey := chart_within H y hy
  have hxyw : Within (2*H) (.mul (mirror H ex) ey) :=
    ⟨mirror_within H ex, within_mono (by omega : H ≤ 2*H) ey hey⟩
  have hxxw : Within (2*H) (.mul (mirror H ex) ex) :=
    ⟨mirror_within H ex, within_mono (by omega : H ≤ 2*H) ex hex⟩
  have hyyw : Within (2*H) (.mul (mirror H ey) ey) :=
    ⟨mirror_within H ey, within_mono (by omega : H ≤ 2*H) ey hey⟩
  refine leEv_trans (leEv_of_equiv (Pivot2.mul_congr hxy hxy)) ?_
  refine leEv_trans ?_ (leEv_of_equiv (Pivot2.mul_congr hxx.symm hyy.symm))
  apply leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (originalJoint_diagonal_converges hw0 hw1 (2*H) (.mul (mirror H ex) ey) hxyw)
      (originalJoint_diagonal_converges hw0 hw1 (2*H) (.mul (mirror H ex) ey) hxyw))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (originalJoint_diagonal_converges hw0 hw1 (2*H) (.mul (mirror H ex) ex) hxxw)
      (originalJoint_diagonal_converges hw0 hw1 (2*H) (.mul (mirror H ey) ey) hyyw))
  intro stage
  have hs := (finitePreInnerForm hw0 hw1 width H stage stage).cauchy_schwarz
    ⟨ex, hex⟩ ⟨ey, hey⟩
  intro epsilon hepsilon
  refine ⟨0, fun _ _ => ?_⟩
  exact Q'.le_trans' _ _ _ hs
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon))

private theorem zero_of_square_le_zero (A : CReal)
    (h : leEv (mul A A) (ofQ' 0)) : Equiv A (ofQ' 0) := by
  intro epsilon he
  obtain ⟨index, hN⟩ := h (epsilon*epsilon) (Q'.mul_pos he he)
  refine ⟨index, fun n hn => ?_⟩
  have hs : A.approx n * A.approx n ≤ epsilon*epsilon := by
    have hs := hN n hn
    change A.approx n * A.approx n ≤ 0 + epsilon*epsilon at hs
    rwa [Q'.zero_add'] at hs
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hs)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

theorem intrinsicForm_radical_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x y : IntrinsicExpression width)
    (hnull : Equiv (intrinsicForm hw0 hw1 x x) (ofQ' 0)) :
    Equiv (intrinsicForm hw0 hw1 x y) (ofQ' 0) :=
  zero_of_square_le_zero _ (leEv_trans
    (intrinsicForm_cauchySchwarz hw0 hw1 x y)
    (leEv_of_equiv ((Pivot2.mul_congr_left hnull).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        Q'.zero_mul_eqv ((intrinsicForm hw0 hw1 y y).approx n))))))

/-! The following complex bound uses the SAME literal original finite form.
Only the carrier-free direct-sum construction is reused from the older
finite realification module; its physical form is never substituted. -/

private theorem finite_add_right {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H stage t : Nat) (e f g : WindowExpression width)
    (he : Within H e) (hf : Within H f) (hg : Within H g) :
    finitePairing hw0 hw1 H stage t e (.add f g) ≈
      finitePairing hw0 hw1 H stage t e f + finitePairing hw0 hw1 H stage t e g :=
  Q'.eqv_trans _ _ _ (finite_symm hw0 hw1 H stage t e (.add f g) he ⟨hf,hg⟩)
    (Q'.eqv_trans _ _ _ (finite_add_left hw0 hw1 H stage t f g e hf hg he)
      (Q'.add_eqv_congr'
        (finite_symm hw0 hw1 H stage t f e hf he)
        (finite_symm hw0 hw1 H stage t g e hg he)))

private theorem finite_smul_right {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H stage t : Nat) (c : Q') (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) :
    finitePairing hw0 hw1 H stage t e (.smul c f) ≈
      c * finitePairing hw0 hw1 H stage t e f :=
  Q'.eqv_trans _ _ _ (finite_symm hw0 hw1 H stage t e (.smul c f) he hf)
    (Q'.eqv_trans _ _ _ (finite_smul_left hw0 hw1 H stage t c f e hf he)
      (Q'.mul_eqv_congr_left c _ _ (finite_symm hw0 hw1 H stage t f e hf he)))

private def complexFiniteForm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width H stage t : Nat) : PreInnerForm (guardedExpression width H × guardedExpression width H) :=
  BF4ExactSlabFixedSpatialFiniteComplexRealification.directSumPreInnerForm
    (finitePreInnerForm hw0 hw1 width H stage t) (finitePreInnerForm hw0 hw1 width H stage t)

private def complexFiniteAdd {width H : Nat}
    (x y : guardedExpression width H × guardedExpression width H) :
    guardedExpression width H × guardedExpression width H :=
  (⟨WindowExpression.add x.1.val y.1.val,⟨x.1.property,y.1.property⟩⟩,
   ⟨WindowExpression.add x.2.val y.2.val,⟨x.2.property,y.2.property⟩⟩)

private def complexFiniteSmul {width H : Nat} (c : Q')
    (x : guardedExpression width H × guardedExpression width H) :
    guardedExpression width H × guardedExpression width H :=
  (⟨WindowExpression.smul c x.1.val,x.1.property⟩,
   ⟨WindowExpression.smul c x.2.val,x.2.property⟩)

private def complexFiniteTurn {width H : Nat}
    (y : guardedExpression width H × guardedExpression width H) :
    guardedExpression width H × guardedExpression width H :=
  (y.2,⟨WindowExpression.smul (-1) y.1.val,y.1.property⟩)

section ComplexFinite

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width H stage t : Nat)

local notation "R" => complexFiniteForm hw0 hw1 width H stage t
local notation "B" => finitePairing hw0 hw1 (width := width) H stage t

private theorem complexFinite_add_right
    (x y z : guardedExpression width H × guardedExpression width H) :
    (R).B x (complexFiniteAdd y z) ≈ (R).B x y + (R).B x z := by
  dsimp only [complexFiniteForm,
    BF4ExactSlabFixedSpatialFiniteComplexRealification.directSumPreInnerForm,
    finitePreInnerForm,complexFiniteAdd]
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (finite_add_right hw0 hw1 H stage t _ _ _ x.1.property y.1.property z.1.property)
    (finite_add_right hw0 hw1 H stage t _ _ _ x.2.property y.2.property z.2.property)) ?_
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
    (by decide)
    (fun | 0 => B x.1.val y.1.val | 1 => B x.1.val z.1.val
         | 2 => B x.2.val y.2.val | _ => B x.2.val z.2.val)

private theorem complexFinite_smul_right (c : Q')
    (x y : guardedExpression width H × guardedExpression width H) :
    (R).B x (complexFiniteSmul c y) ≈ c*(R).B x y := by
  dsimp only [complexFiniteForm,
    BF4ExactSlabFixedSpatialFiniteComplexRealification.directSumPreInnerForm,
    finitePreInnerForm,complexFiniteSmul]
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (finite_smul_right hw0 hw1 H stage t c _ _ x.1.property y.1.property)
    (finite_smul_right hw0 hw1 H stage t c _ _ x.2.property y.2.property))
    (Q'.eqv_symm (Q'.mul_add_eqv c _ _))

private theorem complexFinite_symm
    (x y : guardedExpression width H × guardedExpression width H) :
    (R).B x y ≈ (R).B y x :=
  Q'.add_eqv_congr'
    (finite_symm hw0 hw1 H stage t _ _ x.1.property y.1.property)
    (finite_symm hw0 hw1 H stage t _ _ x.2.property y.2.property)

private theorem negative_one_mul (a : Q') : (-1)*a ≈ -a :=
  RingNormaliser.poly_identity_of_normal_eq
    (.mul (.neg (.const 1)) (.var 0)) (.neg (.var 0)) (by decide) (fun _ => a)

private theorem complexFinite_turn_pairing
    (x y : guardedExpression width H × guardedExpression width H) :
    (R).B x (complexFiniteTurn y) ≈ B x.1.val y.2.val - B x.2.val y.1.val := by
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _
      (finite_smul_right hw0 hw1 H stage t (-1) _ _ x.2.property y.1.property)
      (negative_one_mul _))

private theorem complexFinite_turn_orthogonal
    (y : guardedExpression width H × guardedExpression width H) :
    (R).B y (complexFiniteTurn y) ≈ 0 := by
  exact Q'.eqv_trans _ _ _ (complexFinite_turn_pairing hw0 hw1 width H stage t y y)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (finite_symm hw0 hw1 H stage t _ _ y.1.property y.2.property))
      (Q'.add_neg_self_eqv _))

private theorem complexFinite_turn_norm
    (y : guardedExpression width H × guardedExpression width H) :
    (R).B (complexFiniteTurn y) (complexFiniteTurn y) ≈ (R).B y y := by
  have h := Q'.eqv_trans _ _ _
    (finite_smul_left hw0 hw1 H stage t (-1) y.1.val (.smul (-1) y.1.val)
      y.1.property y.1.property)
    (Q'.mul_eqv_congr_left (-1) _ _
      (finite_smul_right hw0 hw1 H stage t (-1) _ _ y.1.property y.1.property))
  have hneg : (-1)*((-1)*B y.1.val y.1.val) ≈ B y.1.val y.1.val :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.neg (.const 1)) (.mul (.neg (.const 1)) (.var 0)))
      (.var 0) (by decide) (fun _ => B y.1.val y.1.val)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ h hneg))
    (Q'.add_comm_eqv _ _)

/-- Sharp complex Cauchy--Schwarz at the literal ORIGINAL finite window. -/
theorem finiteWindowComplex_cauchySchwarz
    (x y : WindowExpression width × WindowExpression width)
    (hx1 : Within H x.1) (hx2 : Within H x.2)
    (hy1 : Within H y.1) (hy2 : Within H y.2) :
    (B x.1 y.1+B x.2 y.2)*(B x.1 y.1+B x.2 y.2) +
      (B x.1 y.2-B x.2 y.1)*(B x.1 y.2-B x.2 y.1) ≤
    (B x.1 x.1+B x.2 x.2)*(B y.1 y.1+B y.2 y.2) := by
  let X : guardedExpression width H × guardedExpression width H := (⟨x.1,hx1⟩,⟨x.2,hx2⟩)
  let Y : guardedExpression width H × guardedExpression width H := (⟨y.1,hy1⟩,⟨y.2,hy2⟩)
  have h := RationalOrthogonalPairBessel.orthogonal_pair_bessel R
    complexFiniteAdd complexFiniteSmul
    (complexFinite_add_right hw0 hw1 width H stage t)
    (complexFinite_smul_right hw0 hw1 width H stage t)
    (complexFinite_symm hw0 hw1 width H stage t)
    X Y (complexFiniteTurn Y)
    (complexFinite_turn_orthogonal hw0 hw1 width H stage t Y)
    (complexFinite_turn_norm hw0 hw1 width H stage t Y)
  have hp := complexFinite_turn_pairing hw0 hw1 width H stage t X Y
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hp)
        (Q'.mul_eqv_congr_left _ _ _ hp)))) h

end ComplexFinite

end YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz

#print axioms YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz.intrinsicForm_cauchySchwarz
#print axioms YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz.intrinsicForm_radical_zero
#print axioms YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz.finiteWindowComplex_cauchySchwarz
