/-
# The actual completed cleared Jacobi addition square

The literal parity rectangles, their retained odd boundaries, and the
independently completed alternating endpoint determinant meet the SAME
product/radial-cost limit. Only a rational factor two is cancelled here;
no density inverse, differentiated value limit, or analytic identity premise
is used. This scalar equality does not supply an original-action/OS estimate
or a physical/scaling gap. Positive-normalization order cancellation is a
separate consumer.
-/

import YMGap.Continuum.ThetaJointRectangleCompletion
import YMGap.Continuum.ThetaAlternatingCompletedPin
import YMGap.Continuum.ThetaProductRadialCompletedPin
import YMGap.Continuum.Pivot2Moments
import YMGap.Constructive.CRealExp
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ThetaCompletedAdditionSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaJointRectangleCompletion
open YMGap.Continuum.ThetaOddSeriesCompletion
open YMGap.Continuum.ThetaEvenSeriesCompletion
open YMGap.Continuum.ThetaOneSidedSeriesCompletion
open YMGap.Continuum.ThetaAlternatingCompletedPin
open YMGap.Continuum.ThetaJointFrequencyCompletion
open YMGap.Continuum.JacobiTripleProductOnBox
open YMGap.Continuum.RingNormaliser (PolyExpr normalize eval poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
local infixl:65 " +ᶜ " => CReal.add
local infixl:65 " -ᶜ " => CReal.sub
local infixl:70 " *ᶜ " => CReal.mul
local notation "⟦" q "⟧" => CReal.ofQ' q

private theorem reflC (a : CReal) : CReal.Equiv a a :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem sub_congr {a a' b b' : CReal}
    (ha : CReal.Equiv a a') (hb : CReal.Equiv b b') :
    CReal.Equiv (a -ᶜ b) (a' -ᶜ b') :=
  Pivot2.add_congr ha (Pivot2.neg_congr hb)

private theorem four_product (w a b : CReal) :
    CReal.Equiv (w *ᶜ ((⟦(2 : Q')⟧ *ᶜ a) *ᶜ (⟦(2 : Q')⟧ *ᶜ b)))
      ((⟦(4 : Q')⟧ *ᶜ w) *ᶜ (a *ᶜ b)) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 2))))
    (.mul (.mul (.const 4) (.var 0)) (.mul (.var 1) (.var 2)))
    (by decide) (fun | 0 => w.approx n | 1 => a.approx n | _ => b.approx n)

/-- The factor four is obtained from the completed signed odd boundary pins,
not from an equality of finite unbalanced prefixes. -/
theorem valueRectangle_eq_oneSided {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (valueRectangleCReal hw0 hw1 hx0 hx1)
      ((evenCReal hw0 hw1 hx0 hx1 *ᶜ evenCReal hw0 hw1 (by decide) (Q'.le_refl' 1))
        +ᶜ ((⟦(4 : Q')⟧ *ᶜ ⟦w⟧) *ᶜ
          (oddCReal hw0 hw1 hx0 hx1 *ᶜ oddCReal hw0 hw1 (by decide) (Q'.le_refl' 1)))) := by
  apply Pivot2.add_congr (reflC _)
  exact CReal.Equiv.trans
    (Pivot2.mul_congr_right (A := ⟦w⟧)
      (Pivot2.mul_congr (oddSignedCReal_eq_twice hw0 hw1 hx0 hx1)
        (oddSignedCReal_eq_twice hw0 hw1 (by decide) (Q'.le_refl' 1))))
    (four_product _ _ _)

/-- The separately constructed endpoint-frequency rectangle has the same
one-sided normalization, without differentiation of a completed value. -/
theorem frequencyRectangle_eq_oneSided {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (frequencyRectangleCReal hw0 hw1 hx0 hx1)
      ((evenCReal hw0 hw1 hx0 hx1 *ᶜ evenEndpointCReal hw0 hw1)
        +ᶜ ((⟦(4 : Q')⟧ *ᶜ ⟦w⟧) *ᶜ
          (oddCReal hw0 hw1 hx0 hx1 *ᶜ oddEndpointCReal hw0 hw1))) := by
  apply Pivot2.add_congr (reflC _)
  exact CReal.Equiv.trans
    (Pivot2.mul_congr_right (A := ⟦w⟧)
      (Pivot2.mul_congr (oddSignedCReal_eq_twice hw0 hw1 hx0 hx1)
        (oddSignedEndpointCReal_eq_twice hw0 hw1)))
    (four_product _ _ _)

private def valueExpr : PolyExpr :=
  .add (.mul (.var 1) (.var 3))
    (.mul (.mul (.const 4) (.var 0)) (.mul (.var 2) (.var 4)))
private def valueOneExpr : PolyExpr :=
  .add (.mul (.var 3) (.var 3))
    (.mul (.mul (.const 4) (.var 0)) (.mul (.var 4) (.var 4)))
private def frequencyExpr : PolyExpr :=
  .add (.mul (.var 1) (.var 5))
    (.mul (.mul (.const 4) (.var 0)) (.mul (.var 2) (.var 6)))
private def frequencyOneExpr : PolyExpr :=
  .add (.mul (.var 3) (.var 5))
    (.mul (.mul (.const 4) (.var 0)) (.mul (.var 4) (.var 6)))
private def determinantExpr : PolyExpr :=
  .add (.mul (.var 3) (.var 2)) (.neg (.mul (.var 4) (.var 1)))
private def endpointExpr : PolyExpr :=
  .add (.mul (.var 3) (.var 6)) (.neg (.mul (.var 4) (.var 5)))

private theorem rectangle_determinant (w e h e1 h1 ep hp : CReal) :
    CReal.Equiv
      (((e *ᶜ e1 +ᶜ (⟦(4 : Q')⟧ *ᶜ w) *ᶜ (h *ᶜ h1)) *ᶜ
          (e1 *ᶜ ep +ᶜ (⟦(4 : Q')⟧ *ᶜ w) *ᶜ (h1 *ᶜ hp))) -ᶜ
        ((e1 *ᶜ e1 +ᶜ (⟦(4 : Q')⟧ *ᶜ w) *ᶜ (h1 *ᶜ h1)) *ᶜ
          (e *ᶜ ep +ᶜ (⟦(4 : Q')⟧ *ᶜ w) *ᶜ (h *ᶜ hp))))
      ((⟦(-4 : Q')⟧ *ᶜ w) *ᶜ
        ((e1 *ᶜ h -ᶜ h1 *ᶜ e) *ᶜ (e1 *ᶜ hp -ᶜ h1 *ᶜ ep))) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact poly_identity_of_normal_eq
    (.add (.mul valueExpr frequencyOneExpr) (.neg (.mul valueOneExpr frequencyExpr)))
    (.mul (.mul (.const (-4)) (.var 0)) (.mul determinantExpr endpointExpr))
    (by decide)
    (fun
      | 0 => w.approx n
      | 1 => e.approx n
      | 2 => h.approx n
      | 3 => e1.approx n
      | 4 => h1.approx n
      | 5 => ep.approx n
      | _ => hp.approx n)

private theorem cost_factor (v v1 d d1 : CReal) :
    CReal.Equiv
      ((v *ᶜ (⟦(2 : Q')⟧ *ᶜ (v1 *ᶜ d1))) -ᶜ
        (v1 *ᶜ (⟦(2 : Q')⟧ *ᶜ (v *ᶜ d))))
      (⟦(2 : Q')⟧ *ᶜ (v1 *ᶜ ((d1 -ᶜ d) *ᶜ v))) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.mul (.const 2) (.mul (.var 1) (.var 3))))
      (.neg (.mul (.var 1) (.mul (.const 2) (.mul (.var 0) (.var 2))))))
    (.mul (.const 2) (.mul (.var 1)
      (.mul (.add (.var 3) (.neg (.var 2))) (.var 0))))
    (by decide) (fun
      | 0 => v.approx n
      | 1 => v1.approx n
      | 2 => d.approx n
      | _ => d1.approx n)

private theorem signed_factor (w x : Q') (a b : CReal) :
    CReal.Equiv
      ((⟦(-4 : Q')⟧ *ᶜ ⟦w⟧) *ᶜ ((⟦x + -(1 : Q')⟧ *ᶜ (a *ᶜ a)) *ᶜ (b *ᶜ b)))
      (⟦(2 : Q')⟧ *ᶜ (⟦2*w*(1 + -x)⟧ *ᶜ ((a *ᶜ a) *ᶜ (b *ᶜ b)))) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact poly_identity_of_normal_eq
    (.mul (.mul (.const (-4)) (.var 0))
      (.mul (.mul (.add (.var 1) (.neg (.const 1))) (.mul (.var 2) (.var 2)))
        (.mul (.var 3) (.var 3))))
    (.mul (.const 2) (.mul
      (.mul (.mul (.const 2) (.var 0)) (.add (.const 1) (.neg (.var 1))))
      (.mul (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
    (by decide) (fun | 0 => w | 1 => x | 2 => a.approx n | _ => b.approx n)

private theorem cancel_two {a b : CReal}
    (h : CReal.Equiv (⟦(2 : Q')⟧ *ᶜ a) (⟦(2 : Q')⟧ *ᶜ b)) : CReal.Equiv a b := by
  intro epsilon he
  obtain ⟨N, hN⟩ := h (2*epsilon) (Q'.mul_pos (by decide) he)
  refine ⟨N, fun n hn => ?_⟩
  have hstep := hN n hn
  have expand : ∀ z : Q', 2*z+2*epsilon ≈ 2*(z+epsilon) :=
    fun z => Q'.eqv_symm (Q'.mul_add_eqv 2 z epsilon)
  exact ⟨Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ hstep.1 (Q'.le_of_eqv (expand _))) (by decide : (0 : Q') < 2),
    Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ hstep.2 (Q'.le_of_eqv (expand _))) (by decide : (0 : Q') < 2)⟩

/-- The actual cleared addition square at every fixed strict nome and every
rational x in the full interval. All value/frequency/product pins are produced
by the imported leaves; no analytic identity is supplied as a hypothesis. -/
theorem cleared_addition_square {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    let P := ThetaConvGen.thetaConvCRealGen hw0 hw1 hx0 hx1
    let P1 := ThetaConvGen.thetaConvCRealGen (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1)
    let D := JacobiProductRadialLimit.productRadialCostCReal hw0 hw1 hx0 hx1
    let D1 := JacobiProductRadialLimit.productRadialCostCReal (x := 1) hw0 hw1
      (by decide) (Q'.le_refl' 1)
    let A := alternatingCReal hw0 hw1 hx0 hx1
    let A1 := alternatingCReal (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1)
    CReal.Equiv ((P1 *ᶜ P1) *ᶜ ((D1 -ᶜ D) *ᶜ (P *ᶜ P)))
      (⟦2*w*(1 + -x)⟧ *ᶜ ((A *ᶜ A) *ᶜ (A1 *ᶜ A1))) := by
  dsimp only
  let V := valueRectangleCReal hw0 hw1 hx0 hx1
  let V1 := valueRectangleCReal (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1)
  let Q := frequencyRectangleCReal hw0 hw1 hx0 hx1
  let Q1 := frequencyRectangleCReal (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1)
  have valuePin : ∀ {y : Q'} (hy0 : (-1 : Q') ≤ y) (hy1 : y ≤ (1 : Q')),
      CReal.Equiv (valueRectangleCReal hw0 hw1 hy0 hy1)
        (ThetaConvGen.thetaConvCRealGen hw0 hw1 hy0 hy1 *ᶜ
          ThetaConvGen.thetaConvCRealGen hw0 hw1 hy0 hy1) := by
    intro y hy0 hy1
    exact CReal.Equiv.trans (completed_value_rectangle_pin hw0 hw1 hy0 hy1)
      (Pivot2.mul_congr (CReal.Equiv.symm (thetaProduct_eq_fullThetaSeries hw0 hw1 hy1 hy0))
        (CReal.Equiv.symm (thetaProduct_eq_fullThetaSeries hw0 hw1 hy1 hy0)))
  have frequencyPin : ∀ {y : Q'} (hy0 : (-1 : Q') ≤ y) (hy1 : y ≤ (1 : Q')),
      CReal.Equiv (frequencyRectangleCReal hw0 hw1 hy0 hy1)
        (⟦(2 : Q')⟧ *ᶜ ((ThetaConvGen.thetaConvCRealGen hw0 hw1 hy0 hy1 *ᶜ
          ThetaConvGen.thetaConvCRealGen hw0 hw1 hy0 hy1) *ᶜ
          JacobiProductRadialLimit.productRadialCostCReal hw0 hw1 hy0 hy1)) := by
    intro y hy0 hy1
    exact CReal.Equiv.trans (completed_frequency_rectangle_pin hw0 hw1 hy0 hy1)
      (ThetaProductRadialCompletedPin.frequencyNumerator_eq_productCost hw0 hw1 hy0 hy1)
  have hcost := CReal.Equiv.trans
    (sub_congr (Pivot2.mul_congr (valuePin hx0 hx1) (frequencyPin (by decide) (Q'.le_refl' 1)))
      (Pivot2.mul_congr (valuePin (by decide) (Q'.le_refl' 1)) (frequencyPin hx0 hx1)))
    (cost_factor _ _ _ _)
  have hdet : CReal.Equiv ((V *ᶜ Q1) -ᶜ (V1 *ᶜ Q))
      ((⟦(-4 : Q')⟧ *ᶜ ⟦w⟧) *ᶜ
        (mixedDeterminantCReal hw0 hw1 hx0 hx1 *ᶜ endpointDeterminantCReal hw0 hw1)) := by
    exact CReal.Equiv.trans
      (sub_congr
        (Pivot2.mul_congr (valueRectangle_eq_oneSided hw0 hw1 hx0 hx1)
          (frequencyRectangle_eq_oneSided hw0 hw1 (by decide) (Q'.le_refl' 1)))
        (Pivot2.mul_congr (valueRectangle_eq_oneSided hw0 hw1 (by decide) (Q'.le_refl' 1))
          (frequencyRectangle_eq_oneSided hw0 hw1 hx0 hx1)))
      (rectangle_determinant _ _ _ _ _ _ _)
  apply cancel_two
  exact CReal.Equiv.trans (CReal.Equiv.symm hcost)
    (CReal.Equiv.trans hdet
      (CReal.Equiv.trans
        (Pivot2.mul_congr_right (A := ⟦(-4 : Q')⟧ *ᶜ ⟦w⟧)
          (Pivot2.mul_congr (completed_alternating_square_pin hw0 hw1 hx0 hx1)
            (completed_endpoint_square_pin hw0 hw1)))
        (signed_factor w x _ _)))

end YMGap.Continuum.ThetaCompletedAdditionSquare

#print axioms YMGap.Continuum.ThetaCompletedAdditionSquare.valueRectangle_eq_oneSided
#print axioms YMGap.Continuum.ThetaCompletedAdditionSquare.frequencyRectangle_eq_oneSided
#print axioms YMGap.Continuum.ThetaCompletedAdditionSquare.cleared_addition_square
