/-
# The signed theta numerator meets the SAME original product radial cost

The original product value, first jet and angular jet are completed separately.
The existing quantitative finite comparisons join them to the separately
completed bare theta series. The finite SAME-product numerator identity then
identifies the signed frequency numerator with 2*P^2*D, where D is the existing
completion of the literal product radial costs. No derivative of a value limit,
finite Euler/bare substitution, positive division or analytic identity premise
is used. The comparison cutoff is uniform in x at each fixed strict nome only.

This scalar identity does not itself prove the completed addition square,
whole-interval cost ceiling, original-action bound or physical mass gap.
-/

import YMGap.Continuum.ThetaProductAngularCompletion
import YMGap.Continuum.ThetaJointFrequencyCompletion
import YMGap.Continuum.JacobiProductRadialLimit
import YMGap.Continuum.Pivot2Moments

namespace YMGap.Continuum.ThetaProductRadialCompletedPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative (pderiv)
open YMGap.Continuum.ThetaProductAngularCompletion
open YMGap.Continuum.ThetaJointFrequencyCompletion
open YMGap.Continuum.JacobiProductRadialLimit
open YMGap.Continuum.FiniteJacobiAngularComparison (productRadialNumerator productRadialNumerator_pin)
open YMGap.Continuum.FiniteJacobiDerivativeComparison (derivativeCutoff fullProdDx_sub_two_dPartial_close)
open YMGap.Continuum.JTPFullProductDerivativeNormalization (fullProdDx_eqv_Ppart_mul_Spart)
open YMGap.Continuum.JacobiHeatRadialMomentJets (product_first_moment_pin)
open YMGap.Continuum.JacobiTripleProductOnBox (thetaProduct_eq_fullThetaSeries)

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ g)

/-- The existing completion of the original product first jets, unhalved. -/
def productFirstCReal {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  JTPIdentity.Rproduct hw0 hw1 hx0 hx1

/-- EVERY approximant is the actual first formal product jet, modulo Q' equivalence. -/
theorem productFirstCReal_formal_pin {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (productFirstCReal hw0 hw1 hx0 hx1).approx N ≈
      eval (pderiv (JacobiShiftedPositiveCoefficients.product w N)) (1+x) :=
  Q'.eqv_symm (product_first_moment_pin hw0 hw1 hx0 N)

/-- Explicit first-jet comparison cutoff, independent of x at each fixed nome. -/
def productFirstEquivCutoff (w epsilon : Q') : Nat := derivativeCutoff w epsilon

theorem productFirstCReal_equiv_close {w x epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (he : (0 : Q') < epsilon) (N : Nat) (hN : productFirstEquivCutoff w epsilon ≤ N) :
    Q'.abs ((productFirstCReal hw0 hw1 hx0 hx1).approx N +
      -(bareFirstCReal hw0 hw1 hx0 hx1).approx N) ≤ epsilon := by
  have hp := Q'.eqv_symm (fullProdDx_eqv_Ppart_mul_Spart hw0 hw1 hx0 N)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr
      (Q'.add_eqv_congr' hp (Q'.eqv_refl (-(2*JTPIdentity.dPartial w x N))))))
    (fullProdDx_sub_two_dPartial_close hw0 hw1 hx1 hx0 he N hN)

/-- Actual unhalved product first completion equals the actual 2*dSeries completion. -/
theorem productFirstCReal_eq_bare {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (productFirstCReal hw0 hw1 hx0 hx1) (bareFirstCReal hw0 hw1 hx0 hx1) := by
  apply CReal.Equiv_of_abs_sub_le_all_pos
  intro epsilon he
  apply CReal.leRat_of_eventually
  exact ⟨productFirstEquivCutoff w epsilon,
    fun N hN => productFirstCReal_equiv_close hw0 hw1 hx0 hx1 he N hN⟩

/-- Constructed numerator on the original product completions, with the factor two. -/
def productFrequencyNumeratorCReal {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  CReal.mul (CReal.ofQ' 2)
    (CReal.add
      (CReal.mul (CReal.ofQ' (1 + -(x*x)))
        (CReal.mul (productFirstCReal hw0 hw1 hx0 hx1) (productFirstCReal hw0 hw1 hx0 hx1)))
      (CReal.neg
        (CReal.mul (ThetaConvGen.thetaConvCRealGen hw0 hw1 hx0 hx1)
          (productAngularCReal hw0 hw1 hx0 hx1))))

/-- EVERY numerator approximant is twice the actual finite product radial numerator. -/
theorem productFrequencyNumeratorCReal_formal_pin {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (productFrequencyNumeratorCReal hw0 hw1 hx0 hx1).approx N ≈
      2*productRadialNumerator w x N := by
  have hd := productFirstCReal_formal_pin hw0 hw1 hx0 hx1 N
  exact Q'.mul_eqv_congr_left 2 _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (1 + -(x*x)) _ _ (qmul_congr hd hd))
      (Q'.eqv_refl _))

/-- The literal finite numerator pin contracts on the SAME constructed radial-cost limit. -/
theorem productFrequencyNumerator_eq_productCost {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (productFrequencyNumeratorCReal hw0 hw1 hx0 hx1)
      (CReal.mul (CReal.ofQ' 2)
        (CReal.mul
          (CReal.mul (ThetaConvGen.thetaConvCRealGen hw0 hw1 hx0 hx1)
            (ThetaConvGen.thetaConvCRealGen hw0 hw1 hx0 hx1))
          (productRadialCostCReal hw0 hw1 hx0 hx1))) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro N
  exact Q'.eqv_trans _ _ _ (productFrequencyNumeratorCReal_formal_pin hw0 hw1 hx0 hx1 N)
    (Q'.mul_eqv_congr_left 2 _ _ (productRadialNumerator_pin hw0 hw1 hx0 N))

/-- Actual value/first/angular finite comparisons identify the two completed numerators. -/
theorem productFrequencyNumerator_eq_bare {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (productFrequencyNumeratorCReal hw0 hw1 hx0 hx1)
      (frequencyNumeratorCReal hw0 hw1 hx0 hx1) := by
  have hd := productFirstCReal_eq_bare hw0 hw1 hx0 hx1
  have hv := thetaProduct_eq_fullThetaSeries hw0 hw1 hx1 hx0
  have ha := productAngularCReal_eq_bare hw0 hw1 hx0 hx1
  exact Pivot2.mul_congr (JTPIdentity.Equiv_refl _)
    (CReal.Equiv.trans
      (CReal.add_congr_left (Pivot2.mul_congr (JTPIdentity.Equiv_refl _) (Pivot2.mul_congr hd hd)))
      (CReal.add_congr_right (CReal.neg_congr (Pivot2.mul_congr hv ha))))

/-- Produced SAME-object pin from the original signed theta numerator to 2*P^2*D. -/
theorem frequencyNumerator_eq_productCost {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (frequencyNumeratorCReal hw0 hw1 hx0 hx1)
      (CReal.mul (CReal.ofQ' 2)
        (CReal.mul
          (CReal.mul (ThetaConvGen.thetaConvCRealGen hw0 hw1 hx0 hx1)
            (ThetaConvGen.thetaConvCRealGen hw0 hw1 hx0 hx1))
          (productRadialCostCReal hw0 hw1 hx0 hx1))) :=
  CReal.Equiv.trans (CReal.Equiv.symm (productFrequencyNumerator_eq_bare hw0 hw1 hx0 hx1))
    (productFrequencyNumerator_eq_productCost hw0 hw1 hx0 hx1)

end YMGap.Continuum.ThetaProductRadialCompletedPin

#print axioms YMGap.Continuum.ThetaProductRadialCompletedPin.productFirstCReal
#print axioms YMGap.Continuum.ThetaProductRadialCompletedPin.productFirstCReal_formal_pin
#print axioms YMGap.Continuum.ThetaProductRadialCompletedPin.productFirstEquivCutoff
#print axioms YMGap.Continuum.ThetaProductRadialCompletedPin.productFirstCReal_equiv_close
#print axioms YMGap.Continuum.ThetaProductRadialCompletedPin.productFirstCReal_eq_bare
#print axioms YMGap.Continuum.ThetaProductRadialCompletedPin.productFrequencyNumeratorCReal
#print axioms YMGap.Continuum.ThetaProductRadialCompletedPin.productFrequencyNumeratorCReal_formal_pin
#print axioms YMGap.Continuum.ThetaProductRadialCompletedPin.productFrequencyNumerator_eq_productCost
#print axioms YMGap.Continuum.ThetaProductRadialCompletedPin.productFrequencyNumerator_eq_bare
#print axioms YMGap.Continuum.ThetaProductRadialCompletedPin.frequencyNumerator_eq_productCost
