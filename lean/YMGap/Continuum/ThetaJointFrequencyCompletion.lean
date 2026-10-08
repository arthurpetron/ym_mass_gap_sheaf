/-
# Completion of the actual signed theta-box frequency numerator

The value, first-series and angular-series completions are constructed
separately. Finite formal jet pins and the exact signed frequency identity
identify EVERY approximant of their cleared numerator with the original
box sum. No derivative of a value limit, finite Euler-product substitution,
positivity or completed Jacobi radial-cost identification is assumed.
Arithmetic uses the existing constructive CReal operations and their Cauchy
proofs. This is a fixed-nome scalar completion, not a physical gap estimate.
-/

import YMGap.Continuum.ThetaJointFrequencyNumerator
import YMGap.Continuum.ThetaBareAngularCompletion
import YMGap.Continuum.JacobiTripleProductOnBox

namespace YMGap.Continuum.ThetaJointFrequencyCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation (coefficient_eval)
open YMGap.Continuum.FiniteJacobiAngularComparison (seriesPoly eval_seriesPoly)
open YMGap.Continuum.FiniteSymmetricChebyshevDerivative (dsum)
open YMGap.Continuum.ChebyshevFormalJets (eval_Tpoly_derivative)
open YMGap.Continuum.FiniteJacobiDerivativeComparison (dsum_bare_eq_two_dPartial)
open YMGap.Continuum.ThetaJointAngularPin (barePolynomial)
open YMGap.Continuum.ThetaJointFrequencyNumerator (frequency_box_numerator_pin)
open YMGap.Continuum.ThetaBareAngularCompletion
open YMGap.Continuum.JacobiTripleProductOnBox
open YMGap.Continuum.ThetaParityConvolution (boxIndices)
open YMGap.Continuum.ThetaParityWeights (frequencyCell)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ g)

private theorem first_seriesPoly_pin (a : Nat → Q') (x : Q') : ∀ N,
    eval (pderiv (seriesPoly a N)) x ≈ dsum a x N
  | 0 => Q'.eqv_refl 0
  | N+1 => Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_padd _ _) x)
      (Q'.eqv_trans _ _ _ (eval_padd _ _ x)
        (Q'.add_eqv_congr' (first_seriesPoly_pin a x N)
          (Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_pscale _ _) x)
            (Q'.eqv_trans _ _ _ (eval_pscale _ _ x)
              (Q'.mul_eqv_congr_left _ _ _ (eval_Tpoly_derivative (N+1) x))))))

/-- Actual formal first jet, including the essential factor two. -/
theorem bare_first_jet_pin (w x : Q') (N : Nat) :
    eval (pderiv (barePolynomial w N)) x ≈ 2*JTPIdentity.dPartial w x N :=
  Q'.eqv_trans _ _ _ (first_seriesPoly_pin (fun j => w^(j*j)) x N)
    (dsum_bare_eq_two_dPartial w x N)

/-- Constructed first-series completion, not a derivative of a value limit. -/
def bareFirstCReal {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  CReal.mul (CReal.ofQ' 2) (JTPIdentity.dSeriesCReal hw0 hw1 hx0 hx1)

theorem bareFirstCReal_formal_pin {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (bareFirstCReal hw0 hw1 hx0 hx1).approx N ≈
      eval (pderiv (barePolynomial w N)) x := Q'.eqv_symm (bare_first_jet_pin w x N)

/-- SAME signed frequency numerator, assembled from separately constructed
actual series completions. Its approximants are pinned to the literal box. -/
def frequencyNumeratorCReal {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  CReal.mul (CReal.ofQ' 2)
    (CReal.add
      (CReal.mul (CReal.ofQ' (1 + -(x*x)))
        (CReal.mul (bareFirstCReal hw0 hw1 hx0 hx1) (bareFirstCReal hw0 hw1 hx0 hx1)))
      (CReal.neg
        (CReal.mul (fullThetaSeries hw0 hw1 hx1 hx0) (bareAngularCReal hw0 hw1 hx0 hx1))))

/-- EVERY approximation is the actual signed frequency-box sum, modulo
rational equivalence. No box-limit or same-series pin is supplied. -/
theorem frequencyNumeratorCReal_box_pin {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (frequencyNumeratorCReal hw0 hw1 hx0 hx1).approx N ≈
      listQSum (frequencyCell w x) (boxIndices N) := by
  have hv : (fullThetaSeries hw0 hw1 hx1 hx0).approx N ≈ eval (barePolynomial w N) x :=
    Q'.eqv_trans _ _ _ (fullThetaSeries_approx hw0 hw1 hx1 hx0 N)
      (Q'.eqv_symm (eval_seriesPoly (fun j => w^(j*j)) x N))
  have hd := bareFirstCReal_formal_pin hw0 hw1 hx0 hx1 N
  have ha := bareAngularCReal_formal_pin hw0 hw1 hx0 hx1 N
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left 2 _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (1 + -(x*x)) _ _ (mul_congr hd hd))
        (Q'.neg_eqv_congr _ _ (mul_congr hv ha))))
    (Q'.eqv_symm (frequency_box_numerator_pin w x N))

end YMGap.Continuum.ThetaJointFrequencyCompletion

#print axioms YMGap.Continuum.ThetaJointFrequencyCompletion.bare_first_jet_pin
#print axioms YMGap.Continuum.ThetaJointFrequencyCompletion.bareFirstCReal
#print axioms YMGap.Continuum.ThetaJointFrequencyCompletion.bareFirstCReal_formal_pin
#print axioms YMGap.Continuum.ThetaJointFrequencyCompletion.frequencyNumeratorCReal
#print axioms YMGap.Continuum.ThetaJointFrequencyCompletion.frequencyNumeratorCReal_box_pin
