/-
# A fully supplied nonconstant product-symbol instance

The squared capped cusp has bound 1, continuity modulus 2*abs(delta),
and monotone vanishing selector epsilon/2. All symbol data are constructed.
Its action on every represented original cyclic state is exactly the
composition of the cusp action with itself, by the general product law.

Nonconstancy refers to the rational symbol, not to nonzeroness of its
action on a particular vector. No full-carrier or continuum gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication
open YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe

def cuspSquare (t : Q') : Q' := cusp t*cusp t

theorem cuspSquare_bound (t : Q') : Q'.abs (cuspSquare t)≤1 :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg (cusp_bound t) (cusp_bound t) Q'.zero_le_one (Q'.abs_nonneg _))
      (Q'.le_of_eqv (Q'.one_mul_eqv 1)))

theorem cuspSquare_modulus (s t delta : Q') (h : Q'.abs (s - t)≤delta) :
    Q'.abs (cuspSquare s - cuspSquare t)≤(1+1)*Q'.abs delta := by
  have hd : Q'.abs (cusp s + -cusp t)≤Q'.abs delta :=
    Q'.le_trans' _ _ _ (cusp_lipschitz s t) (Q'.le_trans' _ _ _ h (Q'.le_abs_self delta))
  exact mul_difference_bound _ _ _ _ 1 1 _ Q'.zero_le_one Q'.zero_le_one
    (cusp_bound s) (cusp_bound t) hd hd

def cuspSquareSymbol : CtsMod where
  f := cuspSquare
  bound := 1
  ω := fun delta => (1+1)*Q'.abs delta
  f_le := cuspSquare_bound
  ω_nn := fun delta => Q'.mul_nonneg _ _ (by decide) (Q'.abs_nonneg delta)
  mod := cuspSquare_modulus

def cuspSquareVanishing : MonotoneOmegaVanishing cuspSquareSymbol where
  delta := fun epsilon => HalfPow.half*epsilon
  mono := fun _ _ h => Q'.mul_le_mul_of_nonneg_left _ _ _ h (by decide)
  pos := ExpNeg.half_mul_pos
  small := by
    intro epsilon he
    change (1+1)*Q'.abs (HalfPow.half*epsilon)≤epsilon
    rw [abs_of_nonneg (Q'.le_of_lt (ExpNeg.half_mul_pos epsilon he))]
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)) (ExpNeg.two_halves epsilon)))

theorem cuspSquare_nonconstant : ¬Q'.eqv (cuspSquare 0) (cuspSquare HalfPow.half) := by decide

/-- All three symbol packages are supplied; the equality holds on every represented original cyclic input. -/
theorem cuspSquare_composition (X : CyclicPresentation) :
    symbolAction cuspSquareSymbol cuspSquareVanishing X=
      symbolAction cuspSymbol cuspVanishing (actionPresentation cuspSymbol cuspVanishing X) :=
  symbolAction_mul cuspSymbol cuspVanishing cuspSymbol cuspVanishing cuspSquareSymbol cuspSquareVanishing
    (fun t _ _ => Q'.eqv_refl (cuspSquare t)) X

def cuspSquareActionCertificate (X : CyclicPresentation) :=
  symbolActionCertificate cuspSquareSymbol cuspSquareVanishing X

end YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication.cuspSquare
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication.cuspSquare_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication.cuspSquare_modulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication.cuspSquareSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication.cuspSquareVanishing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication.cuspSquare_nonconstant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication.cuspSquare_composition
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication.cuspSquareActionCertificate
