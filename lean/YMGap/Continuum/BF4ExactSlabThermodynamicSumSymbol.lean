/-
# Constructed sums and addition of ORIGINAL continuous actions

The bounded symbol F+G and its continuity data are constructed from F,G.
The common input selector takes the minimum of the two selectors at half
the output tolerance. UniformSymbolEncoding supplies the oscillation data
without assuming monotonicity of either original oscillation function.

Finite Bernstein sums preserve addition exactly in rational equivalence.
This gives (F+G)(T2)x = F(T2)x + G(T2)x by the original represented row
limits. No new physical input or alternative operator model is supplied.
Fixed SU(2) nome and spacing; the continuum/Clay target remains open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol

namespace YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.UniformSymbolEncoding
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication

theorem sum_difference (a b c d : Q') : Q'.eqv ((a+b)-(c+d)) ((a-c)+(b-d)) :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_eqv c d))
    (Q'.add_regroup a b (-c) (-d))

theorem sum_bound (F G : CtsMod) (t : Q') : Q'.abs (F.f t+G.f t)≤F.bound+G.bound :=
  Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.add_le_add (F.f_le t) (G.f_le t))

def sumInputDelta (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (e : Q') : Q' :=
  Q'.min' (V.delta (HalfPow.half*e)) (W.delta (HalfPow.half*e))

theorem sumInputDelta_pos (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (e : Q') (he : (0 : Q')<e) :
    (0 : Q')<sumInputDelta F V G W e :=
  UniformSymbolEncoding.min_pos (V.pos _ (ExpNeg.half_mul_pos e he)) (W.pos _ (ExpNeg.half_mul_pos e he))

theorem sumInputDelta_mono (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (a b : Q') (h : a≤b) :
    sumInputDelta F V G W a≤sumInputDelta F V G W b := by
  have hh := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half h (by decide)
  exact min_mono (V.mono _ _ hh) (W.mono _ _ hh)

theorem sumInputDelta_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (e : Q') (he : (0 : Q')<e)
    (s t : Q') (h : Q'.abs (s-t)≤sumInputDelta F V G W e) :
    Q'.abs ((F.f s+G.f s)-(F.f t+G.f t))≤e := by
  have hd := ExpNeg.half_mul_pos e he
  have hF := Q'.le_trans' _ _ _ (F.mod s t _
    (Q'.le_trans' _ _ _ h (Q'.min_le_left' _ _))) (V.small _ hd)
  have hG := Q'.le_trans' _ _ _ (G.mod s t _
    (Q'.le_trans' _ _ _ h (Q'.min_le_right' _ _))) (W.small _ hd)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (sum_difference _ _ _ _)))
    (Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hF hG) (Q'.le_of_eqv (ExpNeg.two_halves e))))

def sumSymbol (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) : CtsMod :=
  encodedSymbol (fun t => F.f t+G.f t) (F.bound+G.bound)
    (Q'.zero_le_add _ _ (bound_nonneg F) (bound_nonneg G)) (sum_bound F G)
    (sumInputDelta F V G W) (sumInputDelta_bound F V G W)

def sumVanishing (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) : MonotoneOmegaVanishing (sumSymbol F V G W) :=
  encodedVanishing (fun t => F.f t+G.f t) (F.bound+G.bound)
    (Q'.zero_le_add _ _ (bound_nonneg F) (bound_nonneg G)) (sum_bound F G)
    (sumInputDelta F V G W) (sumInputDelta_bound F V G W)
    (sumInputDelta_mono F V G W) (sumInputDelta_pos F V G W)

theorem sumSymbol_value (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (t : Q') :
    (sumSymbol F V G W).f t=F.f t+G.f t := rfl

theorem bernstein_sumSymbol (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (n : Nat) (t : Q') :
    Q'.eqv (bernstein (sumSymbol F V G W) n t) (bernstein F n t+bernstein G n t) :=
  Q'.eqv_trans _ _ _ (finSum_eqv_congr _ _
    (fun k => Q'.add_mul_eqv (F.f (smp n k)) (G.f (smp n k)) _) (n+1))
    (finSum_add _ _ (n+1))

theorem bernsteinPoly_sumSymbol (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (n : Nat) (t : Q') :
    Q'.eqv (QPoly.eval (bernsteinPoly (sumSymbol F V G W) n) t)
      (QPoly.eval (QPoly.padd (bernsteinPoly F n) (bernsteinPoly G n)) t) :=
  Q'.eqv_trans _ _ _ (eval_bernsteinPoly _ n t)
    (Q'.eqv_trans _ _ _ (bernstein_sumSymbol F V G W n t)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_eqv_congr' (eval_bernsteinPoly F n t) (eval_bernsteinPoly G n t)))
        (Q'.eqv_symm (QPoly.eval_padd _ _ t))))

theorem sumSymbol_action (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) :
    symbolAction (sumSymbol F V G W) (sumVanishing F V G W) X=
      completedAdd (symbolAction F V X) (symbolAction G W X) := by
  have h : symbolAction (sumSymbol F V G W) (sumVanishing F V G W) X=
      rowLimit (addRows (symbolRows F V X) (symbolRows G W X)) := by
    apply rowLimit_independent
    intro n
    rw [symbolRows_pin,addRows_pin,symbolRows_pin,symbolRows_pin,← operator_add]
    exact polynomial_eval_congr X _ _ (fun t _ _ => bernsteinPoly_sumSymbol F V G W n t)
  exact h.trans (rowLimit_add _ _)

def sumSymbolActionCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) :=
  symbolActionCertificate (sumSymbol F V G W) (sumVanishing F V G W) X

end YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sum_difference
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sum_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sumInputDelta
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sumInputDelta_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sumInputDelta_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sumInputDelta_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sumSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sumVanishing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sumSymbol_value
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.bernstein_sumSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.bernsteinPoly_sumSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sumSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol.sumSymbolActionCertificate
