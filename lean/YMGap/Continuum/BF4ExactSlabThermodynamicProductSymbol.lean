/-
# Constructed product symbols for the ORIGINAL continuous action

For arbitrary existing continuous F,G and their monotone vanishing data,
the product symbol, bound, oscillation modulus and monotone vanishing
selector are all constructed. The finite encoding does not presume that
F.omega or G.omega is monotone. Multiplication therefore has no additional
H-symbol-data premise. Its original action representative/rate are retained.

The action remains on represented original cyclic states at the fixed SU(2)
nome and spacing. Nonnegative square forms do not supply a strict physical
gap, a full-carrier spectral realization, or continuum/Clay closure.
-/

import YMGap.Continuum.UniformSymbolEncoding
import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder

namespace YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.UniformSymbolEncoding
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder

theorem product_bound (F G : CtsMod) (t : Q') : Q'.abs (F.f t*G.f t)≤F.bound*G.bound :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
    (Q'.mul_le_mul_of_nonneg (F.f_le t) (G.f_le t) (bound_nonneg F) (Q'.abs_nonneg _))

theorem productScalarTolerance_mono (F G : CtsMod) (a b : Q') (h : a≤b) :
    productScalarTolerance F G a≤productScalarTolerance F G b :=
  Q'.mul_le_mul_of_nonneg_right _ _ _ h (Q'.le_of_lt (Q'.recipPos_pos _ _))

def productInputDelta (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (e : Q') : Q' :=
  Q'.min' (V.delta (productScalarTolerance F G e)) (W.delta (productScalarTolerance F G e))

theorem productInputDelta_pos (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (e : Q') (he : (0 : Q')<e) :
    (0 : Q')<productInputDelta F V G W e :=
  UniformSymbolEncoding.min_pos (V.pos _ (productScalarTolerance_pos F G he))
    (W.pos _ (productScalarTolerance_pos F G he))

theorem productInputDelta_mono (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (a b : Q') (h : a≤b) :
    productInputDelta F V G W a≤productInputDelta F V G W b :=
  min_mono (V.mono _ _ (productScalarTolerance_mono F G a b h))
    (W.mono _ _ (productScalarTolerance_mono F G a b h))

theorem productInputDelta_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (e : Q') (he : (0 : Q')<e)
    (s t : Q') (h : Q'.abs (s-t)≤productInputDelta F V G W e) :
    Q'.abs (F.f s*G.f s - F.f t*G.f t)≤e := by
  have hd := productScalarTolerance_pos F G he
  have hF := Q'.le_trans' _ _ _ (F.mod s t _
    (Q'.le_trans' _ _ _ h (Q'.min_le_left' _ _))) (V.small _ hd)
  have hG := Q'.le_trans' _ _ _ (G.mod s t _
    (Q'.le_trans' _ _ _ h (Q'.min_le_right' _ _))) (W.small _ hd)
  exact Q'.le_trans' _ _ _
    (mul_difference_bound _ _ _ _ F.bound G.bound _ (bound_nonneg F) (bound_nonneg G)
      (F.f_le s) (G.f_le t) hG hF)
    (linearTolerance_budget _ (Q'.zero_le_add _ _ (bound_nonneg F) (bound_nonneg G)) he)

/-- Literal pointwise multiplication; bound F.bound*G.bound; all continuity data computed. -/
def productSymbol (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) : CtsMod :=
  encodedSymbol (fun t => F.f t*G.f t) (F.bound*G.bound)
    (Q'.mul_nonneg _ _ (bound_nonneg F) (bound_nonneg G)) (product_bound F G)
    (productInputDelta F V G W) (productInputDelta_bound F V G W)

def productVanishing (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) : MonotoneOmegaVanishing (productSymbol F V G W) :=
  encodedVanishing (fun t => F.f t*G.f t) (F.bound*G.bound)
    (Q'.mul_nonneg _ _ (bound_nonneg F) (bound_nonneg G)) (product_bound F G)
    (productInputDelta F V G W) (productInputDelta_bound F V G W)
    (productInputDelta_mono F V G W) (productInputDelta_pos F V G W)

theorem productSymbol_value (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (t : Q') :
    (productSymbol F V G W).f t=F.f t*G.f t := rfl

/-- No additional product-symbol package is supplied to this multiplication law. -/
theorem productSymbol_composition (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) :
    symbolAction (productSymbol F V G W) (productVanishing F V G W) X=
      symbolAction F V (actionPresentation G W X) :=
  symbolAction_mul F V G W _ _ (fun t _ _ => Q'.eqv_refl (F.f t*G.f t)) X

theorem productSymbol_pairing (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X Y : CyclicPresentation) :
    completedInner (symbolAction (productSymbol F V G W) (productVanishing F V G W) X) (state Y)=
      completedInner (symbolAction G W X) (symbolAction F V Y) := by
  rw [productSymbol_composition,symbolAction_symmetric,state_actionPresentation]

theorem productSquare_form_identity (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (X : CyclicPresentation) :
    completedInner (symbolAction (productSymbol F V F V) (productVanishing F V F V) X) (state X)=
      completedInner (symbolAction F V X) (symbolAction F V X) :=
  productSymbol_pairing F V F V X X

def productSymbolActionCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) :=
  symbolActionCertificate (productSymbol F V G W) (productVanishing F V G W) X

end YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.product_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productScalarTolerance_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productInputDelta
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productInputDelta_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productInputDelta_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productInputDelta_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productVanishing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productSymbol_value
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productSymbol_composition
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productSymbol_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productSquare_form_identity
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol.productSymbolActionCertificate
