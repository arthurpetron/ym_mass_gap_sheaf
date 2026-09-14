/-
# Constants, rational scaling and differences in the ORIGINAL calculus

Constant symbols have zero oscillation modulus and the identity vanishing
selector. Their actions are the original scalar operators. The constructed
product and sum symbols then supply scaling and subtraction, including
their complete continuity data and exact original-action identities.

Together with the earlier multiplication and input-linearity theorems,
these are algebra laws on represented original cyclic states, not a
replacement carrier or a full-carrier spectral/continuum construction.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol

namespace YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure
open YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol
open YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol

def constantSymbol (c : Q') : CtsMod where
  f := fun _ => c
  bound := Q'.abs c
  ω := fun _ => 0
  f_le := fun _ => Q'.le_refl' _
  ω_nn := fun _ => Q'.le_refl' _
  mod := fun _ _ _ _ => Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_neg_self_eqv c))) (by decide)

def constantVanishing (c : Q') : MonotoneOmegaVanishing (constantSymbol c) where
  delta := fun e => e
  mono := fun _ _ h => h
  pos := fun _ h => h
  small := fun _ h => Q'.le_of_lt h

theorem constantSymbol_action (c : Q') (X : CyclicPresentation) :
    symbolAction (constantSymbol c) (constantVanishing c) X=completedSmul c (state X) :=
  (symbolAction_eq_polynomial _ _ X [c] (fun t _ _ => Q'.eqv_symm (eval_single c t))).trans
    (operator_constant c (state X))

theorem oneSymbol_action (X : CyclicPresentation) :
    symbolAction (constantSymbol 1) (constantVanishing 1) X=state X :=
  (constantSymbol_action 1 X).trans (completedSmul_one _)

theorem zeroSymbol_action (X : CyclicPresentation) :
    symbolAction (constantSymbol 0) (constantVanishing 0) X=completedZero :=
  (constantSymbol_action 0 X).trans (completedSmul_zero _)

def scaledSymbol (c : Q') (F : CtsMod) (V : MonotoneOmegaVanishing F) : CtsMod :=
  productSymbol (constantSymbol c) (constantVanishing c) F V

def scaledVanishing (c : Q') (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    MonotoneOmegaVanishing (scaledSymbol c F V) :=
  productVanishing (constantSymbol c) (constantVanishing c) F V

theorem scaledSymbol_value (c : Q') (F : CtsMod) (V : MonotoneOmegaVanishing F) (t : Q') :
    (scaledSymbol c F V).f t=c*F.f t := rfl

theorem scaledSymbol_action (c : Q') (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (X : CyclicPresentation) :
    symbolAction (scaledSymbol c F V) (scaledVanishing c F V) X=completedSmul c (symbolAction F V X) := by
  change symbolAction (productSymbol (constantSymbol c) (constantVanishing c) F V)
    (productVanishing (constantSymbol c) (constantVanishing c) F V) X=_
  rw [productSymbol_composition,constantSymbol_action,state_actionPresentation]

def differenceSymbol (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) : CtsMod :=
  sumSymbol F V (scaledSymbol (-1) G W) (scaledVanishing (-1) G W)

def differenceVanishing (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) : MonotoneOmegaVanishing (differenceSymbol F V G W) :=
  sumVanishing F V (scaledSymbol (-1) G W) (scaledVanishing (-1) G W)

theorem differenceSymbol_value (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (t : Q') :
    Q'.eqv ((differenceSymbol F V G W).f t) (F.f t-G.f t) :=
  Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (G.f t))
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (G.f t))))

theorem differenceSymbol_action (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) :
    symbolAction (differenceSymbol F V G W) (differenceVanishing F V G W) X=
      completedSub (symbolAction F V X) (symbolAction G W X) := by
  change symbolAction (sumSymbol F V (scaledSymbol (-1) G W) (scaledVanishing (-1) G W))
    (sumVanishing F V (scaledSymbol (-1) G W) (scaledVanishing (-1) G W)) X=_
  rw [sumSymbol_action,scaledSymbol_action]
  rfl

def differenceSymbolActionCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) :=
  symbolActionCertificate (differenceSymbol F V G W) (differenceVanishing F V G W) X

end YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.constantSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.constantVanishing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.constantSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.oneSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.zeroSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.scaledSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.scaledVanishing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.scaledSymbol_value
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.scaledSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.differenceSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.differenceVanishing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.differenceSymbol_value
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.differenceSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra.differenceSymbolActionCertificate
