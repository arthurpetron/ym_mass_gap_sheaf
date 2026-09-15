/-
# Symbol algebra and positive calculus on the FULL ORIGINAL carrier

The constructed sum, constant, scaled and difference symbols act as the
original completed operations on every original state. Nonnegative
Bernstein polynomials give nonnegative continuous quadratic forms;
differences give form order. Together with actual multiplication, square
forms yield sharp upper/lower interval norm bounds and uniform symbol
perturbation bounds, without a cyclic-density or spectral-model premise.

The lower-bound theorem transports a SUPPLIED rational interval bound;
it does not assert one for a physical gap symbol. All bounds concern the
fixed SU(2) nome and spacing. Physical-scale uniformity, continuum
reconstruction and the Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication
import YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra

namespace YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (completedInner_sub_left)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear (addRows addRows_pin rowLimit_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_zero_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound (polynomialForm_nonnegative)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder (bernsteinPoly_nonnegative)
open YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol (productSymbol productVanishing)
open YMGap.Continuum.BF4ExactSlabThermodynamicSumSymbol (sumSymbol sumVanishing bernsteinPoly_sumSymbol)
open YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra
  (constantSymbol constantVanishing scaledSymbol scaledVanishing differenceSymbol differenceVanishing differenceSymbol_value)

local notation "point" X => Quotient.mk seminorm.completionSetoid X

theorem polynomial_eval_congr (x : Completion) (p q : QPoly.Poly)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (QPoly.eval p t) (QPoly.eval q t)) :
    polynomialOperator p x=polynomialOperator q x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completed_eq_of_small
  intro epsilon he
  apply polynomial_close X p q epsilon he
  intro t ht h1
  have hd := Q'.le_of_lt (approximationTolerance_pos X he)
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (h t ht h1)) (Q'.add_le_self_of_nonneg _ _ hd),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (h t ht h1)) (Q'.add_le_self_of_nonneg _ _ hd)⟩

theorem sumSymbol_action (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (x : Completion) :
    continuousAction (sumSymbol F V G W) (sumVanishing F V G W) x=
      completedAdd (continuousAction F V x) (continuousAction G W x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h : continuousAction (sumSymbol F V G W) (sumVanishing F V G W) (point X)=
      rowLimit (addRows (symbolRows F V X) (symbolRows G W X)) := by
    apply rowLimit_independent
    intro n
    rw [symbolRows_pin,addRows_pin,symbolRows_pin,symbolRows_pin,← operator_add]
    exact polynomial_eval_congr (point X) _ _ (fun t _ _ => bernsteinPoly_sumSymbol F V G W n t)
  exact h.trans (rowLimit_add _ _)

theorem constantSymbol_action (c : Q') (x : Completion) :
    continuousAction (constantSymbol c) (constantVanishing c) x=completedSmul c x :=
  (continuousAction_eq_polynomial _ _ [c] (fun t _ _ => Q'.eqv_symm (eval_single c t)) x).trans
    (operator_constant c x)

theorem oneSymbol_action (x : Completion) :
    continuousAction (constantSymbol 1) (constantVanishing 1) x=x :=
  (constantSymbol_action 1 x).trans (completedSmul_one x)

theorem zeroSymbol_action (x : Completion) :
    continuousAction (constantSymbol 0) (constantVanishing 0) x=completedZero :=
  (constantSymbol_action 0 x).trans (completedSmul_zero x)

theorem scaledSymbol_action (c : Q') (F : CtsMod) (V : MonotoneOmegaVanishing F) (x : Completion) :
    continuousAction (scaledSymbol c F V) (scaledVanishing c F V) x=completedSmul c (continuousAction F V x) := by
  change continuousAction (productSymbol (constantSymbol c) (constantVanishing c) F V)
    (productVanishing (constantSymbol c) (constantVanishing c) F V) x=_
  rw [productSymbol_composition,constantSymbol_action]

theorem differenceSymbol_action (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (x : Completion) :
    continuousAction (differenceSymbol F V G W) (differenceVanishing F V G W) x=
      completedSub (continuousAction F V x) (continuousAction G W x) := by
  change continuousAction (sumSymbol F V (scaledSymbol (-1) G W) (scaledVanishing (-1) G W))
    (sumVanishing F V (scaledSymbol (-1) G W) (scaledVanishing (-1) G W)) x=_
  rw [sumSymbol_action,scaledSymbol_action]
  rfl

theorem le_of_sub_nonnegative (a b : RC) (h : RCnonneg (RCsub b a)) : RCle a b := by
  have hc : RCadd (RCsub b a) a=b := by
    refine Quotient.inductionOn₂ b a ?_
    intro B A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.sub_add_cancel_eqv (B.approx n) (A.approx n)))
  have hb := RCadd_le_add h (RCle_refl a)
  rw [rc_zero_add,hc] at hb
  exact hb

theorem continuousAction_form_nonnegative (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (hF : ∀ t : Q',(0 : Q')≤t → t≤1 → (0 : Q')≤F.f t) (x : Completion) :
    RCnonneg (completedInner (continuousAction F V x) x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h := rowLimit_pairing_nonnegative (symbolRows F V X) (constantRows X) (by
    intro n
    rw [symbolRows_pin,constantRows_pin,completedInner_symm]
    exact polynomialForm_nonnegative (point X) _ (bernsteinPoly_nonnegative F hF n))
  rw [rowLimit_constant] at h
  exact h

theorem continuousAction_form_mono (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G)
    (hfg : ∀ t : Q',(0 : Q')≤t → t≤1 → F.f t≤G.f t) (x : Completion) :
    RCle (completedInner (continuousAction F V x) x) (completedInner (continuousAction G W x) x) := by
  have h := continuousAction_form_nonnegative _ (differenceVanishing G W F V) (by
    intro t ht h1
    exact Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le (hfg t ht h1))
      (Q'.ge_of_eqv (differenceSymbol_value G W F V t))) x
  rw [differenceSymbol_action,completedInner_sub_left] at h
  exact le_of_sub_nonnegative _ _ h

/-- The interval bound, not the global presentation bound, controls the original norm. -/
theorem continuousAction_interval_norm_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (x : Completion) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (F.f t)≤M) :
    RCle (completedInner (continuousAction F V x) (continuousAction F V x))
      (RCscale (M*M) (completedInner x x)) := by
  have hp : ∀ t : Q',(0 : Q')≤t → t≤1 → (productSymbol F V F V).f t≤(constantSymbol (M*M)).f t := by
    intro t ht h1
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (abs_sq (F.f t)))
      (Q'.mul_le_mul_of_nonneg (h t ht h1) (h t ht h1) hM (Q'.abs_nonneg _))
  have hb := continuousAction_form_mono _ (productVanishing F V F V) _ (constantVanishing (M*M)) hp x
  rw [productSquare_form_identity,constantSymbol_action,completedInner_smul_left] at hb
  exact hb

/-- Conditional transfer of a supplied interval lower bound, NOT a physical gap assertion. -/
theorem continuousAction_interval_norm_lower (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (x : Completion) (m : Q') (hm : (0 : Q')≤m)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → m≤Q'.abs (F.f t)) :
    RCle (RCscale (m*m) (completedInner x x))
      (completedInner (continuousAction F V x) (continuousAction F V x)) := by
  have hp : ∀ t : Q',(0 : Q')≤t → t≤1 → (constantSymbol (m*m)).f t≤(productSymbol F V F V).f t := by
    intro t ht h1
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg (h t ht h1) (h t ht h1) (Q'.abs_nonneg _) hm)
      (Q'.le_of_eqv (abs_sq (F.f t)))
  have hb := continuousAction_form_mono _ (constantVanishing (m*m)) _ (productVanishing F V F V) hp x
  rw [productSquare_form_identity,constantSymbol_action,completedInner_smul_left] at hb
  exact hb

theorem continuousAction_interval_distance_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (x : Completion) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (F.f t-G.f t)≤M) :
    RCle (completedDist (continuousAction F V x) (continuousAction G W x))
      (RCscale (M*M) (completedInner x x)) := by
  have hb := continuousAction_interval_norm_bound _ (differenceVanishing F V G W) x M hM
    (fun t ht h1 => Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (differenceSymbol_value F V G W t))) (h t ht h1))
  rw [differenceSymbol_action] at hb
  exact hb

end YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.polynomial_eval_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.sumSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.constantSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.oneSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.zeroSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.scaledSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.differenceSymbol_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.le_of_sub_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.continuousAction_form_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.continuousAction_form_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.continuousAction_interval_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.continuousAction_interval_norm_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder.continuousAction_interval_distance_bound
