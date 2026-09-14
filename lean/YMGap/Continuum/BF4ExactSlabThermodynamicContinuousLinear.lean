/-
# Bounded linear continuous action on the represented ORIGINAL cyclic sector

Original polynomial linearity passes through the constructed row limits.
The action preserves rational sums, scaling and differences of represented
cyclic states. Its sharp norm bound therefore gives the relative squared
distance bound F.bound^2*d(x,y), with explicit input tolerance
epsilon/(F.bound^2+1). Together with the constructed output presentation,
this supplies composable continuous actions on the SAME original states.

No linearity or image-limit premise is supplied. Multiplication of symbols,
full-carrier spectral realization, physical-scale uniformity and continuum
Yang--Mills remain subsequent obligations; nome and spacing stay fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure
import YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear
import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility

namespace YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem symbolAction_add (F : CtsMod) (V : MonotoneOmegaVanishing F) (X Y : CyclicPresentation) :
    symbolAction F V (addPresentation X Y)=completedAdd (symbolAction F V X) (symbolAction F V Y) := by
  have h : symbolAction F V (addPresentation X Y)=rowLimit (addRows (symbolRows F V X) (symbolRows F V Y)) := by
    apply rowLimit_independent
    intro n
    simp only [symbolRows_pin,addRows_pin,state_addPresentation]
    exact vector_base_add _ _ _ _
  exact h.trans (rowLimit_add _ _)

theorem symbolAction_smul (F : CtsMod) (V : MonotoneOmegaVanishing F) (c : Q') (X : CyclicPresentation) :
    symbolAction F V (smulPresentation c X)=completedSmul c (symbolAction F V X) := by
  have h : symbolAction F V (smulPresentation c X)=rowLimit (operatorRows [c] (symbolRows F V X)) := by
    apply rowLimit_independent
    intro n
    simp only [symbolRows_pin,operatorRows_pin,state_smulPresentation,operator_constant]
    exact vector_base_smul _ _ _ _
  exact h.trans ((operator_rowLimit _ _).trans (operator_constant _ _))

theorem symbolAction_sub (F : CtsMod) (V : MonotoneOmegaVanishing F) (X Y : CyclicPresentation) :
    symbolAction F V (subPresentation X Y)=completedSub (symbolAction F V X) (symbolAction F V Y) := by
  rw [subPresentation,symbolAction_add,symbolAction_smul]
  rfl

/-- A relative distance estimate on the SAME original carrier, independent of presentation norm ceilings. -/
theorem symbolAction_distance_bound (F : CtsMod) (V : MonotoneOmegaVanishing F) (X Y : CyclicPresentation) :
    RCle (completedDist (symbolAction F V X) (symbolAction F V Y))
      (RCscale (F.bound*F.bound) (completedDist (state X) (state Y))) := by
  have h := symbolAction_norm_bound F V (subPresentation X Y)
  rw [symbolAction_sub,state_subPresentation] at h
  exact h

def inputTolerance (F : CtsMod) (epsilon : Q') : Q' :=
  linearTolerance (F.bound*F.bound) (SumOfSquares.q_mul_self_nonneg F.bound) epsilon

theorem inputTolerance_pos (F : CtsMod) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (0 : Q')<inputTolerance F epsilon := linearTolerance_pos _ _ he

theorem symbolAction_close (F : CtsMod) (V : MonotoneOmegaVanishing F) (X Y : CyclicPresentation)
    (epsilon : Q') (he : (0 : Q')<epsilon)
    (h : RCle (completedDist (state X) (state Y)) (rat (inputTolerance F epsilon))) :
    RCle (completedDist (symbolAction F V X) (symbolAction F V Y)) (rat epsilon) :=
  RCle_trans (symbolAction_distance_bound F V X Y) (RCle_trans
    (RCscale_mono (SumOfSquares.q_mul_self_nonneg F.bound) h)
    (leEv_le_ofQ'_of_approx_le (fun _ => linearTolerance_budget _ (SumOfSquares.q_mul_self_nonneg F.bound) he)))

theorem actionPresentation_congr (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X Y : CyclicPresentation)
    (hxy : state X=state Y) (hfg : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (F.f t) (G.f t)) :
    state (actionPresentation F V X)=state (actionPresentation G W Y) := by
  rw [state_actionPresentation,state_actionPresentation]
  exact symbolAction_congr F V G W X Y hxy hfg

theorem actionPresentation_add (F : CtsMod) (V : MonotoneOmegaVanishing F) (X Y : CyclicPresentation) :
    state (actionPresentation F V (addPresentation X Y))=
      completedAdd (state (actionPresentation F V X)) (state (actionPresentation F V Y)) := by
  simp only [state_actionPresentation,symbolAction_add]

theorem actionPresentation_smul (F : CtsMod) (V : MonotoneOmegaVanishing F) (c : Q') (X : CyclicPresentation) :
    state (actionPresentation F V (smulPresentation c X))=completedSmul c (state (actionPresentation F V X)) := by
  simp only [state_actionPresentation,symbolAction_smul]

/-- Composition is constructed and norm-controlled; this is not yet the symbol multiplication identity. -/
theorem composition_norm_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) :
    RCle (completedInner (state (actionPresentation F V (actionPresentation G W X)))
        (state (actionPresentation F V (actionPresentation G W X))))
      (RCscale (F.bound*F.bound) (RCscale (G.bound*G.bound) (completedInner (state X) (state X)))) := by
  rw [state_actionPresentation]
  have h := symbolAction_norm_bound F V (actionPresentation G W X)
  rw [state_actionPresentation] at h
  exact RCle_trans h (RCscale_mono (SumOfSquares.q_mul_self_nonneg F.bound) (symbolAction_norm_bound G W X))

end YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.symbolAction_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.symbolAction_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.symbolAction_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.symbolAction_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.inputTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.inputTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.symbolAction_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.actionPresentation_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.actionPresentation_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.actionPresentation_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear.composition_norm_bound
