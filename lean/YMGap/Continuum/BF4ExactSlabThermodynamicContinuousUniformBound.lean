/-
# Sharp interval bounds and uniform perturbations of ORIGINAL actions

Square-form identities and form order give upper and lower squared-norm
bounds using only rational values on [0,1], not global presentation bounds.
The constructed difference symbol gives the sharp relative bound
  ||F(T2)x-G(T2)x||^2 <= M^2 ||x||^2
when |F-G| <= M on that interval. All actions are on the SAME represented
original cyclic input.

The existing explicit norm cap converts this to an absolute squared-error
tolerance. An interval-uniform symbol convergence rate is transported to
an original action convergence rate, retaining the target representative.
This is fixed-nome/spacing functional calculus, not a beta/spacing-uniform
physical mass gap or full-carrier/continuum construction.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra

namespace YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUniformBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol
open YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem symbolAction_interval_norm_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (X : CyclicPresentation) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (F.f t)≤M) :
    RCle (completedInner (symbolAction F V X) (symbolAction F V X))
      (RCscale (M*M) (completedInner (state X) (state X))) := by
  have hp : ∀ t : Q',(0 : Q')≤t → t≤1 → (productSymbol F V F V).f t≤(constantSymbol (M*M)).f t := by
    intro t ht h1
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (abs_sq (F.f t)))
      (Q'.mul_le_mul_of_nonneg (h t ht h1) (h t ht h1) hM (Q'.abs_nonneg _))
  have hb := symbolAction_form_mono _ (productVanishing F V F V) _ (constantVanishing (M*M)) hp X
  rw [productSquare_form_identity,constantSymbol_action,completedInner_smul_left] at hb
  exact hb

/-- This transports a supplied interval lower bound; it does not assert such a bound for a physical gap symbol. -/
theorem symbolAction_interval_norm_lower (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (X : CyclicPresentation) (m : Q') (hm : (0 : Q')≤m)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → m≤Q'.abs (F.f t)) :
    RCle (RCscale (m*m) (completedInner (state X) (state X)))
      (completedInner (symbolAction F V X) (symbolAction F V X)) := by
  have hp : ∀ t : Q',(0 : Q')≤t → t≤1 → (constantSymbol (m*m)).f t≤(productSymbol F V F V).f t := by
    intro t ht h1
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg (h t ht h1) (h t ht h1) (Q'.abs_nonneg _) hm)
      (Q'.le_of_eqv (abs_sq (F.f t)))
  have hb := symbolAction_form_mono _ (constantVanishing (m*m)) _ (productVanishing F V F V) hp X
  rw [productSquare_form_identity,constantSymbol_action,completedInner_smul_left] at hb
  exact hb

theorem symbolAction_interval_distance_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (F.f t-G.f t)≤M) :
    RCle (completedDist (symbolAction F V X) (symbolAction G W X))
      (RCscale (M*M) (completedInner (state X) (state X))) := by
  have hb := symbolAction_interval_norm_bound _ (differenceVanishing F V G W) X M hM
    (fun t ht h1 => Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (differenceSymbol_value F V G W t))) (h t ht h1))
  rw [differenceSymbol_action] at hb
  exact hb

theorem symbolAction_uniform_close (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation)
    (epsilon : Q') (he : (0 : Q')<epsilon)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (F.f t-G.f t)≤approximationTolerance X epsilon) :
    RCle (completedDist (symbolAction F V X) (symbolAction G W X)) (rat epsilon) := by
  have hb := symbolAction_interval_distance_bound F V G W X _ (Q'.le_of_lt (approximationTolerance_pos X he)) h
  exact RCle_trans hb (RCle_trans
    (RCscale_mono (SumOfSquares.q_mul_self_nonneg _) (state_norm_le_cap X))
    (leEv_le_ofQ'_of_approx_le (fun _ => approximationTolerance_budget X he)))

/-- One computed tolerance works for every admissible pair of symbols on this input. -/
def uniformComparisonCertificate (X : CyclicPresentation) (epsilon : Q') (he : (0 : Q')<epsilon) :
    {d : Q' // (0 : Q')<d ∧ ∀ (F : CtsMod) (V : MonotoneOmegaVanishing F)
      (G : CtsMod) (W : MonotoneOmegaVanishing G),
      (∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (F.f t-G.f t)≤d) →
      RCle (completedDist (symbolAction F V X) (symbolAction G W X)) (rat epsilon)} :=
  ⟨approximationTolerance X epsilon,approximationTolerance_pos X he,
    fun F V G W h => symbolAction_uniform_close F V G W X epsilon he h⟩

def symbolComparisonModulus (X : CyclicPresentation) (rate : Q' → Nat) (epsilon : Q') : Nat :=
  rate (approximationTolerance X epsilon)

theorem symbolAction_uniform_convergence (Fs : Nat → CtsMod) (Vs : ∀ n,MonotoneOmegaVanishing (Fs n))
    (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) (rate : Q' → Nat)
    (h : ∀ e : Q',(0 : Q')<e → ∀ n,rate e≤n → ∀ t : Q',(0 : Q')≤t → t≤1 →
      Q'.abs ((Fs n).f t-F.f t)≤e)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : symbolComparisonModulus X rate epsilon≤n) :
    RCle (completedDist (symbolAction (Fs n) (Vs n) X) (symbolAction F V X)) (rat epsilon) :=
  symbolAction_uniform_close _ _ F V X epsilon he
    (h _ (approximationTolerance_pos X he) n hn)

def symbolUniformLimitCertificate (Fs : Nat → CtsMod) (Vs : ∀ n,MonotoneOmegaVanishing (Fs n))
    (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) (rate : Q' → Nat)
    (h : ∀ e : Q',(0 : Q')<e → ∀ n,rate e≤n → ∀ t : Q',(0 : Q')≤t → t≤1 →
      Q'.abs ((Fs n).f t-F.f t)≤e) :
    Σ' Y : seminorm.Cauchy,
      {N : Q' → Nat // Quotient.mk seminorm.completionSetoid Y=symbolAction F V X ∧
        ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,N epsilon≤n →
          RCle (completedDist (symbolAction (Fs n) (Vs n) X) (Quotient.mk seminorm.completionSetoid Y)) (rat epsilon)} :=
  ⟨symbolRepresentative F V X,⟨symbolComparisonModulus X rate,rfl,
    symbolAction_uniform_convergence Fs Vs F V X rate h⟩⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUniformBound

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUniformBound.symbolAction_interval_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUniformBound.symbolAction_interval_norm_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUniformBound.symbolAction_interval_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUniformBound.symbolAction_uniform_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUniformBound.uniformComparisonCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUniformBound.symbolComparisonModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUniformBound.symbolAction_uniform_convergence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUniformBound.symbolUniformLimitCertificate
