/-
# Continuous symbols act on the ORIGINAL unit by evaluation at one

The original geometric times fix the original unit, so polynomial action
is evaluation at one times that same unit. Explicit Bernstein convergence
at one and the exact scalar-distance identity give the continuous action
with an explicit rate. The clipped coordinate recovers the pre-existing
two-step transfer. No eigenvector, spectral model or limit pin is assumed.

These are fixed-nome/spacing equalities, not a physical Hamiltonian or
continuum construction.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols

namespace YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit

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
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection (unitCauchy)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (smul_norm)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit (squareTolerance squareTolerance_pos squareTolerance_budget)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier (symbolErrorModulus)
open YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility (bernstein_symbol_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols

local notation "u" => completedUnit
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem sub_same_smul (a b : Q') (x : Completion) :
    completedSub (completedSmul a x) (completedSmul b x)=completedSmul (a-b) x := by
  unfold completedSub completedNeg
  rw [completedSmul_mul,completedAdd_smul]
  exact completedSmul_congr (Q'.add_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 b) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv b)))) x

theorem scalar_distance (a b : Q') (x : Completion) :
    completedDist (completedSmul a x) (completedSmul b x)=RCscale ((a-b)*(a-b)) (completedInner x x) := by
  unfold completedDist
  rw [sub_same_smul,smul_norm]

theorem polynomial_unit (p : QPoly.Poly) (r : Nat) :
    polynomialVector u p r=completedSmul (QPoly.eval p 1) u := by
  induction p generalizing r with
  | nil => exact (completedSmul_zero u).symm
  | cons c p ih =>
      rw [polynomialVector,completedTime_unit,ih,completedAdd_smul]
      exact completedSmul_congr (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))) u

theorem coordinate_action (x : Completion) :
    continuousAction coordinateSymbol coordinateVanishing x=twoStepTransfer x := by
  apply (continuousAction_eq_polynomial _ _ [0,1] ?_ x).trans (operator_coordinate x)
  intro t ht h1
  rw [coordinate_value t ht h1]
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _
    (QPoly.q_zero_add_eqv _) (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (eval_single 1 t)) (Q'.mul_one_eqv t)))

theorem unit_scalar_close (a b epsilon : Q') (he : (0 : Q')<epsilon)
    (h : Q'.abs (a-b)≤squareTolerance epsilon) :
    RCle (completedDist (completedSmul a u) (completedSmul b u)) (rat epsilon) := by
  rw [scalar_distance,completedUnit_norm_one]
  have hd := Q'.le_of_lt (squareTolerance_pos epsilon he)
  have hs : (a-b)*(a-b)≤squareTolerance epsilon*squareTolerance epsilon :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (abs_sq (a-b)))
      (Q'.mul_le_mul_of_nonneg h h hd (Q'.abs_nonneg _))
  exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _ hs (squareTolerance_budget epsilon he)))

def unitActionModulus (F : CtsMod) (V : MonotoneOmegaVanishing F) (epsilon : Q') : Nat :=
  (symbolErrorModulus F V).stage (squareTolerance epsilon)

theorem unitAction_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : unitActionModulus F V epsilon≤n) :
    RCle (completedDist (polynomialOperator (bernsteinPoly F n) u) (completedSmul (F.f 1) u)) (rat epsilon) := by
  rw [polynomialOperator,polynomial_unit]
  apply unit_scalar_close _ _ epsilon he
  have h := bernstein_symbol_bound F V _ (squareTolerance_pos epsilon he) n hn 1 Q'.zero_le_one (Q'.le_refl' _)
  exact abs_sub_le_of_bounds h.1 h.2

theorem continuousAction_unit (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    continuousAction F V u=completedSmul (F.f 1) u := by
  apply rowLimit_eq_of_bound (symbolRows F V unitCauchy) _ (unitActionModulus F V)
  intro epsilon he n hn
  rw [symbolRows_pin]
  exact unitAction_bound F V epsilon he n hn

end YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit.sub_same_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit.scalar_distance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit.polynomial_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit.coordinate_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit.unit_scalar_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit.unitActionModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit.unitAction_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit.continuousAction_unit
