/-
# Finite inactive-residual budgets for the actual hybrid-map endpoint

The budget carries a rational value and its proof for the explicit residual
of the original hybrid sweep. Every finite input has the displayed absolute
budget; supported inputs also have the exact residual-square budget. Neither
constructor supplies a cutoff-, volume-, spacing-, or nome-uniform estimate.

The endpoint compiler retains both the signed cross-term budget and this
inactive-projection budget. The exposed-link pairing certificates remain
explicit inputs. No interacting/OS gap or limiting estimate is claimed.
-/

import YMGap.Continuum.SU2QuaternionProductHeatHybridProjection

namespace YMGap.Continuum.SU2QuaternionProductHeatHybridSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification
open YMGap.Continuum.SU2HeatCutoffCasimirBound

/-- A finite upper bound for the actual residual square, with its computed
nonnegative rational budget retained as data rather than erased in Prop. -/
structure HybridInactiveResidualBudget
    (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (p : RatPoly) : Type where
  budget : Q'
  budget_nonneg : (0 : Q') ≤ budget
  residual_square_le :
    quaternionHaar (n+n)
      (polyMul (hybridInactiveResidual n w K ids p) (hybridInactiveResidual n w K ids p)) ≤ budget

/-- Inhabited for every finite input. This exact computed absolute value is
presentation-dependent; it is not a uniform analytic estimate. -/
def hybridInactiveResidualBudget_of_abs
    (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (p : RatPoly) :
    HybridInactiveResidualBudget n w K ids p where
  budget := Q'.abs (quaternionHaar (n+n)
    (polyMul (hybridInactiveResidual n w K ids p) (hybridInactiveResidual n w K ids p)))
  budget_nonneg := Q'.abs_nonneg _
  residual_square_le := Q'.le_abs_self _

/-- On the supported doubled carrier, the square certificate makes its
actual Haar value a nonnegative budget without taking an absolute value. -/
def hybridInactiveResidualBudget_of_square
    (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (n+n) p) :
    HybridInactiveResidualBudget n w K ids p where
  budget := quaternionHaar (n+n)
    (polyMul (hybridInactiveResidual n w K ids p) (hybridInactiveResidual n w K ids p))
  budget_nonneg := hybridInactiveResidual_square_nonnegative n w K ids hids hp
  residual_square_le := Q'.le_refl' _

/-- Finite arithmetic compiler: an upper bound for the sweep deficit becomes
one for the actual projected deficit after ADDING the residual budget. -/
theorem hybridMap_endpoint_bound_of_sweep_and_inactiveBudget
    (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (p : RatPoly)
    (sweepBound : Q')
    (hsweep : quaternionHaar (n+n) (polyMul p p) -
      quaternionHaar (n+n)
        (polyMul (hybridSweep n w K ids p) (hybridSweep n w K ids p)) ≤ sweepBound)
    (inactiveBudget : HybridInactiveResidualBudget n w K ids p) :
    quaternionHaar (n+n) (polyMul p p) -
      quaternionHaar n (polyMul (hybridMap n w K ids p) (hybridMap n w K ids p)) ≤
        sweepBound + inactiveBudget.budget :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (hybridMap_endpoint_eq_sweep_endpoint_add_inactive_square n w K ids p))
    (Q'.add_le_add hsweep inactiveBudget.residual_square_le)

/-- Compose the existing selected-stage angular estimate with both finite
budgets. The exposed-chart certificates remain explicit, and the two budget
values retain all dependence on the displayed carrier, cutoff and input. -/
theorem hybridMap_endpoint_bound_of_exposed_and_budgets
    (n : Nat) (ids : List Nat) (hn : 2 ≤ n)
    (hids : ∀ i, i ∈ ids → i < n)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : sufficientCutoff w ≤ K)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p)
    (exposed : ∀ (i : Nat) (hmem : i ∈ ids),
      SelectedLinkExposedHeadPairing
        (n+n-1) i (n+i)
        (by omega)
        (by have := hids i hmem; omega)
        (by have := hids i hmem; omega)
        (by have := hids i hmem; omega) w K)
    (crossBudget : HybridSweepSignedCrossTermBudget n w K ids p)
    (inactiveBudget : HybridInactiveResidualBudget n w K ids p) :
    quaternionHaar (n+n) (polyMul p p) -
      quaternionHaar n (polyMul (hybridMap n w K ids p) (hybridMap n w K ids p)) ≤
        (((1 : Q') - w) * qListSum (hybridSweepStageAngularEnergies n w K ids p) +
          crossBudget.budget) + inactiveBudget.budget :=
  hybridMap_endpoint_bound_of_sweep_and_inactiveBudget n w K ids p _
    (hybridSweep_endpoint_bound_of_exposed_and_crossBudget
      n ids hn hids hw0 hw1 K hK p hp exposed crossBudget) inactiveBudget

end YMGap.Continuum.SU2QuaternionProductHeatHybridSweep

#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.HybridInactiveResidualBudget
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridInactiveResidualBudget_of_abs
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridInactiveResidualBudget_of_square
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridMap_endpoint_bound_of_sweep_and_inactiveBudget
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridMap_endpoint_bound_of_exposed_and_budgets
