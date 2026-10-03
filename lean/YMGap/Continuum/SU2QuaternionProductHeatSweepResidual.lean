/-
# ORIGINAL conditional heat sweeps commute with original-input residuals

Literal coefficient linearity and distinct-pair commutation show that a
selected residual after a sweep equals the sweep of the ORIGINAL residual.
The source can depend on every retained output and shared spectator.
No universal headMap identification, contraction, energy or variance premise
is used. This supplies the fixed-source algebra for weighted Efron--Stein;
the joint-law contraction and active-product Poincare join remain separate.
-/

import YMGap.Continuum.SU2QuaternionProductHeatHybridSweep

namespace YMGap.Continuum.SU2QuaternionProductHeatSweepResidual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionWeightedProjectionSweep
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatHybridSweep

theorem weightedSweep_congr (W : Nat → RatPoly) (ids : List Nat)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (weightedSweep W ids p) (weightedSweep W ids q) := by
  induction ids with
  | nil => exact h
  | cons i ids ih => exact project_congr i (ih.mul_left (W i))

theorem weightedSweep_add (W : Nat → RatPoly) (ids : List Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (weightedSweep W ids (polyAdd p q))
      (polyAdd (weightedSweep W ids p) (weightedSweep W ids q)) := by
  induction ids with
  | nil => exact .refl _
  | cons i ids ih =>
    refine (project_congr i ((ih.mul_left (W i)).trans
      (RatPolyCoeffEqv.mul_add_right _ _ _))).trans ?_
    rw [project_add]
    exact .refl _

theorem weightedSweep_neg (W : Nat → RatPoly) (ids : List Nat) (p : RatPoly) :
    RatPolyCoeffEqv (weightedSweep W ids (polyNeg p))
      (polyNeg (weightedSweep W ids p)) := by
  induction ids with
  | nil => exact .refl _
  | cons i ids ih =>
    have hmul : RatPolyCoeffEqv (polyMul (W i) (polyNeg (weightedSweep W ids p)))
        (polyNeg (polyMul (W i) (weightedSweep W ids p))) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => W i | _ => weightedSweep W ids p)
    exact (project_congr i ((ih.mul_left (W i)).trans hmul)).trans (project_neg i _)

/-- The actual selected update, retaining its original upper partner. -/
def update (n : Nat) (w : Q') (K i : Nat) (p : RatPoly) : RatPoly :=
  project i (polyMul (heatAt i (n+i) w K) p)

/-- The actual original-input residual used in the joint-law telescope. -/
def residual (n : Nat) (w : Q') (K i : Nat) (p : RatPoly) : RatPoly :=
  polyAdd p (polyNeg (update n w K i p))

theorem update_congr (n : Nat) (w : Q') (K i : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (update n w K i p) (update n w K i q) :=
  project_congr i (h.mul_left _)

/-- Includes repeats and a selected slot occurring in the sweep itself.
Only literal distinct lower/upper pair geometry is used. -/
theorem update_sweep_comm (n : Nat) (w : Q') (K i : Nat) (hi : i < n) :
    ∀ (ids : List Nat), (∀ j, j ∈ ids → j < n) → ∀ p : RatPoly,
      RatPolyCoeffEqv (update n w K i (hybridSweep n w K ids p))
        (hybridSweep n w K ids (update n w K i p))
  | [], _, p => .refl _
  | j::ids, hids, p => by
      have hj : j < n := hids j List.mem_cons_self
      have hcomm : RatPolyCoeffEqv
          (update n w K i (update n w K j (hybridSweep n w K ids p)))
          (update n w K j (update n w K i (hybridSweep n w K ids p))) := by
        by_cases he : i = j
        · subst j; exact .refl _
        · exact hybrid_updates_comm n w K i j hi hj he _
      exact hcomm.trans (update_congr n w K j
        (update_sweep_comm n w K i hi ids
          (fun k hk => hids k (List.mem_cons_of_mem j hk)) p))

/-- No enlarged sweep-source onset is needed to compare this residual:
it is the exact sweep image of the fixed ORIGINAL-input residual. -/
theorem residual_sweep_comm (n : Nat) (w : Q') (K i : Nat) (hi : i < n)
    (ids : List Nat) (hids : ∀ j, j ∈ ids → j < n) (p : RatPoly) :
    RatPolyCoeffEqv (residual n w K i (hybridSweep n w K ids p))
      (hybridSweep n w K ids (residual n w K i p)) := by
  have hlinear : RatPolyCoeffEqv (hybridSweep n w K ids (residual n w K i p))
      (polyAdd (hybridSweep n w K ids p)
        (polyNeg (hybridSweep n w K ids (update n w K i p)))) :=
    (weightedSweep_add (fun j => heatAt j (n+j) w K) ids p
      (polyNeg (update n w K i p))).trans
      ((RatPolyCoeffEqv.refl _).add
        (weightedSweep_neg (fun j => heatAt j (n+j) w K) ids (update n w K i p)))
  exact ((RatPolyCoeffEqv.refl _).add
    (RatPolyCoeffEqv.neg (update_sweep_comm n w K i hi ids hids p))).trans hlinear.symm

#print axioms weightedSweep_congr
#print axioms weightedSweep_add
#print axioms weightedSweep_neg
#print axioms update_congr
#print axioms update_sweep_comm
#print axioms residual_sweep_comm

end YMGap.Continuum.SU2QuaternionProductHeatSweepResidual
