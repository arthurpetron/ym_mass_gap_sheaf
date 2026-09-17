/-
# Quantitative decay on the SAME completed Wilson vacuum complement

Time balance identifies the two-step form with the one-step squared norm.
The proved invariant unit complement therefore admits induction with the
existing coupling-dependent rate q = timeRate(w)^2:

  B(T_n x,T_n x) <= q^n B(x,x),  B(x,U) = 0.

Sharp Cauchy--Schwarz gives squared mixed-correlator decay on this very
carrier. The scalar Cauchy data of a supplied representative compute a
rational norm ceiling and a tolerance cutoff; no quotient representative
is selected and no modulus is extracted from a Prop-level existential.

This is fixed-spacing, small-nome SU(2) discrete-time decay. It does not
assert one-step positivity, a nonzero positive-time response, full Hilbert
completeness, canonical OS/QFT realization, a calibrated physical mass,
changing-spacing control, or the all-compact-simple-group Clay theorem.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
import YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4WilsonSpatialUnionRelaxation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap (completed_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (scalarCeiling scalarCeiling_nonnegative scalar_approx_le_ceiling)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "q" => twoStepRate w hd

/-- q bounds one-step SQUARED norms, not an assumed one-step positive form. -/
theorem oneStep_norm_gap (x : V) (hx : B x U = RCzero) :
    RCle (B (T 1 x) (T 1 x)) (RCscale q (B x x)) := by
  rw [completedInner_time_balance, ← completedTime_add]
  exact completed_twoStep_form_gap hw0 hw1 hsmall hd hs x hx

/-- Every completed vector in the SAME unit complement, with no support bound. -/
theorem norm_decay (x : V) (hx : B x U = RCzero) : ∀ n : Nat,
    RCle (B (T n x) (T n x)) (RCscale (q^n) (B x x))
  | 0 => by
      rw [completedTime_zero, show q^0 = (1 : Q') from rfl, RCscale_one]
      exact RCle_refl _
  | n+1 => by
      have hstep := oneStep_norm_gap hw0 hw1 hsmall hd hs (T n x)
        (completedTime_preserves_orthogonal hw0 hw1 hsmall hd hs n x hx)
      rw [← completedTime_add, Nat.add_comm 1 n] at hstep
      have h := RCle_trans hstep
        (RCscale_mono (Q'.le_of_lt (twoStepRate_positive hw0 hd)) (norm_decay x hx n))
      rw [RCscale_RCscale] at h
      exact h

/-- The actual even-time autocorrelation has the SAME q^n bound. -/
theorem even_autocorrelation_decay (x : V) (hx : B x U = RCzero) (n : Nat) :
    RCle (B x (T (2*n) x)) (RCscale (q^n) (B x x)) := by
  rw [completedInner_even_diagonal]
  exact norm_decay hw0 hw1 hsmall hd hs x hx n

/-- The test vector is arbitrary; only the propagated vector is unit-orthogonal. -/
theorem mixed_correlator_sq_decay (x y : V) (hy : B y U = RCzero) (n : Nat) :
    RCle (RCmul (B x (T n y)) (B x (T n y)))
      (RCmul (B x x) (RCscale (q^n) (B y y))) :=
  RCle_trans (completedInner_cauchySchwarz hw0 hw1 hsmall hd hs x (T n y))
    (RCmul_mono_nonneg_left (completedInner_nonnegative hw0 hw1 hsmall hd hs x)
      (norm_decay hw0 hw1 hsmall hd hs y hy n))

/-- A computed ceiling for the actual representative's completed squared norm. -/
def normCap (X : (D).Cauchy) : Q' :=
  scalarCeiling (representativeInner hw0 hw1 hsmall hd hs X X)
    (representativeInnerCauchy hw0 hw1 hsmall hd hs X X)

theorem normCap_nonnegative (X : (D).Cauchy) : (0 : Q') ≤ normCap hw0 hw1 hsmall hd hs X :=
  scalarCeiling_nonnegative _ _

private theorem scalar_le_ceiling (s : CReal) (cs : QCauchy s.approx) :
    leEv s (ofQ' (scalarCeiling s cs)) := by
  intro epsilon he
  refine ⟨cs.M 1, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _) (scalar_approx_le_ceiling s cs n hn))
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

theorem norm_le_cap (X : (D).Cauchy) :
    RCle (B (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid X))
      (Quotient.mk crealSetoid (ofQ' (normCap hw0 hw1 hsmall hd hs X))) := scalar_le_ceiling _ _

/-- Depends explicitly on w through q and on the supplied stream through its cap. -/
def relaxationModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  geometricCutoff q (normCap hw0 hw1 hsmall hd hs X) epsilon

theorem norm_small (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : relaxationModulus hw0 hw1 hsmall hd hs X epsilon ≤ n) :
    RCle (B (T n (Quotient.mk (D).completionSetoid X))
      (T n (Quotient.mk (D).completionSetoid X))) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have h := RCle_trans
    (norm_decay hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) hX n)
    (RCscale_mono (Q'.pow_nonneg _ (Q'.le_of_lt (twoStepRate_positive hw0 hd)) _)
      (norm_le_cap hw0 hw1 hsmall hd hs X))
  refine RCle_trans h ?_
  exact leEv_le_ofQ'_of_approx_le (fun _ => geometric_bound
    (Q'.le_of_lt (twoStepRate_positive hw0 hd)) (twoStepRate_lt_one hw0 hd hs)
    (normCap_nonnegative hw0 hw1 hsmall hd hs X) he n hn)

/-- The threshold and its entire late-tail bound are returned as data. -/
def relaxationCertificate (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    {N : Nat // ∀ n, N ≤ n → RCle
      (B (T n (Quotient.mk (D).completionSetoid X)) (T n (Quotient.mk (D).completionSetoid X)))
      (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  ⟨relaxationModulus hw0 hw1 hsmall hd hs X epsilon,
    norm_small hw0 hw1 hsmall hd hs X hX epsilon he⟩

end YMGap.Continuum.BF4WilsonSpatialUnionRelaxation

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRelaxation.oneStep_norm_gap
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRelaxation.norm_decay
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRelaxation.even_autocorrelation_decay
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRelaxation.mixed_correlator_sq_decay
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRelaxation.normCap
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRelaxation.normCap_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRelaxation.norm_le_cap
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRelaxation.relaxationModulus
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRelaxation.norm_small
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRelaxation.relaxationCertificate
