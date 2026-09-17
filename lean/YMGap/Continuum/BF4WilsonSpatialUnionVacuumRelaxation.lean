/-
# All-vector relaxation to the SAME Wilson vacuum projection

The actual centered vector is orthogonal to the actual unit. Its previously
proved norm decay is exactly the squared distance from the original time
orbit to its computed unit projection. This removes the orthogonality
premise on the input vector, without changing the carrier or time operator.

For every supplied Cauchy representative, the centered representative gives
an explicit tolerance cutoff. The ORIGINAL time orbit is a represented
Cauchy row family and its computed diagonal limit is its existing vacuum
projection. The connected scalar is pinned to the same centered vectors,
so its squared decay follows with their actual norm prefactors.

Fixed-spacing, small-nome SU(2) only. No one-step positivity, nonzero
positive-time response, canonical OS/QFT realization, changing-spacing
control, finite physical mass or continuum/all-group closure is asserted.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
import YMGap.Continuum.BF4WilsonSpatialUnionCauchyRows

namespace YMGap.Continuum.BF4WilsonSpatialUnionVacuumRelaxation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion (Stage unitStage)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner completedInner_embedStage)
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear (completedSub completedTime_sub)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap (completedCenteredScalar)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm (completedTime_correlator)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
open YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm (centeredMoment)
open YMGap.Continuum.CRealSeminormCauchyRows
open YMGap.Continuum.CRealSeminormCompletedApproximation (completedDist_two_segment)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "DP" => distanceData hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "P" => unitProjection hw0 hw1 hsmall hd hs
local notation "C" => center hw0 hw1 hsmall hd hs
local notation "d" => completedDist hw0 hw1 hsmall hd hs
local notation "q" => twoStepRate w hd
local notation "K" => completedCenteredScalar hw0 hw1 hsmall hd hs

/-- All vectors, not an assumed orthogonal input. -/
theorem distance_to_projection (n : Nat) (x : V) :
    d (T n x) (P x) = B (T n (C x)) (T n (C x)) := by
  unfold completedDist center
  rw [completedTime_sub, time_unitProjection]

theorem distance_to_projection_decay (n : Nat) (x : V) :
    RCle (d (T n x) (P x)) (RCscale (q^n) (B (C x) (C x))) := by
  rw [distance_to_projection]
  exact norm_decay hw0 hw1 hsmall hd hs (C x) (center_orthogonal hw0 hw1 hsmall hd hs x) n

/-- Original connected scalar; the two prefactors are actual centered norms. -/
theorem connected_sq_decay (n : Nat) (x y : V) :
    RCle (RCmul (K n x y) (K n x y))
      (RCmul (B (C x) (C x)) (RCscale (q^n) (B (C y) (C y)))) := by
  rw [← centered_time_pairing]
  exact mixed_correlator_sq_decay hw0 hw1 hsmall hd hs (C x) (C y)
    (center_orthogonal hw0 hw1 hsmall hd hs y) n

/-- The SAME dense original connected Wilson moment is recovered exactly. -/
theorem connected_embedStage (n : Nat) (x y : Stage) :
    K n (embedStage hw0 hw1 hsmall hd hs x) (embedStage hw0 hw1 hsmall hd hs y) =
      Quotient.mk crealSetoid (centeredMoment hw0 hw1 hsmall hd hs n x y) := by
  unfold completedCenteredScalar
  rw [completedTime_correlator]
  change RCsub _ (RCmul
    (B (embedStage hw0 hw1 hsmall hd hs x) (embedStage hw0 hw1 hsmall hd hs unitStage))
    (B (embedStage hw0 hw1 hsmall hd hs unitStage) (embedStage hw0 hw1 hsmall hd hs y))) = _
  rw [completedInner_embedStage, completedInner_embedStage]
  rfl

/-- The rate is computed from the actual centered stream and the explicit q(w). -/
def vacuumModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  relaxationModulus hw0 hw1 hsmall hd hs (centerCauchy hw0 hw1 hsmall hd hs X) epsilon

theorem distance_to_projection_small (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : vacuumModulus hw0 hw1 hsmall hd hs X epsilon ≤ n) :
    RCle (d (T n (Quotient.mk (D).completionSetoid X))
      (P (Quotient.mk (D).completionSetoid X))) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  rw [distance_to_projection, center_mk]
  exact norm_small hw0 hw1 hsmall hd hs (centerCauchy hw0 hw1 hsmall hd hs X)
    (by rw [← center_mk]; exact center_orthogonal hw0 hw1 hsmall hd hs _)
    epsilon he n hn

/-- Witness-bearing tail bound, with no representative selected from a quotient. -/
def vacuumCertificate (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    {N : Nat // ∀ n, N ≤ n → RCle
      (d (T n (Quotient.mk (D).completionSetoid X)) (P (Quotient.mk (D).completionSetoid X)))
      (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  ⟨vacuumModulus hw0 hw1 hsmall hd hs X epsilon,
    distance_to_projection_small hw0 hw1 hsmall hd hs X epsilon he⟩

/-- These are the original uncentered time rows, not replacement centered rows. -/
def vacuumRows (X : (D).Cauchy) : CauchyRows DP where
  row := fun n => (timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy X
  modulus := fun epsilon => vacuumModulus hw0 hw1 hsmall hd hs X (quarter epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    let x : V := Quotient.mk (D).completionSetoid X
    have hl := distance_to_projection_small hw0 hw1 hsmall hd hs X
      (quarter epsilon) (quarter_pos he) m hm
    have hr := distance_to_projection_small hw0 hw1 hsmall hd hs X
      (quarter epsilon) (quarter_pos he) n hn
    rw [completedDist_symm] at hr
    exact completedDist_two_segment DP (T m x) (P x) (T n x) epsilon hl hr

attribute [local irreducible] vacuumModulus

theorem vacuumRows_point (X : (D).Cauchy) (n : Nat) :
    rowPoint DP (vacuumRows hw0 hw1 hsmall hd hs X) n =
      T n (Quotient.mk (D).completionSetoid X) := rfl

theorem vacuumRows_modulus (X : (D).Cauchy) (epsilon : Q') :
    (vacuumRows hw0 hw1 hsmall hd hs X).modulus epsilon =
      vacuumModulus hw0 hw1 hsmall hd hs X (quarter epsilon) := rfl

/-- The generic computed diagonal limit is the already constructed projection. -/
theorem vacuumRows_limit (X : (D).Cauchy) :
    rowLimit DP (vacuumRows hw0 hw1 hsmall hd hs X) =
      P (Quotient.mk (D).completionSetoid X) := by
  apply rowLimit_eq_of_bound DP _ _ (vacuumModulus hw0 hw1 hsmall hd hs X)
  exact distance_to_projection_small hw0 hw1 hsmall hd hs X

#print axioms distance_to_projection
#print axioms distance_to_projection_decay
#print axioms connected_sq_decay
#print axioms connected_embedStage
#print axioms vacuumModulus
#print axioms distance_to_projection_small
#print axioms vacuumCertificate
#print axioms vacuumRows
#print axioms vacuumRows_point
#print axioms vacuumRows_modulus
#print axioms vacuumRows_limit

end YMGap.Continuum.BF4WilsonSpatialUnionVacuumRelaxation
