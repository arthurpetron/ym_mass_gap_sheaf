/-
# Represented Wilson union limits and the actual decaying time orbit

The computed diagonal limit of supplied Cauchy rows lies in the SAME Wilson
completion. Original time preserves each outer modulus and commutes with
this limit. For a supplied unit-orthogonal representative, the previously
proved geometric norm certificate constructs an actual Cauchy time orbit;
its diagonal limit is the already constructed zero vector.

Rows include their representatives and moduli as data. No representatives
of an arbitrary quotient-valued sequence are chosen. This is a constructive
completion ingredient and fixed-spacing relaxation, not full real Hilbert
or canonical OS/QFT reconstruction, continuum survival or a physical mass.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
import YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
import YMGap.Continuum.CRealSeminormCauchyRows

namespace YMGap.Continuum.BF4WilsonSpatialUnionCauchyRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCauchyRows
open YMGap.Continuum.CRealSeminormCompletedApproximation
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "DP" => distanceData hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs

/-- Supplied rows, no countable selection of representatives from the quotient. -/
def timeRows (lag : Nat) (R : CauchyRows DP) : CauchyRows DP where
  row := fun n => (timeNonexpansive hw0 hw1 hsmall hd hs lag).mapCauchy (R.row n)
  modulus := R.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    exact RCle_trans (completedDist_time_contraction hw0 hw1 hsmall hd hs lag
      (rowPoint DP R m) (rowPoint DP R n)) (R.isCauchy epsilon he m n hm hn)

theorem timeRows_point (lag : Nat) (R : CauchyRows DP) (n : Nat) :
    rowPoint DP (timeRows hw0 hw1 hsmall hd hs lag R) n = T lag (rowPoint DP R n) := rfl

theorem timeRows_modulus (lag : Nat) (R : CauchyRows DP) :
    (timeRows hw0 hw1 hsmall hd hs lag R).modulus = R.modulus := rfl

theorem rowLimit_time (lag : Nat) (R : CauchyRows DP) :
    rowLimit DP (timeRows hw0 hw1 hsmall hd hs lag R) = T lag (rowLimit DP R) := by
  apply rowLimit_eq_of_bound DP _ _ (rowLimitRate DP R)
  intro epsilon he n hn
  rw [timeRows_point]
  exact RCle_trans (completedDist_time_contraction hw0 hw1 hsmall hd hs lag
    (rowPoint DP R n) (rowLimit DP R)) (rowLimit_bound DP R epsilon he n hn)

/-- The SAME norm certificate is an actual distance-to-zero estimate. -/
theorem relaxation_distance_small (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : relaxationModulus hw0 hw1 hsmall hd hs X epsilon ≤ n) :
    RCle (completedDist hw0 hw1 hsmall hd hs (T n (Quotient.mk (D).completionSetoid X)) Z)
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  rw [completedDist_zero_right]
  exact norm_small hw0 hw1 hsmall hd hs X hX epsilon he n hn

/-- Original physical-time orbit with a computed outer rate and supplied inner rows. -/
def relaxationRows (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) : CauchyRows DP where
  row := fun n => (timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy X
  modulus := fun epsilon => relaxationModulus hw0 hw1 hsmall hd hs X (quarter epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    let x : V := Quotient.mk (D).completionSetoid X
    have hl := relaxation_distance_small hw0 hw1 hsmall hd hs X hX
      (quarter epsilon) (quarter_pos he) m hm
    have hr := relaxation_distance_small hw0 hw1 hsmall hd hs X hX
      (quarter epsilon) (quarter_pos he) n hn
    rw [completedDist_symm] at hr
    exact completedDist_two_segment DP (T m x) Z (T n x) epsilon hl hr

theorem relaxationRows_point (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) (n : Nat) :
    rowPoint DP (relaxationRows hw0 hw1 hsmall hd hs X hX) n =
      T n (Quotient.mk (D).completionSetoid X) := rfl

attribute [local irreducible] relaxationModulus

theorem relaxationRows_modulus (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) (epsilon : Q') :
    (relaxationRows hw0 hw1 hsmall hd hs X hX).modulus epsilon =
      relaxationModulus hw0 hw1 hsmall hd hs X (quarter epsilon) := rfl

/-- The computed diagonal converges to the existing zero, not an adjoined state. -/
theorem relaxationRows_limit (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) :
    rowLimit DP (relaxationRows hw0 hw1 hsmall hd hs X hX) = Z := by
  apply rowLimit_eq_of_bound DP _ _ (relaxationModulus hw0 hw1 hsmall hd hs X)
  exact relaxation_distance_small hw0 hw1 hsmall hd hs X hX

#print axioms timeRows
#print axioms timeRows_point
#print axioms timeRows_modulus
#print axioms rowLimit_time
#print axioms relaxation_distance_small
#print axioms relaxationRows
#print axioms relaxationRows_point
#print axioms relaxationRows_modulus
#print axioms relaxationRows_limit

end YMGap.Continuum.BF4WilsonSpatialUnionCauchyRows
