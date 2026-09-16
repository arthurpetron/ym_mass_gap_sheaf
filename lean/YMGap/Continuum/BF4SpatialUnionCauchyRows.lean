/-
# Represented limits commute with actual spatial-union time and centering

The generic diagonal construction is instantiated on the SAME physical
UnionCompletion. Physical time and centering map supplied Cauchy rows to
supplied Cauchy rows without changing the outer modulus, and commute with
their computed limits. In particular the existing unit complement is closed
under these represented limits. The actual relaxation orbit has a computed
row modulus and its limit is the already constructed unit projection.

No representatives of an arbitrary quotient-valued sequence are selected.
This is a constructive completion ingredient, not full Hilbert/OS/QFT
reconstruction or a continuum/spacing-uniform mass theorem.
-/

import YMGap.Continuum.CRealSeminormCauchyRows
import YMGap.Continuum.BF4SpatialUnionRelaxation

namespace YMGap.Continuum.BF4SpatialUnionCauchyRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCauchyRows
open YMGap.Continuum.CRealSeminormCompletedApproximation
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionGeometry
open YMGap.Continuum.BF4SpatialUnionCentered
open YMGap.Continuum.BF4SpatialUnionUnitProjection
open YMGap.Continuum.BF4SpatialUnionUnitComplement
open YMGap.Continuum.BF4SpatialUnionCompletedDistance
open YMGap.Continuum.BF4SpatialUnionRelaxation
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
local notation "C" => center hw0 hw1 hsmall hd hs
local notation "P" => unitProjection hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

/-- Actual time-mapped representatives, retaining the supplied outer modulus. -/
def timeRows (lag : Nat) (R : CauchyRows DP) : CauchyRows DP where
  row := fun n => (timeNonexpansive hw0 hw1 hsmall hd hs lag).mapCauchy (R.row n)
  modulus := R.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    exact RCle_trans
      (completedDist_time_contraction hw0 hw1 hsmall hd hs lag
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
  exact RCle_trans
    (completedDist_time_contraction hw0 hw1 hsmall hd hs lag
      (rowPoint DP R n) (rowLimit DP R)) (rowLimit_bound DP R epsilon he n hn)

/-- Centering is performed on the given representatives, with no quotient choice. -/
def centerRows (R : CauchyRows DP) : CauchyRows DP where
  row := fun n => centerCauchy hw0 hw1 hsmall hd hs (R.row n)
  modulus := R.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    exact RCle_trans (center_nonexpansive hw0 hw1 hsmall hd hs
      (rowPoint DP R m) (rowPoint DP R n)) (R.isCauchy epsilon he m n hm hn)

theorem centerRows_point (R : CauchyRows DP) (n : Nat) :
    rowPoint DP (centerRows hw0 hw1 hsmall hd hs R) n = C (rowPoint DP R n) := rfl

theorem centerRows_modulus (R : CauchyRows DP) :
    (centerRows hw0 hw1 hsmall hd hs R).modulus = R.modulus := rfl

theorem rowLimit_center (R : CauchyRows DP) :
    rowLimit DP (centerRows hw0 hw1 hsmall hd hs R) = C (rowLimit DP R) := by
  apply rowLimit_eq_of_bound DP _ _ (rowLimitRate DP R)
  intro epsilon he n hn
  rw [centerRows_point]
  exact RCle_trans (center_nonexpansive hw0 hw1 hsmall hd hs
    (rowPoint DP R n) (rowLimit DP R)) (rowLimit_bound DP R epsilon he n hn)

/-- The pre-existing unit complement is closed under supplied represented limits. -/
theorem rowLimit_orthogonal (R : CauchyRows DP)
    (h : ∀ n, B (rowPoint DP R n) U = RCzero) : B (rowLimit DP R) U = RCzero := by
  apply (center_fixed_iff hw0 hw1 hsmall hd hs _).mp
  rw [← rowLimit_center]
  apply rowLimit_independent DP
  intro n
  rw [centerRows_point]
  exact (center_fixed_iff hw0 hw1 hsmall hd hs _).mpr (h n)

def orthogonalRowLimit (R : CauchyRows DP)
    (h : ∀ n, B (rowPoint DP R n) U = RCzero) : UnitComplement hw0 hw1 hsmall hd hs :=
  ⟨rowLimit DP R, rowLimit_orthogonal hw0 hw1 hsmall hd hs R h⟩

/-- The original orbit, with an explicit outer rate computed from its input stream. -/
def relaxationRows (X : (D).Cauchy) : CauchyRows DP where
  row := fun n => (timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy X
  modulus := fun epsilon => relaxationModulus hw0 hw1 hsmall hd hs X (quarter epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    let x : V := Quotient.mk (D).completionSetoid X
    have hl := relaxation_small hw0 hw1 hsmall hd hs X (quarter epsilon) (quarter_pos he) m hm
    have hr := relaxation_small hw0 hw1 hsmall hd hs X (quarter epsilon) (quarter_pos he) n hn
    rw [completedDist_symm] at hr
    exact completedDist_two_segment DP (T m x) (P x) (T n x) epsilon hl hr

theorem relaxationRows_point (X : (D).Cauchy) (n : Nat) :
    rowPoint DP (relaxationRows hw0 hw1 hsmall hd hs X) n =
      T n (Quotient.mk (D).completionSetoid X) := rfl

/-- The computed diagonal limit is the SAME actual stationary projection. -/
theorem relaxationRows_limit (X : (D).Cauchy) :
    rowLimit DP (relaxationRows hw0 hw1 hsmall hd hs X) =
      P (Quotient.mk (D).completionSetoid X) := by
  apply rowLimit_eq_of_bound DP _ _ (relaxationModulus hw0 hw1 hsmall hd hs X)
  exact relaxation_small hw0 hw1 hsmall hd hs X

end YMGap.Continuum.BF4SpatialUnionCauchyRows

#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.timeRows
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.timeRows_point
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.timeRows_modulus
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.rowLimit_time
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.centerRows
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.centerRows_point
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.centerRows_modulus
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.rowLimit_center
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.rowLimit_orthogonal
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.orthogonalRowLimit
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.relaxationRows
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.relaxationRows_point
#print axioms YMGap.Continuum.BF4SpatialUnionCauchyRows.relaxationRows_limit
