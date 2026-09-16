/-
# Positive-definite completed union pairing and physical time balance

The dense zero-distance pin and sharp CS are proved in a computed common
base of the original spatial-limit form. Generic completion then supplies
positive definiteness and sharp CS on the same union Cauchy quotient.
Original time balance also passes through the actual mixed scalar limits.
No full completed vector-space, metric-completeness, observable-density,
or continuum claim is made by these form identities.
-/

import YMGap.Continuum.BF4SpatialUnionPairingData
import YMGap.Continuum.CRealSeminormPairingPosdef
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedPosdef

namespace YMGap.Continuum.BF4SpatialUnionGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData (pairingData completedInner)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime (spatialPairing_time_balance)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "P" => pairing hw0 hw1 hsmall hd hs
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

attribute [local irreducible] pairing distSq spatialPairing

theorem distance_zero (x : Stage) :
    Equiv (distSq hw0 hw1 hsmall hd hs x zeroStage) (P x x) := by
  have h := distSq_at_base hw0 hw1 hsmall hd hs x zeroStage x.base (Nat.le_refl _) x.positive
  have hp := pairing_at_base hw0 hw1 hsmall hd hs x x x.base (Nat.le_refl _) (Nat.le_refl _)
  simp only [atBase_self, atBase_zero] at h hp
  exact h.trans ((BF4ExactSlabFixedSpatialSpatialCompletedPosdef.distSq_zero
    hw0 hw1 x.base hsmall hd hs x.positive x.value).trans hp.symm)

theorem pairing_zero_zero : Equiv (P zeroStage zeroStage) czero :=
  (distance_zero hw0 hw1 hsmall hd hs zeroStage).symm.trans
    (distance_refl hw0 hw1 hsmall hd hs zeroStage)

theorem pairing_cauchySchwarz (x y : Stage) :
    leEv (mul (P x y) (P x y)) (mul (P x x) (P y y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have hxy := pairing_at_base hw0 hw1 hsmall hd hs x y N hx hy
  have hxx := pairing_at_base hw0 hw1 hsmall hd hs x x N hx hx
  have hyy := pairing_at_base hw0 hw1 hsmall hd hs y y N hy hy
  have hl := (CReal.mul_congr_left hxy).trans (TrigSignedAdd.mul_congr_right hxy)
  have hr := (CReal.mul_congr_left hxx).trans (TrigSignedAdd.mul_congr_right hyy)
  exact leEv_trans (leEv_of_equiv hl)
    (leEv_trans (spatialPairing_cauchySchwarz hw0 hw1 N hsmall hd hs
      (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase y hy)) (leEv_of_equiv hr.symm))

def completedZero : UnionCompletion hw0 hw1 hsmall hd hs := embedStage hw0 hw1 hsmall hd hs zeroStage

theorem completedZero_inner_zero : B (completedZero hw0 hw1 hsmall hd hs)
    (completedZero hw0 hw1 hsmall hd hs) = RCzero :=
  CRealSeminormPairingCompletion.completedZero_inner_zero PD zeroStage
    (pairing_zero_zero hw0 hw1 hsmall hd hs)

theorem completedInner_posdef (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    B x x = RCzero ↔ x = completedZero hw0 hw1 hsmall hd hs :=
  CRealSeminormPairingCompletion.completedInner_posdef PD zeroStage
    (distance_zero hw0 hw1 hsmall hd hs) (pairing_zero_zero hw0 hw1 hsmall hd hs) x

theorem completedInner_cauchySchwarz (x y : UnionCompletion hw0 hw1 hsmall hd hs) :
    RCle (RCmul (B x y) (B x y)) (RCmul (B x x) (B y y)) :=
  CRealSeminormPairingCompletion.completedInner_cauchySchwarz PD
    (pairing_cauchySchwarz hw0 hw1 hsmall hd hs) x y

theorem pairing_time_balance (n : Nat) (x y : Stage) :
    Equiv (P (time n x) y) (P x (time n y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have hl := pairing_at_base hw0 hw1 hsmall hd hs (time n x) y N hx hy
  have hr := pairing_at_base hw0 hw1 hsmall hd hs x (time n y) N hx hy
  simp only [atBase_time] at hl hr
  exact hl.trans ((spatialPairing_time_balance hw0 hw1 N hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) n (atBase x hx) (atBase y hy)).trans hr.symm)

theorem completedInner_time_balance (n : Nat) (x y : UnionCompletion hw0 hw1 hsmall hd hs) :
    B (T n x) y = B x (T n y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (Equiv_of_limit_of_equal
    (fun k => pairing_time_balance hw0 hw1 hsmall hd hs n (X.seq k) (Y.seq k))
    (CRealSeminormPairingCompletion.pairSequence_converges PD
      ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy X) Y)
    (CRealSeminormPairingCompletion.pairSequence_converges PD
      X ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy Y)))

theorem completedUnitCoefficient_time (n : Nat) (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    B (T n x) U = B x U := by
  rw [completedInner_time_balance, completedUnit_fixed]

end YMGap.Continuum.BF4SpatialUnionGeometry

#print axioms YMGap.Continuum.BF4SpatialUnionGeometry.distance_zero
#print axioms YMGap.Continuum.BF4SpatialUnionGeometry.pairing_zero_zero
#print axioms YMGap.Continuum.BF4SpatialUnionGeometry.pairing_cauchySchwarz
#print axioms YMGap.Continuum.BF4SpatialUnionGeometry.completedZero
#print axioms YMGap.Continuum.BF4SpatialUnionGeometry.completedZero_inner_zero
#print axioms YMGap.Continuum.BF4SpatialUnionGeometry.completedInner_posdef
#print axioms YMGap.Continuum.BF4SpatialUnionGeometry.completedInner_cauchySchwarz
#print axioms YMGap.Continuum.BF4SpatialUnionGeometry.pairing_time_balance
#print axioms YMGap.Continuum.BF4SpatialUnionGeometry.completedInner_time_balance
#print axioms YMGap.Continuum.BF4SpatialUnionGeometry.completedUnitCoefficient_time
