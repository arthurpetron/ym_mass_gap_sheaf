/-
# Norm separation and absence of stationary orthogonal Wilson union vectors

Common-base coherence identifies the actual distance to the zero stage
with the actual form diagonal. The generic constructive separation proof
therefore applies on this SAME union Cauchy quotient, using its computed
pairing rate as the closeness modulus. No quotient representatives are chosen.

Combined with the proved strict two-step bound, positive definiteness shows
that a unit-orthogonal vector fixed by two original time steps is zero.
This is not a continuum Hamiltonian spectral theorem, full Hilbert
completeness, observable coverage or a changing-spacing mass calibration.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra

namespace YMGap.Continuum.BF4WilsonSpatialUnionPosdef

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
  (zero intrinsicForm_zero_left distSq_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "P" => pairingData hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

attribute [local irreducible] pairing distSq
  BF4ExactSlabFixedSpatialWilsonIntrinsicForm.intrinsicForm
  BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq

theorem distance_zero (x : Stage) :
    Equiv (distSq hw0 hw1 hsmall hd hs x zeroStage) (pairing hw0 hw1 hsmall hd hs x x) := by
  have hz := distSq_at_base hw0 hw1 hsmall hd hs x zeroStage x.base
    (Nat.le_refl _) x.positive
  simp only [atBase_self, atBase_zero] at hz
  exact hz.trans ((distSq_zero hw0 hw1 hsmall hd hs x.positive x.value).trans
    (by simpa only [atBase_self] using
      (pairing_at_base hw0 hw1 hsmall hd hs x x x.base (Nat.le_refl _) (Nat.le_refl _)).symm))

theorem pairing_zero_left (x : Stage) :
    Equiv (pairing hw0 hw1 hsmall hd hs zeroStage x) czero := by
  have h := pairing_at_base hw0 hw1 hsmall hd hs zeroStage x x.base
    x.positive (Nat.le_refl _)
  simp only [atBase_zero, atBase_self] at h
  exact h.trans (intrinsicForm_zero_left hw0 hw1 hsmall hd hs x.positive x.value)

def completedZero : V := embedStage hw0 hw1 hsmall hd hs zeroStage

/-- The explicit modulus is the actual pairing rate of the supplied stream. -/
def closeZeroOfInnerZero (X : (D).Cauchy)
    (h : Equiv (representativeInner hw0 hw1 hsmall hd hs X X) czero) :
    (D).Close X ((D).constant zeroStage) :=
  CRealSeminormPairingCompletion.closeZeroOfInnerZero P zeroStage
    (distance_zero hw0 hw1 hsmall hd hs) X h

theorem closeZeroOfInnerZero_modulus (X : (D).Cauchy)
    (h : Equiv (representativeInner hw0 hw1 hsmall hd hs X X) czero) :
    (closeZeroOfInnerZero hw0 hw1 hsmall hd hs X h).modulus =
      CRealSeminormPairingCompletion.pairRate P X X := rfl

theorem completedInner_zero_left (x : V) :
    B (completedZero hw0 hw1 hsmall hd hs) x = RCzero := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (Equiv_of_limit_of_equal
    (fun n => pairing_zero_left hw0 hw1 hsmall hd hs (X.seq n))
    (CRealSeminormPairingCompletion.pairSequence_converges P ((D).constant zeroStage) X)
    (convergesTo_const czero))

theorem completedInner_zero_right (x : V) :
    B x (completedZero hw0 hw1 hsmall hd hs) = RCzero :=
  (completedInner_symm hw0 hw1 hsmall hd hs x (completedZero hw0 hw1 hsmall hd hs)).trans
    (completedInner_zero_left hw0 hw1 hsmall hd hs x)

theorem completedInner_posdef (x : V) :
    B x x = RCzero ↔ x = completedZero hw0 hw1 hsmall hd hs :=
  CRealSeminormPairingCompletion.completedInner_posdef P zeroStage
    (distance_zero hw0 hw1 hsmall hd hs) (pairing_zero_left hw0 hw1 hsmall hd hs zeroStage) x

/-- A stationary vector in the actual unit complement must vanish. -/
theorem fixed_orthogonal_eq_zero (x : V) (hx : B x U = RCzero) (ht : T 2 x = x) :
    x = completedZero hw0 hw1 hsmall hd hs := by
  have h := BF4WilsonSpatialUnionCompletedGap.completed_twoStep_form_gap hw0 hw1 hsmall hd hs x hx
  rw [ht] at h
  exact (completedInner_posdef hw0 hw1 hsmall hd hs x).mp
    (CRealSeminormPairingCompletion.scalar_contraction_zero (twoStepRate w hd)
      (twoStepRate_lt_one hw0 hd hs) (B x x)
      (completedInner_nonnegative hw0 hw1 hsmall hd hs x) h)

#print axioms distance_zero
#print axioms pairing_zero_left
#print axioms completedZero
#print axioms closeZeroOfInnerZero
#print axioms closeZeroOfInnerZero_modulus
#print axioms completedInner_zero_left
#print axioms completedInner_zero_right
#print axioms completedInner_posdef
#print axioms fixed_orthogonal_eq_zero

end YMGap.Continuum.BF4WilsonSpatialUnionPosdef
