/-
# Time balance on the SAME completed Wilson spatial union

Compare each finite pair at one computed common support base, use the
original reflected time-sum identity there, and pass through the actual
pairing limits. The completed time maps therefore preserve the coefficient
of the SAME fixed unit and its orthogonal complement. Even-time positivity
is the half-time norm identity; no one-step positivity is asserted.

These are laws on the existing Wilson union Cauchy quotient, not a new
carrier or a supplied operator model. They do not establish full Hilbert
completeness, full gauge-observable coverage, canonical OS reconstruction,
changing-spacing control, a physical Hamiltonian or the Clay theorem.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionPairingData

namespace YMGap.Continuum.BF4WilsonSpatialUnionTimeForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (intrinsicForm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm (intrinsicForm_time_sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction
  (intrinsicForm_advance_contraction)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "P" => pairing hw0 hw1 hsmall hd hs
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "A" n => timeNonexpansive hw0 hw1 hsmall hd hs n

attribute [local irreducible] pairing intrinsicForm

/-- The common spatial base is computed from just these two stages. -/
theorem pairing_time_sum (m n : Nat) (x y : Stage) :
    Equiv (P (time m x) (time n y)) (P x (time (m+n) y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have hl := pairing_at_base hw0 hw1 hsmall hd hs (time m x) (time n y) N hx hy
  have hr := pairing_at_base hw0 hw1 hsmall hd hs x (time (m+n) y) N hx hy
  simp only [atBase_time] at hl hr
  exact hl.trans ((intrinsicForm_time_sum hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) m n (atBase x hx) (atBase y hy)).trans hr.symm)

theorem pairing_time_contraction (n : Nat) (x : Stage) :
    leEv (P (time n x) (time n x)) (P x x) := by
  have hl := pairing_at_base hw0 hw1 hsmall hd hs (time n x) (time n x)
    x.base (Nat.le_refl _) (Nat.le_refl _)
  have hr := pairing_at_base hw0 hw1 hsmall hd hs x x
    x.base (Nat.le_refl _) (Nat.le_refl _)
  simp only [atBase_time, atBase_self] at hl hr
  exact leEv_trans (leEv_of_equiv hl)
    (leEv_trans (intrinsicForm_advance_contraction hw0 hw1 hsmall hd hs x.positive n x.value)
      (leEv_of_equiv hr.symm))

/-- Time and Cauchy-stream indices remain independent; no uniform support is assumed. -/
theorem representativeInner_time_sum (m n : Nat) (X Y : (D).Cauchy) :
    Equiv
      (representativeInner hw0 hw1 hsmall hd hs ((A m).mapCauchy X) ((A n).mapCauchy Y))
      (representativeInner hw0 hw1 hsmall hd hs X ((A (m+n)).mapCauchy Y)) := by
  apply Equiv_of_limit_of_equal
    (hA := CRealSeminormPairingCompletion.pairSequence_converges PD
      ((A m).mapCauchy X) ((A n).mapCauchy Y))
    (hB := CRealSeminormPairingCompletion.pairSequence_converges PD X ((A (m+n)).mapCauchy Y))
  intro k
  exact pairing_time_sum hw0 hw1 hsmall hd hs m n (X.seq k) (Y.seq k)

theorem completedInner_time_sum (m n : Nat) (x y : V) :
    B (T m x) (T n y) = B x (T (m+n) y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (representativeInner_time_sum hw0 hw1 hsmall hd hs m n X Y)

/-- Symmetry of each discrete advance with respect to the actual completed form. -/
theorem completedInner_time_balance (n : Nat) (x y : V) :
    B (T n x) y = B x (T n y) := by
  simpa only [completedTime_zero, Nat.add_zero] using
    completedInner_time_sum hw0 hw1 hsmall hd hs n 0 x y

theorem representativeInner_time_contraction (n : Nat) (X : (D).Cauchy) :
    leEv
      (representativeInner hw0 hw1 hsmall hd hs ((A n).mapCauchy X) ((A n).mapCauchy X))
      (representativeInner hw0 hw1 hsmall hd hs X X) := by
  apply leEv_of_convergesTo_le
    (CRealSeminormPairingCompletion.pairSequence_converges PD ((A n).mapCauchy X) ((A n).mapCauchy X))
    (CRealSeminormPairingCompletion.pairSequence_converges PD X X)
  intro k
  exact pairing_time_contraction hw0 hw1 hsmall hd hs n (X.seq k)

theorem completedInner_time_contraction (n : Nat) (x : V) :
    RCle (B (T n x) (T n x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact representativeInner_time_contraction hw0 hw1 hsmall hd hs n X

theorem completedInner_even_diagonal (n : Nat) (x : V) :
    B x (T (2*n) x) = B (T n x) (T n x) := by
  simpa only [Nat.two_mul] using
    (completedInner_time_sum hw0 hw1 hsmall hd hs n n x x).symm

/-- EVEN time only: the norm diagonal does not imply one-step positivity. -/
theorem completedInner_even_nonnegative (n : Nat) (x : V) :
    RCnonneg (B x (T (2*n) x)) := by
  rw [completedInner_even_diagonal]
  exact completedInner_nonnegative hw0 hw1 hsmall hd hs (T n x)

theorem completedInner_even_le_identity (n : Nat) (x : V) :
    RCle (B x (T (2*n) x)) (B x x) := by
  rw [completedInner_even_diagonal]
  exact completedInner_time_contraction hw0 hw1 hsmall hd hs n x

theorem completedUnitCoefficient_time (n : Nat) (x : V) : B (T n x) U = B x U := by
  rw [completedInner_time_balance, completedUnit_fixed]

theorem completedTime_preserves_orthogonal (n : Nat) (x : V) (hx : B x U = RCzero) :
    B (T n x) U = RCzero :=
  (completedUnitCoefficient_time hw0 hw1 hsmall hd hs n x).trans hx

/-- Literal original reflected correlator, with the SAME physical time advance. -/
theorem completedTime_correlator (n : Nat) (x y : Stage) :
    B (embedStage hw0 hw1 hsmall hd hs x) (T n (embedStage hw0 hw1 hsmall hd hs y)) =
      Quotient.mk crealSetoid (P x (time n y)) := by
  rw [completedTime_embedStage, completedInner_embedStage]

end YMGap.Continuum.BF4WilsonSpatialUnionTimeForm

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.pairing_time_sum
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.pairing_time_contraction
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.representativeInner_time_sum
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.completedInner_time_sum
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.completedInner_time_balance
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.representativeInner_time_contraction
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.completedInner_time_contraction
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.completedInner_even_diagonal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.completedInner_even_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.completedInner_even_le_identity
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.completedUnitCoefficient_time
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.completedTime_preserves_orthogonal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimeForm.completedTime_correlator
