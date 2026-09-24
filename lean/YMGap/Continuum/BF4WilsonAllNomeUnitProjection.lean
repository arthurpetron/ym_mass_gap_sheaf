/-
# Computed vacuum projection on the literal all-nome Wilson completion

The original completed pairing computes the coefficient against the actual
normalized unit, including its approximation modulus. Real scaling of the
constant unit stream constructs the projected vector. Pairing separation
gives quotient descent without choosing scalar or vector representatives.

This map acts on EVERY vector of the existing fixed-nome, fixed-width Wilson
completion. It is not a continuum vacuum, carrier identification or scaling
estimate. Its orthogonal complement is the existing vacuum-complement sector.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonAllNomeUnitProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

private theorem rc_mul_one (a : RC) :
    RCmul a (Quotient.mk crealSetoid (ofQ' 1)) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_one_eqv (A.approx n)))

private theorem rc_one_mul (a : RC) :
    RCmul (Quotient.mk crealSetoid (ofQ' 1)) a = a := by
  rw [RCmul_comm, rc_mul_one]

private theorem rc_zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul (A.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "T" => completedTime hw0 hw1

def unitCauchy : (D).Cauchy := (D).constant (unit width)

def unitCoefficient (X : (D).Cauchy) : CReal :=
  CRealSeminormPairingCompletion.representativeInner PD X (unitCauchy hw0 hw1)

/-- The modulus is computed for this actual scalar, not extracted from RC. -/
def unitCoefficientCauchy (X : (D).Cauchy) :
    QCauchy (unitCoefficient hw0 hw1 X).approx :=
  CRealSeminormPairingCompletion.representativeInnerCauchy PD X (unitCauchy hw0 hw1)

theorem unitCoefficient_pin (X : (D).Cauchy) :
    Quotient.mk crealSetoid (unitCoefficient hw0 hw1 X) =
      B (Quotient.mk (D).completionSetoid X) U := rfl

def unitProjectionCauchy (X : (D).Cauchy) : (D).Cauchy :=
  realScalarCauchy hw0 hw1 (unitCoefficient hw0 hw1 X)
    (unitCoefficientCauchy hw0 hw1 X) (unitCauchy hw0 hw1)

theorem unitProjectionCauchy_pairing (X : (D).Cauchy) (y : V) :
    B (Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 X)) y =
      RCmul (B (Quotient.mk (D).completionSetoid X) U) (B U y) :=
  realScalarCauchy_pairing hw0 hw1 _ _ (unitCauchy hw0 hw1) y

theorem unitProjectionCauchy_congr (X Y : (D).Cauchy)
    (h : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 X) =
      Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 Y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [unitProjectionCauchy_pairing, unitProjectionCauchy_pairing, h]

/-- Constructed map on the SAME Wilson completion; no representative choice. -/
def unitProjection : V → V :=
  Quotient.lift
    (fun X => Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 X))
    (fun X Y h => unitProjectionCauchy_congr hw0 hw1 X Y (Quotient.sound h))

local notation "P" => unitProjection hw0 hw1

theorem unitProjection_mk (X : (D).Cauchy) :
    P (Quotient.mk (D).completionSetoid X) =
      completedRealSmul hw0 hw1 (unitCoefficient hw0 hw1 X)
        (unitCoefficientCauchy hw0 hw1 X) U := rfl

theorem unitProjection_pairing (x y : V) :
    B (P x) y = RCmul (B x U) (B U y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => unitProjectionCauchy_pairing hw0 hw1 X y

theorem unitProjection_coefficient (x : V) : B (P x) U = B x U := by
  rw [unitProjection_pairing, unitState_norm_one, rc_mul_one]

theorem unitProjection_selfAdjoint (x y : V) : B (P x) y = B x (P y) := by
  rw [completedInner_symm hw0 hw1 x, unitProjection_pairing, unitProjection_pairing,
    completedInner_symm hw0 hw1 U y, completedInner_symm hw0 hw1 U x, RCmul_comm]

theorem unitProjection_idempotent (x : V) : P (P x) = P x := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [unitProjection_pairing, unitProjection_coefficient, unitProjection_pairing]

theorem unitProjection_unit : P U = U := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [unitProjection_pairing, unitState_norm_one, rc_one_mul]

theorem unitProjection_zero_iff (x : V) :
    P x = completedZero hw0 hw1 width ↔ B x U = RCzero := by
  constructor
  · intro h
    rw [← unitProjection_coefficient hw0 hw1 x, h, completedInner_zero_left]
  · intro h
    apply completed_eq_of_pairings hw0 hw1
    intro y
    rw [unitProjection_pairing, h, rc_zero_mul, completedInner_zero_left]

theorem unitProjection_add (x y : V) :
    P (completedAdd hw0 hw1 x y) = completedAdd hw0 hw1 (P x) (P y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [unitProjection_selfAdjoint, completedInner_add_left, completedInner_add_left,
    unitProjection_selfAdjoint, unitProjection_selfAdjoint]

theorem unitProjection_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    P (completedRealSmul hw0 hw1 s cs x) = completedRealSmul hw0 hw1 s cs (P x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [unitProjection_selfAdjoint, completedInner_realSmul_left,
    completedInner_realSmul_left, unitProjection_selfAdjoint]

theorem unitProjection_inner (x y : V) :
    B (P x) (P y) = RCmul (B x U) (B U y) := by
  rw [unitProjection_pairing, completedInner_symm hw0 hw1 U,
    unitProjection_coefficient, completedInner_symm hw0 hw1 y U]

theorem unitProjection_norm_le (x : V) : RCle (B (P x) (P x)) (B x x) := by
  have h := completedInner_cauchySchwarz hw0 hw1 x U
  rw [unitState_norm_one, rc_mul_one] at h
  rw [unitProjection_inner, completedInner_symm hw0 hw1 U x]
  exact h

/-- The projection commutes with the ORIGINAL discrete physical time map. -/
theorem unitProjection_time (n : Nat) (x : V) : P (T n x) = T n (P x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [unitProjection_pairing, completedInner_time_balance, completedUnit_fixed,
    completedInner_time_balance, unitProjection_pairing,
    ← completedInner_time_balance, completedUnit_fixed]

private theorem rc_negative_one (a : RC) : RCscale (-1) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n)))))

private theorem pairing_sub_left (x y z : V) :
    B (completedSub hw0 hw1 x y) z = RCsub (B x z) (B y z) := by
  unfold completedSub completedNeg RCsub
  rw [completedInner_add_left, completedInner_smul_left, rc_negative_one]

private theorem pairing_sub_right (x y z : V) :
    B x (completedSub hw0 hw1 y z) = RCsub (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 x, pairing_sub_left,
    completedInner_symm hw0 hw1 y x, completedInner_symm hw0 hw1 z x]

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CReal.sub_self_eqv_zero A)

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.const 0))) (.var 0) (by decide)
      (fun _ => A.approx n)))

/-- Remove the computed vacuum component from any actual completed vector. -/
def centeredPart (x : V) : V := completedSub hw0 hw1 x (P x)

theorem centeredPart_pairing (x y : V) :
    B (centeredPart hw0 hw1 x) y = RCsub (B x y) (RCmul (B x U) (B U y)) := by
  unfold centeredPart
  rw [pairing_sub_left, unitProjection_pairing]

theorem centeredPart_orthogonal (x : V) : B U (centeredPart hw0 hw1 x) = RCzero := by
  rw [completedInner_symm hw0 hw1 U, centeredPart_pairing,
    unitState_norm_one, rc_mul_one, rc_sub_self]

/-- The codomain is precisely the pre-existing SAME vacuum complement. -/
def centeredState (x : V) : VacuumComplement hw0 hw1 (width := width) :=
  ⟨centeredPart hw0 hw1 x, centeredPart_orthogonal hw0 hw1 x⟩

/-- Connected pairing for arbitrary completed vectors, not just dense loops. -/
theorem centeredPart_pairing_both (x y : V) :
    B (centeredPart hw0 hw1 x) (centeredPart hw0 hw1 y) =
      RCsub (B x y) (RCmul (B x U) (B U y)) := by
  have hzero : B (centeredPart hw0 hw1 x) (P y) = RCzero := by
    rw [completedInner_symm hw0 hw1 (centeredPart hw0 hw1 x),
      unitProjection_pairing, centeredPart_orthogonal, RCmul_comm, rc_zero_mul]
  change B (centeredPart hw0 hw1 x) (completedSub hw0 hw1 y (P y)) = _
  rw [pairing_sub_right, hzero, rc_sub_zero, centeredPart_pairing]

theorem centeredPart_time (n : Nat) (x : V) :
    centeredPart hw0 hw1 (T n x) = T n (centeredPart hw0 hw1 x) := by
  have hcoefficient : B (T n x) U = B x U := by
    rw [completedInner_time_balance, completedUnit_fixed]
  apply completed_eq_of_pairings hw0 hw1
  intro y
  have hunit_y : B U (T n y) = B U y := by
    rw [← completedInner_time_balance, completedUnit_fixed]
  rw [centeredPart_pairing,
    completedInner_time_balance hw0 hw1 n (centeredPart hw0 hw1 x) y,
    centeredPart_pairing, completedInner_time_balance hw0 hw1 n x y,
    hcoefficient, hunit_y]

/-- SAME-operator connected correlation for arbitrary completed states. -/
theorem centeredPart_time_pairing (n : Nat) (x y : V) :
    B (centeredPart hw0 hw1 x) (T n (centeredPart hw0 hw1 y)) =
      RCsub (B x (T n y)) (RCmul (B x U) (B U y)) := by
  rw [← centeredPart_time, centeredPart_pairing_both,
    ← completedInner_time_balance hw0 hw1 n U y, completedUnit_fixed]

#print axioms unitCauchy
#print axioms unitCoefficient
#print axioms unitCoefficientCauchy
#print axioms unitCoefficient_pin
#print axioms unitProjectionCauchy
#print axioms unitProjectionCauchy_pairing
#print axioms unitProjectionCauchy_congr
#print axioms unitProjection
#print axioms unitProjection_mk
#print axioms unitProjection_pairing
#print axioms unitProjection_coefficient
#print axioms unitProjection_selfAdjoint
#print axioms unitProjection_idempotent
#print axioms unitProjection_unit
#print axioms unitProjection_zero_iff
#print axioms unitProjection_add
#print axioms unitProjection_realSmul
#print axioms unitProjection_inner
#print axioms unitProjection_norm_le
#print axioms unitProjection_time
#print axioms centeredPart
#print axioms centeredPart_pairing
#print axioms centeredPart_orthogonal
#print axioms centeredState
#print axioms centeredPart_pairing_both
#print axioms centeredPart_time
#print axioms centeredPart_time_pairing

end YMGap.Continuum.BF4WilsonAllNomeUnitProjection
