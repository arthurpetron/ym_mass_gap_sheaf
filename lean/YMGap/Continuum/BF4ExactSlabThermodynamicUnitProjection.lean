/-
# Projection onto the SAME original thermodynamic completed unit

The coefficient is the actual original mixed-pairing limit, with its
constructed QCauchy modulus. Scaling the original constant-unit stream
returns a representative of the projection. Pairing separation proves
quotient descent without selecting scalar or vector representatives.

The resulting rank-one map is self-adjoint, idempotent, linear and
norm-contractive on this SAME carrier. The unit has norm one; it is not
assumed or proved here to be a stationary physical vacuum.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarAlgebra

namespace YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar

private theorem rc_mul_one (a : RC) : RCmul a (Quotient.mk crealSetoid cone) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CRealAlg.cmul_cone A)

private theorem rc_one_mul (a : RC) : RCmul (Quotient.mk crealSetoid cone) a = a := by
  rw [RCmul_comm, rc_mul_one]

private theorem rc_zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul (A.approx n)))

local notation "D" => seminorm
local notation "u" => completedUnit
local notation "B" => completedInner

def unitCauchy : (D).Cauchy := (D).constant BF4ExactSlabThermodynamicPresentation.one

theorem unitCauchy_pin : Quotient.mk (D).completionSetoid unitCauchy = u := rfl

def unitCoefficient (X : (D).Cauchy) : CReal :=
  representativeInner X (unitCauchy)

def unitCoefficientCauchy (X : (D).Cauchy) : QCauchy (unitCoefficient X).approx :=
  representativeInnerCauchy X (unitCauchy)

theorem unitCoefficient_pin (X : (D).Cauchy) :
    Quotient.mk crealSetoid (unitCoefficient X) = B (Quotient.mk (D).completionSetoid X) u := rfl

def unitProjectionCauchy (X : (D).Cauchy) : (D).Cauchy :=
  realScalarCauchy (unitCoefficient X) (unitCoefficientCauchy X)
    (unitCauchy)

theorem unitProjectionCauchy_pairing (X : (D).Cauchy) (y : Completion) :
    B (Quotient.mk (D).completionSetoid (unitProjectionCauchy X)) y =
      RCmul (B (Quotient.mk (D).completionSetoid X) u) (B u y) :=
  realScalarCauchy_pairing _ _ (unitCauchy) y

theorem unitProjectionCauchy_congr (X Y : (D).Cauchy)
    (h : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (unitProjectionCauchy X) =
      Quotient.mk (D).completionSetoid (unitProjectionCauchy Y) := by
  apply completed_eq_of_pairings
  intro z
  rw [unitProjectionCauchy_pairing, unitProjectionCauchy_pairing, h]

def unitProjection : Completion → Completion :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid (unitProjectionCauchy X))
    (fun X Y h => unitProjectionCauchy_congr X Y (Quotient.sound h))

theorem unitProjection_mk (X : (D).Cauchy) :
    unitProjection (Quotient.mk (D).completionSetoid X) =
      completedRealSmul (unitCoefficient X) (unitCoefficientCauchy X) u := rfl

theorem unitProjection_pairing (x y : Completion) :
    B (unitProjection x) y = RCmul (B x u) (B u y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => unitProjectionCauchy_pairing X y

theorem unitProjection_coefficient (x : Completion) : B (unitProjection x) u = B x u := by
  rw [unitProjection_pairing, completedUnit_norm_one, rc_mul_one]

theorem unitProjection_selfAdjoint (x y : Completion) :
    B (unitProjection x) y = B x (unitProjection y) := by
  rw [completedInner_symm x, unitProjection_pairing, unitProjection_pairing,
    completedInner_symm u y, completedInner_symm u x, RCmul_comm]

theorem unitProjection_idempotent (x : Completion) :
    unitProjection (unitProjection x) = unitProjection x := by
  apply completed_eq_of_pairings
  intro y
  rw [unitProjection_pairing, unitProjection_coefficient, unitProjection_pairing]

theorem unitProjection_unit : unitProjection u = u := by
  apply completed_eq_of_pairings
  intro y
  rw [unitProjection_pairing, completedUnit_norm_one, rc_one_mul]

theorem unitProjection_zero_iff (x : Completion) :
    unitProjection x = completedZero ↔ B x u = RCzero := by
  constructor
  · intro h
    rw [← unitProjection_coefficient x, h, completedInner_zero_left]
  · intro h
    apply completed_eq_of_pairings
    intro y
    rw [unitProjection_pairing, h, rc_zero_mul, completedInner_zero_left]

theorem unitProjection_add (x y : Completion) :
    unitProjection (completedAdd x y) =
      completedAdd (unitProjection x) (unitProjection y) := by
  apply completed_eq_of_pairings
  intro z
  rw [unitProjection_selfAdjoint, completedInner_add_left, completedInner_add_left,
    unitProjection_selfAdjoint, unitProjection_selfAdjoint]

theorem unitProjection_realSmul (s : CReal) (cs : QCauchy s.approx) (x : Completion) :
    unitProjection (completedRealSmul s cs x) =
      completedRealSmul s cs (unitProjection x) := by
  apply completed_eq_of_pairings
  intro y
  rw [unitProjection_selfAdjoint, completedInner_realSmul_left, completedInner_realSmul_left, unitProjection_selfAdjoint]

theorem unitProjection_inner (x y : Completion) :
    B (unitProjection x) (unitProjection y) = RCmul (B x u) (B u y) := by
  rw [unitProjection_pairing, completedInner_symm u, unitProjection_coefficient, completedInner_symm y u]

theorem unitProjection_norm_le (x : Completion) :
    RCle (B (unitProjection x) (unitProjection x)) (B x x) := by
  have h := completedInner_cauchySchwarz x u
  rw [completedUnit_norm_one, rc_mul_one] at h
  rw [unitProjection_inner, completedInner_symm u x]
  exact h

end YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitCauchy_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitCoefficientCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitCoefficient_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjectionCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjectionCauchy_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjectionCauchy_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_coefficient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_selfAdjoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_idempotent
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_inner
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection.unitProjection_norm_le
