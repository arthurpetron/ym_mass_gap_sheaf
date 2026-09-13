/-
# Constructed projection onto the ORIGINAL completed plaquette unit

On a supplied original Cauchy representative X, the coefficient <X,u>
is the actual mixed-pairing limit, with its already computed QCauchy
modulus. Scaling the constant unit stream by that coefficient constructs
a representative. Pairing separation proves quotient descent; no scalar
or vector representative is selected from an erased existence statement.

The rank-one map is self-adjoint, idempotent and contractive on this SAME
completion. The unit has norm one, but its identification with a physical
stationary vacuum is not proved or assumed here.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar

private theorem rc_mul_one (a : RC) : RCmul a (Quotient.mk crealSetoid cone) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CRealAlg.cmul_cone A)

private theorem rc_one_mul (a : RC) : RCmul (Quotient.mk crealSetoid cone) a = a := by
  rw [RCmul_comm, rc_mul_one]

private theorem rc_zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul (A.approx n)))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half
local notation "u" => completedUnit w hw0 hw1 half
local notation "B" => completedInner w hw0 hw1

def unitCauchy (half : Nat) : (seminorm w hw0 hw1 half).Cauchy :=
  (seminorm w hw0 hw1 half).constant .unit

def unitCoefficient (X : (D).Cauchy) : CReal :=
  representativeInner w hw0 hw1 X (unitCauchy w hw0 hw1 half)

def unitCoefficientCauchy (X : (D).Cauchy) : QCauchy (unitCoefficient w hw0 hw1 X).approx :=
  representativeInnerCauchy w hw0 hw1 X (unitCauchy w hw0 hw1 half)

theorem unitCoefficient_pin (X : (D).Cauchy) :
    Quotient.mk crealSetoid (unitCoefficient w hw0 hw1 X) = B (Quotient.mk (D).completionSetoid X) u := rfl

def unitProjectionCauchy (X : (D).Cauchy) : (D).Cauchy :=
  realScalarCauchy w hw0 hw1 (unitCoefficient w hw0 hw1 X) (unitCoefficientCauchy w hw0 hw1 X)
    (unitCauchy w hw0 hw1 half)

theorem unitProjectionCauchy_pairing (X : (D).Cauchy) (y : Completion w hw0 hw1 half) :
    B (Quotient.mk (D).completionSetoid (unitProjectionCauchy w hw0 hw1 X)) y =
      RCmul (B (Quotient.mk (D).completionSetoid X) u) (B u y) :=
  realScalarCauchy_pairing w hw0 hw1 _ _ (unitCauchy w hw0 hw1 half) y

theorem unitProjectionCauchy_congr (X Y : (D).Cauchy)
    (h : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (unitProjectionCauchy w hw0 hw1 X) =
      Quotient.mk (D).completionSetoid (unitProjectionCauchy w hw0 hw1 Y) := by
  apply completed_eq_of_pairings w hw0 hw1
  intro z
  rw [unitProjectionCauchy_pairing, unitProjectionCauchy_pairing, h]

def unitProjection : Completion w hw0 hw1 half → Completion w hw0 hw1 half :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid (unitProjectionCauchy w hw0 hw1 X))
    (fun X Y h => unitProjectionCauchy_congr w hw0 hw1 X Y (Quotient.sound h))

theorem unitProjection_mk (X : (D).Cauchy) :
    unitProjection w hw0 hw1 (Quotient.mk (D).completionSetoid X) =
      completedRealSmul w hw0 hw1 (unitCoefficient w hw0 hw1 X) (unitCoefficientCauchy w hw0 hw1 X) u := rfl

theorem unitProjection_pairing (x y : Completion w hw0 hw1 half) :
    B (unitProjection w hw0 hw1 x) y = RCmul (B x u) (B u y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => unitProjectionCauchy_pairing w hw0 hw1 X y

theorem unitProjection_coefficient (x : Completion w hw0 hw1 half) : B (unitProjection w hw0 hw1 x) u = B x u := by
  rw [unitProjection_pairing, completedUnit_norm_one, rc_mul_one]

theorem unitProjection_selfAdjoint (x y : Completion w hw0 hw1 half) :
    B (unitProjection w hw0 hw1 x) y = B x (unitProjection w hw0 hw1 y) := by
  rw [completedInner_symm w hw0 hw1 x, unitProjection_pairing, unitProjection_pairing,
    completedInner_symm w hw0 hw1 u y, completedInner_symm w hw0 hw1 u x, RCmul_comm]

theorem unitProjection_idempotent (x : Completion w hw0 hw1 half) :
    unitProjection w hw0 hw1 (unitProjection w hw0 hw1 x) = unitProjection w hw0 hw1 x := by
  apply completed_eq_of_pairings w hw0 hw1
  intro y
  rw [unitProjection_pairing, unitProjection_coefficient, unitProjection_pairing]

theorem unitProjection_unit : unitProjection w hw0 hw1 u = u := by
  apply completed_eq_of_pairings w hw0 hw1
  intro y
  rw [unitProjection_pairing, completedUnit_norm_one, rc_one_mul]

theorem unitProjection_zero_iff (x : Completion w hw0 hw1 half) :
    unitProjection w hw0 hw1 x = completedZero w hw0 hw1 half ↔ B x u = RCzero := by
  constructor
  · intro h
    rw [← unitProjection_coefficient w hw0 hw1 x, h, completedInner_zero_left]
  · intro h
    apply completed_eq_of_pairings w hw0 hw1
    intro y
    rw [unitProjection_pairing, h, rc_zero_mul, completedInner_zero_left]

theorem unitProjection_add (x y : Completion w hw0 hw1 half) :
    unitProjection w hw0 hw1 (completedAdd w hw0 hw1 x y) =
      completedAdd w hw0 hw1 (unitProjection w hw0 hw1 x) (unitProjection w hw0 hw1 y) := by
  apply completed_eq_of_pairings w hw0 hw1
  intro z
  rw [unitProjection_selfAdjoint, completedInner_add_left, completedInner_add_left,
    unitProjection_selfAdjoint, unitProjection_selfAdjoint]

theorem unitProjection_realSmul (s : CReal) (cs : QCauchy s.approx) (x : Completion w hw0 hw1 half) :
    unitProjection w hw0 hw1 (completedRealSmul w hw0 hw1 s cs x) =
      completedRealSmul w hw0 hw1 s cs (unitProjection w hw0 hw1 x) := by
  apply completed_eq_of_pairings w hw0 hw1
  intro y
  rw [unitProjection_selfAdjoint, completedInner_realSmul_left, completedInner_realSmul_left, unitProjection_selfAdjoint]

theorem unitProjection_inner (x y : Completion w hw0 hw1 half) :
    B (unitProjection w hw0 hw1 x) (unitProjection w hw0 hw1 y) = RCmul (B x u) (B u y) := by
  rw [unitProjection_pairing, completedInner_symm w hw0 hw1 u, unitProjection_coefficient, completedInner_symm w hw0 hw1 y u]

theorem unitProjection_norm_le (x : Completion w hw0 hw1 half) :
    RCle (B (unitProjection w hw0 hw1 x) (unitProjection w hw0 hw1 x)) (B x x) := by
  have h := completedInner_cauchySchwarz w hw0 hw1 x u
  rw [completedUnit_norm_one, rc_mul_one] at h
  rw [unitProjection_inner, completedInner_symm w hw0 hw1 u x]
  exact h

end YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitCoefficientCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitCoefficient_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjectionCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjectionCauchy_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjectionCauchy_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_mk
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_coefficient
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_selfAdjoint
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_idempotent
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_unit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_inner
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection.unitProjection_norm_le
