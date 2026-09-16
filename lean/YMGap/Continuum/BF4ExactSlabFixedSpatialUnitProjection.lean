/-
# Constructed projection onto the actual fixed-spatial completed unit

A supplied physical Cauchy representative X determines its coefficient
against the original normalized unit by the SAME completed pairing limit.
The existing representativeInnerCauchy supplies explicit approximation data
for that coefficient. Scaling the constant original-unit stream constructs
the projected representative. Pairing separation gives quotient descent;
neither a scalar nor a vector representative is selected from a quotient.

The resulting map preserves the unit and is additive, self-adjoint,
idempotent and norm-contractive for this actual reflected form. Real
scaling is used only with supplied QCauchy data for its approximation
stream. Nome, spatial width and retained heat stage stay fixed. Although
the original unit is already fixed by physical time, this construction
does not assert its uniqueness or isolation, a strict gap, metric
completeness or a continuum vacuum theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (seminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (Completion unit completedUnit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef (completedZero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialRealScalarCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar

private theorem rc_mul_one (a : RC) : RCmul a (Quotient.mk crealSetoid cone) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CRealAlg.cmul_cone A)

private theorem rc_one_mul (a : RC) : RCmul (Quotient.mk crealSetoid cone) a = a := by
  rw [RCmul_comm, rc_mul_one]

private theorem rc_zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul (A.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage
local notation "u" => completedUnit hw0 hw1 width stage
local notation "B" => completedInner hw0 hw1 width stage

/-- The actual physical unit, represented by its constant Cauchy stream. -/
def unitCauchy : (D).Cauchy :=
  (D).constant (unit width)

/-- The original mixed-pairing limit against the constant unit stream. -/
def unitCoefficient (X : (D).Cauchy) : CReal :=
  representativeInner hw0 hw1 width stage X (unitCauchy hw0 hw1 width stage)

/-- Type-level approximation data for the coefficient that is actually used. -/
def unitCoefficientCauchy (X : (D).Cauchy) :
    QCauchy (unitCoefficient hw0 hw1 width stage X).approx :=
  representativeInnerCauchy hw0 hw1 width stage X (unitCauchy hw0 hw1 width stage)

theorem unitCoefficient_pin (X : (D).Cauchy) :
    Quotient.mk crealSetoid (unitCoefficient hw0 hw1 width stage X) =
      B (Quotient.mk (D).completionSetoid X) u := rfl

/-- Projection is computed on supplied representatives by actual real scaling. -/
def unitProjectionCauchy (X : (D).Cauchy) : (D).Cauchy :=
  realScalarCauchy hw0 hw1 width stage
    (unitCoefficient hw0 hw1 width stage X) (unitCoefficientCauchy hw0 hw1 width stage X)
    (unitCauchy hw0 hw1 width stage)

theorem unitProjectionCauchy_pairing (X : (D).Cauchy) (y : Completion hw0 hw1 width stage) :
    B (Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 width stage X)) y =
      RCmul (B (Quotient.mk (D).completionSetoid X) u) (B u y) :=
  realScalarCauchy_pairing hw0 hw1 width stage _ _ (unitCauchy hw0 hw1 width stage) y

theorem unitProjectionCauchy_congr (X Y : (D).Cauchy)
    (h : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 width stage X) =
      Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 width stage Y) := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro z
  rw [unitProjectionCauchy_pairing, unitProjectionCauchy_pairing, h]

/-- Choice-free descent to the SAME physical Cauchy quotient. -/
def unitProjection : Completion hw0 hw1 width stage → Completion hw0 hw1 width stage :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 width stage X))
    (fun X Y h => unitProjectionCauchy_congr hw0 hw1 width stage X Y (Quotient.sound h))

theorem unitProjection_mk (X : (D).Cauchy) :
    unitProjection hw0 hw1 width stage (Quotient.mk (D).completionSetoid X) =
      completedRealSmul hw0 hw1 width stage
        (unitCoefficient hw0 hw1 width stage X) (unitCoefficientCauchy hw0 hw1 width stage X) u := rfl

theorem unitProjection_pairing (x y : Completion hw0 hw1 width stage) :
    B (unitProjection hw0 hw1 width stage x) y = RCmul (B x u) (B u y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => unitProjectionCauchy_pairing hw0 hw1 width stage X y

theorem unitProjection_coefficient (x : Completion hw0 hw1 width stage) :
    B (unitProjection hw0 hw1 width stage x) u = B x u := by
  rw [unitProjection_pairing, completedUnit_norm_one, rc_mul_one]

/-- Self-adjointness means this exact pairing identity on the existing carrier. -/
theorem unitProjection_selfAdjoint (x y : Completion hw0 hw1 width stage) :
    B (unitProjection hw0 hw1 width stage x) y = B x (unitProjection hw0 hw1 width stage y) := by
  rw [completedInner_symm hw0 hw1 width stage x, unitProjection_pairing, unitProjection_pairing,
    completedInner_symm hw0 hw1 width stage u y, completedInner_symm hw0 hw1 width stage u x,
    RCmul_comm]

theorem unitProjection_idempotent (x : Completion hw0 hw1 width stage) :
    unitProjection hw0 hw1 width stage (unitProjection hw0 hw1 width stage x) =
      unitProjection hw0 hw1 width stage x := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro y
  rw [unitProjection_pairing, unitProjection_coefficient, unitProjection_pairing]

theorem unitProjection_unit : unitProjection hw0 hw1 width stage u = u := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro y
  rw [unitProjection_pairing, completedUnit_norm_one, rc_one_mul]

theorem unitProjection_zero_iff (x : Completion hw0 hw1 width stage) :
    unitProjection hw0 hw1 width stage x = completedZero hw0 hw1 width stage ↔ B x u = RCzero := by
  constructor
  · intro h
    rw [← unitProjection_coefficient hw0 hw1 width stage x, h, completedInner_zero_left]
  · intro h
    apply completed_eq_of_pairings hw0 hw1 width stage
    intro y
    rw [unitProjection_pairing, h, rc_zero_mul, completedInner_zero_left]

theorem unitProjection_add (x y : Completion hw0 hw1 width stage) :
    unitProjection hw0 hw1 width stage (completedAdd hw0 hw1 width stage x y) =
      completedAdd hw0 hw1 width stage
        (unitProjection hw0 hw1 width stage x) (unitProjection hw0 hw1 width stage y) := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro z
  rw [unitProjection_selfAdjoint, completedInner_add_left, completedInner_add_left,
    unitProjection_selfAdjoint, unitProjection_selfAdjoint]

theorem unitProjection_realSmul (s : CReal) (cs : QCauchy s.approx)
    (x : Completion hw0 hw1 width stage) :
    unitProjection hw0 hw1 width stage (completedRealSmul hw0 hw1 width stage s cs x) =
      completedRealSmul hw0 hw1 width stage s cs (unitProjection hw0 hw1 width stage x) := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro y
  rw [unitProjection_selfAdjoint, completedInner_realSmul_left, completedInner_realSmul_left,
    unitProjection_selfAdjoint]

theorem unitProjection_inner (x y : Completion hw0 hw1 width stage) :
    B (unitProjection hw0 hw1 width stage x) (unitProjection hw0 hw1 width stage y) =
      RCmul (B x u) (B u y) := by
  rw [unitProjection_pairing, completedInner_symm hw0 hw1 width stage u,
    unitProjection_coefficient, completedInner_symm hw0 hw1 width stage y u]

/-- Constant-one norm contraction onto the normalized unit, not a strict gap. -/
theorem unitProjection_norm_le (x : Completion hw0 hw1 width stage) :
    RCle (B (unitProjection hw0 hw1 width stage x) (unitProjection hw0 hw1 width stage x))
      (B x x) := by
  have h := completedInner_cauchySchwarz hw0 hw1 width stage x u
  rw [completedUnit_norm_one, rc_mul_one] at h
  rw [unitProjection_inner, completedInner_symm hw0 hw1 width stage u x]
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitCoefficientCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitCoefficient_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjectionCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjectionCauchy_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjectionCauchy_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_coefficient
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_selfAdjoint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_idempotent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_inner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection.unitProjection_norm_le
