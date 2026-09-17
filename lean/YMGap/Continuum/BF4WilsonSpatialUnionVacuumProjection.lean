/-
# Projection and centering on the SAME completed Wilson union

For each supplied vector stream, its actual coefficient against the unit
has computed scalar Cauchy data. The proved real-scalar construction applies
that coefficient to the existing unit. Pairing separation proves that this
operation descends to the original vector quotient, without selecting a
representative or a modulus for a bare quotient real.

The projection and orthogonal centering use the SAME form, unit and
completed distance, and commute with original physical time. Centered time pairings
are exactly the existing connected scalars. These are fixed-spacing,
small-nome SU(2) results, not a canonical OS/QFT reconstruction, full Hilbert
completeness, changing-spacing control, or a continuum Hamiltonian gap.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionCompletedRealScalar
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
import YMGap.Continuum.BF4WilsonSpatialUnionTimeForm

namespace YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion (unitStage)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
  (completedZero completedInner_zero_left fixed_orthogonal_eq_zero)
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionRealScalarCauchy (realScalarCauchy)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedRealScalar
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance (completedDist)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap (completedCenteredScalar)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_sub_self rc_sub_add rc_add_zero)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem rc_mul_one (a : RC) : RCmul a (Quotient.mk crealSetoid cone) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CRealAlg.cmul_cone A)

private theorem rc_one_mul (a : RC) : RCmul (Quotient.mk crealSetoid cone) a = a := by
  rw [RCmul_comm, rc_mul_one]

private theorem rc_zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (A.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs

def unitCauchy : (D).Cauchy := (D).constant unitStage

def unitCoefficient (X : (D).Cauchy) : CReal :=
  representativeInner hw0 hw1 hsmall hd hs X (unitCauchy hw0 hw1 hsmall hd hs)

/-- The coefficient's modulus comes from the actual supplied mixed-pairing data. -/
def unitCoefficientCauchy (X : (D).Cauchy) :
    QCauchy (unitCoefficient hw0 hw1 hsmall hd hs X).approx :=
  representativeInnerCauchy hw0 hw1 hsmall hd hs X (unitCauchy hw0 hw1 hsmall hd hs)

theorem unitCoefficient_pin (X : (D).Cauchy) :
    Quotient.mk crealSetoid (unitCoefficient hw0 hw1 hsmall hd hs X) =
      B (Quotient.mk (D).completionSetoid X) U := rfl

/-- Actual scalar multiplication of the original constant unit stream. -/
def unitProjectionCauchy (X : (D).Cauchy) : (D).Cauchy :=
  realScalarCauchy hw0 hw1 hsmall hd hs
    (unitCoefficient hw0 hw1 hsmall hd hs X) (unitCoefficientCauchy hw0 hw1 hsmall hd hs X)
    (unitCauchy hw0 hw1 hsmall hd hs)

theorem unitProjectionCauchy_pairing (X : (D).Cauchy) (y : V) :
    B (Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 hsmall hd hs X)) y =
      RCmul (B (Quotient.mk (D).completionSetoid X) U) (B U y) := by
  change B (completedRealSmul hw0 hw1 hsmall hd hs
    (unitCoefficient hw0 hw1 hsmall hd hs X)
    (unitCoefficientCauchy hw0 hw1 hsmall hd hs X) U) y = _
  rw [completedInner_realSmul_left, unitCoefficient_pin]

theorem unitProjectionCauchy_congr (X Y : (D).Cauchy)
    (h : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 hsmall hd hs X) =
      Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 hsmall hd hs Y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [unitProjectionCauchy_pairing, unitProjectionCauchy_pairing, h]

/-- Choice-free descent to the SAME completed Wilson carrier. -/
def unitProjection : V → V :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 hsmall hd hs X))
    (fun X Y h => unitProjectionCauchy_congr hw0 hw1 hsmall hd hs X Y (Quotient.sound h))

local notation "P" => unitProjection hw0 hw1 hsmall hd hs

theorem unitProjection_mk (X : (D).Cauchy) :
    P (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 hsmall hd hs X) := rfl

theorem unitProjection_pairing (x y : V) :
    B (P x) y = RCmul (B x U) (B U y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => unitProjectionCauchy_pairing hw0 hw1 hsmall hd hs X y

theorem unitProjection_coefficient (x : V) : B (P x) U = B x U := by
  rw [unitProjection_pairing, completedUnit_norm_one, rc_mul_one]

theorem unitProjection_selfAdjoint (x y : V) : B (P x) y = B x (P y) := by
  rw [completedInner_symm hw0 hw1 hsmall hd hs x, unitProjection_pairing, unitProjection_pairing,
    completedInner_symm hw0 hw1 hsmall hd hs U y, completedInner_symm hw0 hw1 hsmall hd hs U x,
    RCmul_comm]

theorem unitProjection_idempotent (x : V) : P (P x) = P x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [unitProjection_pairing, unitProjection_coefficient, unitProjection_pairing]

theorem unitProjection_unit : P U = U := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [unitProjection_pairing, completedUnit_norm_one, rc_one_mul]

theorem unitProjection_inner (x y : V) : B (P x) (P y) = RCmul (B x U) (B U y) := by
  rw [unitProjection_pairing, completedInner_symm hw0 hw1 hsmall hd hs U,
    unitProjection_coefficient, completedInner_symm hw0 hw1 hsmall hd hs y U]

theorem unitProjection_norm_le (x : V) : RCle (B (P x) (P x)) (B x x) := by
  have h := completedInner_cauchySchwarz hw0 hw1 hsmall hd hs x U
  rw [completedUnit_norm_one, rc_mul_one] at h
  rw [unitProjection_inner, completedInner_symm hw0 hw1 hsmall hd hs U x]
  exact h

theorem time_unitProjection (n : Nat) (x : V) : T n (P x) = P x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [completedInner_time_balance, unitProjection_pairing, unitProjection_pairing,
    ← completedInner_time_balance hw0 hw1 hsmall hd hs n U y, completedUnit_fixed]

theorem unitProjection_time (n : Nat) (x : V) : P (T n x) = P x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [unitProjection_pairing, unitProjection_pairing, completedUnitCoefficient_time]

theorem unitProjection_zero_iff (x : V) : P x = Z ↔ B x U = RCzero := by
  constructor
  · intro h
    rw [← unitProjection_coefficient hw0 hw1 hsmall hd hs x, h, completedInner_zero_left]
  · intro h
    apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
    intro y
    rw [unitProjection_pairing, h, rc_zero_mul, completedInner_zero_left]

def center (x : V) : V := completedSub hw0 hw1 hsmall hd hs x (P x)

def centerCauchy (X : (D).Cauchy) : (D).Cauchy :=
  differenceCauchy hw0 hw1 hsmall hd hs X (unitProjectionCauchy hw0 hw1 hsmall hd hs X)

theorem center_mk (X : (D).Cauchy) :
    center hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (centerCauchy hw0 hw1 hsmall hd hs X) := rfl

local notation "C" => center hw0 hw1 hsmall hd hs

theorem center_pairing (x y : V) :
    B (C x) y = RCsub (B x y) (RCmul (B x U) (B U y)) := by
  unfold center
  rw [completedInner_sub_left, unitProjection_pairing]

theorem center_selfAdjoint (x y : V) : B (C x) y = B x (C y) := by
  unfold center
  rw [completedInner_sub_left, completedInner_sub_right, unitProjection_selfAdjoint]

theorem center_orthogonal (x : V) : B (C x) U = RCzero := by
  unfold center
  rw [completedInner_sub_left, unitProjection_coefficient, rc_sub_self]

theorem center_fixed_iff (x : V) : C x = x ↔ B x U = RCzero := by
  constructor
  · intro h
    rw [← h]
    exact center_orthogonal hw0 hw1 hsmall hd hs x
  · intro h
    unfold center
    rw [(unitProjection_zero_iff hw0 hw1 hsmall hd hs x).mpr h, completedSub_zero]

theorem center_idempotent (x : V) : C (C x) = C x :=
  (center_fixed_iff hw0 hw1 hsmall hd hs _).mpr (center_orthogonal hw0 hw1 hsmall hd hs x)

theorem center_decomposition (x : V) : completedAdd hw0 hw1 hsmall hd hs (C x) (P x) = x :=
  completedSub_add_cancel hw0 hw1 hsmall hd hs x (P x)

theorem center_add (x y : V) :
    C (completedAdd hw0 hw1 hsmall hd hs x y) = completedAdd hw0 hw1 hsmall hd hs (C x) (C y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [center_selfAdjoint, completedInner_add_left, completedInner_add_left,
    center_selfAdjoint, center_selfAdjoint]

theorem center_smul (c : Q') (x : V) :
    C (completedSmul hw0 hw1 hsmall hd hs c x) = completedSmul hw0 hw1 hsmall hd hs c (C x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [center_selfAdjoint, completedInner_smul_left, completedInner_smul_left, center_selfAdjoint]

theorem center_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    C (completedRealSmul hw0 hw1 hsmall hd hs s cs x) =
      completedRealSmul hw0 hw1 hsmall hd hs s cs (C x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [center_selfAdjoint, completedInner_realSmul_left,
    completedInner_realSmul_left, center_selfAdjoint]

theorem center_sub (x y : V) :
    C (completedSub hw0 hw1 hsmall hd hs x y) = completedSub hw0 hw1 hsmall hd hs (C x) (C y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [center_selfAdjoint, completedInner_sub_left, completedInner_sub_left,
    center_selfAdjoint, center_selfAdjoint]

theorem centered_inner (x y : V) :
    B (C x) (C y) = RCsub (B x y) (RCmul (B x U) (B U y)) := by
  rw [center_selfAdjoint, center_idempotent, ← center_selfAdjoint, center_pairing]

/-- Exact mixed Pythagoras for the existing Wilson form. -/
theorem orthogonal_decomposition_inner (x y : V) :
    RCadd (B (C x) (C y)) (B (P x) (P y)) = B x y := by
  rw [centered_inner, unitProjection_inner, rc_sub_add]

theorem center_norm_le (x : V) : RCle (B (C x) (C x)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (B (C x) (C x)))
    (completedInner_nonnegative hw0 hw1 hsmall hd hs (P x))
  rw [rc_add_zero, orthogonal_decomposition_inner] at h
  exact h

theorem center_nonexpansive (x y : V) :
    RCle (completedDist hw0 hw1 hsmall hd hs (C x) (C y))
      (completedDist hw0 hw1 hsmall hd hs x y) := by
  unfold completedDist
  rw [← center_sub]
  exact center_norm_le hw0 hw1 hsmall hd hs (completedSub hw0 hw1 hsmall hd hs x y)

theorem completedTime_center (n : Nat) (x : V) : T n (C x) = C (T n x) := by
  unfold center
  rw [completedTime_sub, time_unitProjection, unitProjection_time]

/-- Original connected scalars are pairings of the SAME centered vectors and time. -/
theorem centered_time_pairing (n : Nat) (x y : V) :
    B (C x) (T n (C y)) = completedCenteredScalar hw0 hw1 hsmall hd hs n x y := by
  rw [completedTime_center, centered_inner]
  unfold completedCenteredScalar
  rw [← completedInner_time_balance hw0 hw1 hsmall hd hs n U y, completedUnit_fixed]

/-- The strict bound identifies the complete two-step fixed space with this projection. -/
theorem fixed_twoStep_iff (x : V) : T 2 x = x ↔ x = P x := by
  constructor
  · intro ht
    have hz : C x = Z := fixed_orthogonal_eq_zero hw0 hw1 hsmall hd hs
      (C x) (center_orthogonal hw0 hw1 hsmall hd hs x) (by rw [completedTime_center, ht])
    have h := center_decomposition hw0 hw1 hsmall hd hs x
    rw [hz, completedZero_add] at h
    exact h.symm
  · intro hx
    rw [hx, time_unitProjection]

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
#print axioms unitProjection_inner
#print axioms unitProjection_norm_le
#print axioms time_unitProjection
#print axioms unitProjection_time
#print axioms unitProjection_zero_iff
#print axioms center
#print axioms centerCauchy
#print axioms center_mk
#print axioms center_pairing
#print axioms center_selfAdjoint
#print axioms center_orthogonal
#print axioms center_fixed_iff
#print axioms center_idempotent
#print axioms center_decomposition
#print axioms center_add
#print axioms center_smul
#print axioms center_realSmul
#print axioms center_sub
#print axioms centered_inner
#print axioms orthogonal_decomposition_inner
#print axioms center_norm_le
#print axioms center_nonexpansive
#print axioms completedTime_center
#print axioms centered_time_pairing
#print axioms fixed_twoStep_iff

end YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
