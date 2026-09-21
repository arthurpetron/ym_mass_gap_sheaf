/-
# Vacuum projection on the SAME all-nome joint completion

Actual representative unit coefficients carry explicit scalar Cauchy data.
Their real multiples of the original unit descend without representative
selection. The resulting self-adjoint idempotent and its orthogonal center
decompose every vector in the existing JointCompletion. Their time pairings
are exactly the pre-existing completed connected scalars.

The actual strict two-step form bound identifies its fixed space with this
unit projection. Nome and width stay fixed. No continuous Hamiltonian,
metric completeness, spacing calibration, continuum or every-group theorem
is asserted; no legacy carrier is identified with this completion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar
import YMGap.Continuum.CRealSeminormPairingPosdef

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointVacuumProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap
  (completedCenteredScalar completed_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarCauchy (realScalarCauchy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream
  (mean meanCauchy centeredStream centeredVector)
open YMGap.Continuum.BF4SpatialUnionBilinear
  (rc_sub_self rc_sub_add rc_sub_zero rc_add_zero)

private theorem rc_mul_one (a : RC) : RCmul a (Quotient.mk crealSetoid cone) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CRealAlg.cmul_cone A)

private theorem rc_one_mul (a : RC) : RCmul (Quotient.mk crealSetoid cone) a = a := by
  rw [RCmul_comm, rc_mul_one]

private theorem rc_zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (A.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width
local notation "Z" => completedZero hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width

def unitCauchy : (D).Cauchy := (D).constant (unit width)

def unitCoefficient (X : (D).Cauchy) : CReal :=
  representativeInner hw0 hw1 width X (unitCauchy hw0 hw1 width)

/-- The coefficient's modulus comes from the actual supplied mixed-pairing data. -/
def unitCoefficientCauchy (X : (D).Cauchy) :
    QCauchy (unitCoefficient hw0 hw1 width X).approx :=
  representativeInnerCauchy hw0 hw1 width X (unitCauchy hw0 hw1 width)

theorem unitCoefficient_pin (X : (D).Cauchy) :
    Quotient.mk crealSetoid (unitCoefficient hw0 hw1 width X) =
      B (Quotient.mk (D).completionSetoid X) U := rfl

/-- Actual scalar multiplication of the original constant unit stream. -/
def unitProjectionCauchy (X : (D).Cauchy) : (D).Cauchy :=
  realScalarCauchy hw0 hw1 width
    (unitCoefficient hw0 hw1 width X) (unitCoefficientCauchy hw0 hw1 width X)
    (unitCauchy hw0 hw1 width)

theorem unitProjectionCauchy_pairing (X : (D).Cauchy) (y : V) :
    B (Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 width X)) y =
      RCmul (B (Quotient.mk (D).completionSetoid X) U) (B U y) := by
  change B (completedRealSmul hw0 hw1 width
    (unitCoefficient hw0 hw1 width X)
    (unitCoefficientCauchy hw0 hw1 width X) U) y = _
  rw [completedInner_realSmul_left, unitCoefficient_pin]

theorem unitProjectionCauchy_congr (X Y : (D).Cauchy)
    (h : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 width X) =
      Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 width Y) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro z
  rw [unitProjectionCauchy_pairing, unitProjectionCauchy_pairing, h]

/-- Choice-free descent to the SAME all-nome joint carrier. -/
def unitProjection : V → V :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 width X))
    (fun X Y h => unitProjectionCauchy_congr hw0 hw1 width X Y (Quotient.sound h))

local notation "P" => unitProjection hw0 hw1 width

theorem unitProjection_mk (X : (D).Cauchy) :
    P (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 width X) := rfl

theorem unitProjection_pairing (x y : V) :
    B (P x) y = RCmul (B x U) (B U y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => unitProjectionCauchy_pairing hw0 hw1 width X y

theorem unitProjection_coefficient (x : V) : B (P x) U = B x U := by
  rw [unitProjection_pairing, completedUnit_norm_one, rc_mul_one]

theorem unitProjection_selfAdjoint (x y : V) : B (P x) y = B x (P y) := by
  rw [completedInner_symm hw0 hw1 width x, unitProjection_pairing, unitProjection_pairing,
    completedInner_symm hw0 hw1 width U y, completedInner_symm hw0 hw1 width U x,
    RCmul_comm]

theorem unitProjection_idempotent (x : V) : P (P x) = P x := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro y
  rw [unitProjection_pairing, unitProjection_coefficient, unitProjection_pairing]

theorem unitProjection_unit : P U = U := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro y
  rw [unitProjection_pairing, completedUnit_norm_one, rc_one_mul]

theorem unitProjection_inner (x y : V) : B (P x) (P y) = RCmul (B x U) (B U y) := by
  rw [unitProjection_pairing, completedInner_symm hw0 hw1 width U,
    unitProjection_coefficient, completedInner_symm hw0 hw1 width y U]

theorem unitProjection_norm_le (x : V) : RCle (B (P x) (P x)) (B x x) := by
  have h := completedInner_cauchySchwarz hw0 hw1 width x U
  rw [completedUnit_norm_one, rc_mul_one] at h
  rw [unitProjection_inner, completedInner_symm hw0 hw1 width U x]
  exact h

theorem time_unitProjection (n : Nat) (x : V) : T n (P x) = P x := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro y
  rw [completedInner_time_balance, unitProjection_pairing, unitProjection_pairing,
    ← completedInner_time_balance hw0 hw1 width n U y, jointCompletedUnit_fixed]

theorem unitProjection_time (n : Nat) (x : V) : P (T n x) = P x := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro y
  rw [unitProjection_pairing, unitProjection_pairing, completedUnitCoefficient_time]

theorem unitProjection_zero_iff (x : V) : P x = Z ↔ B x U = RCzero := by
  constructor
  · intro h
    rw [← unitProjection_coefficient hw0 hw1 width x, h, completedInner_zero_left]
  · intro h
    apply completed_eq_of_pairings hw0 hw1 width
    intro y
    rw [unitProjection_pairing, h, rc_zero_mul, completedInner_zero_left]

def center (x : V) : V := completedSub hw0 hw1 width x (P x)

def centerCauchy (X : (D).Cauchy) : (D).Cauchy :=
  (addition hw0 hw1 width).mapCauchy X
    ((scalarContinuous hw0 hw1 width (-1)).mapCauchy (unitProjectionCauchy hw0 hw1 width X))

theorem center_mk (X : (D).Cauchy) :
    center hw0 hw1 width (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (centerCauchy hw0 hw1 width X) := rfl

local notation "C" => center hw0 hw1 width

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
    exact center_orthogonal hw0 hw1 width x
  · intro h
    unfold center
    apply completed_eq_of_pairings hw0 hw1 width
    intro y
    rw [completedInner_sub_left, (unitProjection_zero_iff hw0 hw1 width x).mpr h,
      completedInner_zero_left, rc_sub_zero]

theorem center_idempotent (x : V) : C (C x) = C x :=
  (center_fixed_iff hw0 hw1 width _).mpr (center_orthogonal hw0 hw1 width x)

theorem center_decomposition (x : V) : completedAdd hw0 hw1 width (C x) (P x) = x :=
  completedSub_add_cancel hw0 hw1 width x (P x)

theorem center_add (x y : V) :
    C (completedAdd hw0 hw1 width x y) = completedAdd hw0 hw1 width (C x) (C y) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro z
  rw [center_selfAdjoint, completedInner_add_left, completedInner_add_left,
    center_selfAdjoint, center_selfAdjoint]

theorem center_smul (c : Q') (x : V) :
    C (completedSmul hw0 hw1 width c x) = completedSmul hw0 hw1 width c (C x) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro y
  rw [center_selfAdjoint, completedInner_smul_left, completedInner_smul_left, center_selfAdjoint]

theorem center_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    C (completedRealSmul hw0 hw1 width s cs x) =
      completedRealSmul hw0 hw1 width s cs (C x) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro y
  rw [center_selfAdjoint, completedInner_realSmul_left,
    completedInner_realSmul_left, center_selfAdjoint]

theorem center_sub (x y : V) :
    C (completedSub hw0 hw1 width x y) = completedSub hw0 hw1 width (C x) (C y) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro z
  rw [center_selfAdjoint, completedInner_sub_left, completedInner_sub_left,
    center_selfAdjoint, center_selfAdjoint]

theorem centered_inner (x y : V) :
    B (C x) (C y) = RCsub (B x y) (RCmul (B x U) (B U y)) := by
  rw [center_selfAdjoint, center_idempotent, ← center_selfAdjoint, center_pairing]

/-- Exact mixed Pythagoras for the existing joint form. -/
theorem orthogonal_decomposition_inner (x y : V) :
    RCadd (B (C x) (C y)) (B (P x) (P y)) = B x y := by
  rw [centered_inner, unitProjection_inner, rc_sub_add]

theorem center_norm_le (x : V) : RCle (B (C x) (C x)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (B (C x) (C x)))
    (completedInner_nonnegative hw0 hw1 width (P x))
  rw [rc_add_zero, orthogonal_decomposition_inner] at h
  exact h

theorem completedTime_center (n : Nat) (x : V) : T n (C x) = C (T n x) := by
  unfold center
  rw [completedTime_sub, time_unitProjection, unitProjection_time]

/-- Original connected scalars are pairings of the SAME centered vectors and time. -/
theorem centered_time_pairing (n : Nat) (x y : V) :
    B (C x) (T n (C y)) = completedCenteredScalar hw0 hw1 width n x y := by
  rw [completedTime_center, centered_inner]
  unfold completedCenteredScalar
  rw [← completedInner_time_balance hw0 hw1 width n U y, jointCompletedUnit_fixed]

/-- On an original dense span, the vacuum coefficient is its original joint mean. -/
theorem unitProjection_embedSpan (x : PhysicalSpan width) :
    P (jointEmbedSpan hw0 hw1 width x) =
      completedRealSmul hw0 hw1 width (mean hw0 hw1 width x)
        (meanCauchy hw0 hw1 width x) U := by
  change completedRealSmul hw0 hw1 width
    (unitCoefficient hw0 hw1 width ((D).constant x))
    (unitCoefficientCauchy hw0 hw1 width ((D).constant x)) U = _
  exact completedRealSmul_congr hw0 hw1 width _ _ _ _
    (representativeInner_constant hw0 hw1 width x (unit width)) U

/-- Literal original centering, with both Cauchy constructions retained. -/
theorem centeredVector_sub_mean (x : PhysicalSpan width) :
    centeredVector hw0 hw1 width x =
      completedSub hw0 hw1 width (jointEmbedSpan hw0 hw1 width x)
        (completedRealSmul hw0 hw1 width (mean hw0 hw1 width x)
          (meanCauchy hw0 hw1 width x) U) := by
  apply completion_eq_of_pointwise hw0 hw1 width
  intro n stage test
  exact Equiv.refl _

/-- The new all-vector projection agrees with the previous actual dense centering. -/
theorem center_embedSpan (x : PhysicalSpan width) :
    C (jointEmbedSpan hw0 hw1 width x) = centeredVector hw0 hw1 width x := by
  unfold center
  rw [unitProjection_embedSpan, centeredVector_sub_mean]

/-- A stationary orthogonal vector vanishes by the actual strict form bound. -/
theorem fixed_orthogonal_eq_zero (x : V) (hx : B x U = RCzero) (ht : T 2 x = x) :
    x = Z := by
  have h := completed_twoStep_form_gap hw0 hw1 width x hx
  rw [ht] at h
  exact (completedInner_posdef hw0 hw1 width x).mp
    (CRealSeminormPairingCompletion.scalar_contraction_zero (twoStepRate hw0 hw1 width)
      (twoStepRate_lt_one hw0 hw1 width) (B x x)
      (completedInner_nonnegative hw0 hw1 width x) h)

/-- The strict bound identifies the complete two-step fixed space with this projection. -/
theorem fixed_twoStep_iff (x : V) : T 2 x = x ↔ x = P x := by
  constructor
  · intro ht
    have hz : C x = Z := fixed_orthogonal_eq_zero hw0 hw1 width
      (C x) (center_orthogonal hw0 hw1 width x) (by rw [completedTime_center, ht])
    have h := center_decomposition hw0 hw1 width x
    rw [hz, completedZero_add] at h
    exact h.symm
  · intro hx
    rw [hx, time_unitProjection]

/-- A supplied fixed representative returns its scalar and scalar modulus as data. -/
def fixedScalarWitness (X : (D).Cauchy)
    (hX : T 2 (Quotient.mk (D).completionSetoid X) = Quotient.mk (D).completionSetoid X) :
    Σ' s : CReal, Σ' cs : QCauchy s.approx,
      Quotient.mk (D).completionSetoid X = completedRealSmul hw0 hw1 width s cs U :=
  ⟨unitCoefficient hw0 hw1 width X, unitCoefficientCauchy hw0 hw1 width X,
    (fixed_twoStep_iff hw0 hw1 width _).mp hX⟩

/-- Unit coefficient one singles out the actual unit inside the two-step fixed space. -/
theorem fixed_unitCoefficient_one (x : V) (ht : T 2 x = x)
    (hc : B x U = Quotient.mk crealSetoid cone) : x = U := by
  apply ((fixed_twoStep_iff hw0 hw1 width x).mp ht).trans
  apply completed_eq_of_pairings hw0 hw1 width
  intro y
  rw [unitProjection_pairing, hc, rc_one_mul]

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
#print axioms completedTime_center
#print axioms centered_time_pairing
#print axioms unitProjection_embedSpan
#print axioms centeredVector_sub_mean
#print axioms center_embedSpan
#print axioms fixed_orthogonal_eq_zero
#print axioms fixed_twoStep_iff
#print axioms fixedScalarWitness
#print axioms fixed_unitCoefficient_one

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointVacuumProjection
