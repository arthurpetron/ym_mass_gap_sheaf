/-
# Invariant unit complement of the actual spatial Cauchy carrier

The actual completed pairing retains physical-time balance. Its unit is
fixed, so the orthogonal complement is preserved by every discrete time
advance. The SAME time semigroup restricts to this subtype.

The common small-nome rate rho(w)^2 bounds the two-step reflected form and,
by time balance, the one-step squared norm on this actual sector. Positivity
is asserted only at even times. No completed linear structure, metric
completeness, continuum Hamiltonian or physical mass calibration is assumed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedPosdef
import YMGap.Continuum.RCBilinearDifference

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm (spatialSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedPosdef
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedGap
  (completed_twoStep_form_gap completed_even_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate twoStepRate_lt_one)

open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "D" => spatialSeminorm hw0 hw1 base hsmall hd hs hb
local notation "B" => completedInner hw0 hw1 base hsmall hd hs hb
local notation "T" => spatialCompletedTime hw0 hw1 base hsmall hd hs hb
local notation "U" => spatialCompletedUnit hw0 hw1 base hsmall hd hs hb

/-- The same actual scalar pairing limits retain finite physical-time
balance on every pair of supplied Cauchy representatives. -/
theorem representativeInner_time_balance (n : Nat) (X Y : (D).Cauchy) :
    Equiv
      (representativeInner hw0 hw1 base hsmall hd hs hb
        ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy X) Y)
      (representativeInner hw0 hw1 base hsmall hd hs hb X
        ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy Y)) :=
  Equiv_of_limit_of_equal
    (fun k => spatialPairing_time_balance hw0 hw1 base hsmall hd hs hb n (X.seq k) (Y.seq k))
    (pairSequence_converges hw0 hw1 base hsmall hd hs hb
      ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy X) Y)
    (pairSequence_converges hw0 hw1 base hsmall hd hs hb X
      ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy Y))

theorem completedInner_time_balance (n : Nat) (x y : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    B (T n x) y = B x (T n y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_time_balance hw0 hw1 base hsmall hd hs hb n X Y)

/-- Unit coefficients are invariant because the actual completed unit is
fixed and the actual completed pairing satisfies time balance. -/
theorem completedUnitCoefficient_time (n : Nat) (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    B (T n x) U = B x U := by
  rw [completedInner_time_balance, spatialCompletedUnit_fixed]

theorem completedTime_preserves_orthogonal (n : Nat)
    (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb) (hx : B x U = RCzero) :
    B (T n x) U = RCzero :=
  (completedUnitCoefficient_time hw0 hw1 base hsmall hd hs hb n x).trans hx

/-- The unit-orthogonal sector of the SAME spatial completion and pairing. -/
def UnitComplement : Type :=
  {x : SpatialCompletion hw0 hw1 base hsmall hd hs hb // B x U = RCzero}

def unitComplementTime (n : Nat) (x : UnitComplement hw0 hw1 base hsmall hd hs hb) :
    UnitComplement hw0 hw1 base hsmall hd hs hb :=
  ⟨T n x.val, completedTime_preserves_orthogonal hw0 hw1 base hsmall hd hs hb n x.val x.property⟩

theorem unitComplementTime_val (n : Nat) (x : UnitComplement hw0 hw1 base hsmall hd hs hb) :
    (unitComplementTime hw0 hw1 base hsmall hd hs hb n x).val = T n x.val := rfl

theorem unitComplementTime_zero (x : UnitComplement hw0 hw1 base hsmall hd hs hb) :
    unitComplementTime hw0 hw1 base hsmall hd hs hb 0 x = x :=
  Subtype.ext (spatialCompletedTime_zero hw0 hw1 base hsmall hd hs hb x.val)

theorem unitComplementTime_add (m n : Nat) (x : UnitComplement hw0 hw1 base hsmall hd hs hb) :
    unitComplementTime hw0 hw1 base hsmall hd hs hb (m+n) x =
      unitComplementTime hw0 hw1 base hsmall hd hs hb m (unitComplementTime hw0 hw1 base hsmall hd hs hb n x) :=
  Subtype.ext (spatialCompletedTime_add hw0 hw1 base hsmall hd hs hb m n x.val)

/-- The canonical even-time transfer on this sector. Its form positivity is
the n=1 case of unitComplement_even_nonnegative below. -/
def twoStepTransfer (x : UnitComplement hw0 hw1 base hsmall hd hs hb) : UnitComplement hw0 hw1 base hsmall hd hs hb :=
  unitComplementTime hw0 hw1 base hsmall hd hs hb 2 x

/-- The strict form bound is inherited, with the original twoStepRate q^2.
Its positivity and strict inequality below one are already proved in
SpatialDenseGap; neither is a new premise here. -/
theorem unitComplement_twoStep_form_gap (x : UnitComplement hw0 hw1 base hsmall hd hs hb) :
    RCle (B x.val (unitComplementTime hw0 hw1 base hsmall hd hs hb 2 x).val)
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd)))
        (B x.val x.val)) :=
  completed_twoStep_form_gap hw0 hw1 base hsmall hd hs hb x.val x.property

/-- Site-reflected positivity is retained at even physical time only. -/
theorem unitComplement_even_nonnegative (n : Nat) (x : UnitComplement hw0 hw1 base hsmall hd hs hb) :
    RCnonneg (B x.val (unitComplementTime hw0 hw1 base hsmall hd hs hb (2*n) x).val) :=
  completed_even_nonnegative hw0 hw1 base hsmall hd hs hb n x.val x.property

/-- Time balance turns the two-step form bound into a strict one-step
squared-norm bound, without asserting positivity of one-step time. -/
theorem unitComplement_oneStep_norm_gap (x : UnitComplement hw0 hw1 base hsmall hd hs hb) :
    RCle (B (unitComplementTime hw0 hw1 base hsmall hd hs hb 1 x).val
        (unitComplementTime hw0 hw1 base hsmall hd hs hb 1 x).val)
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd)))
        (B x.val x.val)) := by
  have hdiag : B (T 1 x.val) (T 1 x.val) = B x.val (T 2 x.val) :=
    (completedInner_time_balance hw0 hw1 base hsmall hd hs hb 1 x.val (T 1 x.val)).trans
      (congrArg (fun y => B x.val y) (spatialCompletedTime_add hw0 hw1 base hsmall hd hs hb 1 1 x.val).symm)
  change RCle (B (T 1 x.val) (T 1 x.val))
    (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd))) (B x.val x.val))
  rw [hdiag]
  exact completed_twoStep_form_gap hw0 hw1 base hsmall hd hs hb x.val x.property

/-- The dimensionless margin is explicit and coupling-dependent. -/
def vacuumMargin (w : Q') (hd : heatRemainderBound w < 1) : Q' :=
  1 + -twoStepRate w hd

theorem vacuumMargin_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) :
    (0 : Q') < vacuumMargin w hd :=
  HKPos.one_sub_pos (twoStepRate_lt_one hw0 hd hs)

private theorem scalar_contraction_zero (rate : Q') (hrate : rate < (1 : Q'))
    (a : RC) (hnon : RCnonneg a)
    (hcontract : RCle a (RCmul (Quotient.mk crealSetoid (ofQ' rate)) a)) : a = RCzero := by
  revert hnon hcontract
  refine Quotient.inductionOn a ?_
  intro A hnon hcontract
  have hmargin : (0 : Q') < 1 + -rate := HKPos.one_sub_pos hrate
  have hproduct : leEv (mul A (ofQ' (1 + -rate))) (mul czero (ofQ' (1 + -rate))) := by
    intro epsilon he
    obtain ⟨N, hN⟩ := hcontract epsilon he
    refine ⟨N, fun n hn => ?_⟩
    have hsub := Q'.sub_le_of_le_add (hN n hn)
    have heq : Q'.eqv (A.approx n * (1 + -rate)) (A.approx n + -(rate * A.approx n)) :=
      RingNormaliser.poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.const 1) (.neg (.var 1))))
        (.add (.var 0) (.neg (.mul (.var 1) (.var 0))))
        (by decide) (fun i => if i = 0 then A.approx n else rate)
    have hz : Q'.eqv ((0 : Q') * (1 + -rate) + epsilon) epsilon :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
        (Q'.eqv_of_eq (Q'.zero_add' epsilon))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
      (Q'.le_trans' _ _ _ hsub (Q'.ge_of_eqv hz))
  have hzero : leEv A czero :=
    RCBilinearDifference.cancel_positive_factor (1 + -rate) hmargin
      (fun _ => Q'.le_refl' _) hproduct
  exact Quotient.sound (equiv_of_leEv_leEv hzero hnon)

/-- No nonzero two-step stationary excitation exists in this actual sector.
The cancelled factor is the explicit positive rate margin, never a norm. -/
theorem fixed_twoStep_complement_eq_zero
    (x : UnitComplement hw0 hw1 base hsmall hd hs hb) (hfixed : T 2 x.val = x.val) :
    x.val = completedZero hw0 hw1 base hsmall hd hs hb := by
  have h := completed_twoStep_form_gap hw0 hw1 base hsmall hd hs hb x.val x.property
  rw [hfixed] at h
  exact (completedInner_posdef hw0 hw1 base hsmall hd hs hb x.val).mp
    (scalar_contraction_zero (twoStepRate w hd) (twoStepRate_lt_one hw0 hd hs)
      (B x.val x.val) (completedInner_nonnegative hw0 hw1 base hsmall hd hs hb x.val) h)

theorem fixed_oneStep_complement_eq_zero
    (x : UnitComplement hw0 hw1 base hsmall hd hs hb) (hfixed : T 1 x.val = x.val) :
    x.val = completedZero hw0 hw1 base hsmall hd hs hb := by
  apply fixed_twoStep_complement_eq_zero hw0 hw1 base hsmall hd hs hb x
  have h := spatialCompletedTime_add hw0 hw1 base hsmall hd hs hb 1 1 x.val
  simpa only [hfixed] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.representativeInner_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.completedInner_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.completedUnitCoefficient_time
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.completedTime_preserves_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.UnitComplement
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.unitComplementTime
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.unitComplementTime_val
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.unitComplementTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.unitComplementTime_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.twoStepTransfer
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.unitComplement_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.unitComplement_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.unitComplement_oneStep_norm_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.vacuumMargin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.vacuumMargin_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.fixed_twoStep_complement_eq_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialUnitComplement.fixed_oneStep_complement_eq_zero
