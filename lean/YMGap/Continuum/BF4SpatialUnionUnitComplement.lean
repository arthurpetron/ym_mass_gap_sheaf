/-
# Invariant strict unit complement on the actual spatial union completion

Original physical time preserves orthogonality to the normalized unit.
Its one-step squared-norm bound is the two-step form bound by time balance.
Positive definiteness and cancellation of the explicit positive rate margin
exclude nonzero stationary vectors in this sector. No completed scalar
projection is assumed: full stationary-vacuum-span characterization and
continuum Hamiltonian identification remain separate obligations.
-/

import YMGap.Continuum.BF4SpatialUnionGeometry
import YMGap.Continuum.BF4SpatialUnionCompletedGap

namespace YMGap.Continuum.BF4SpatialUnionUnitComplement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData (completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4SpatialUnionGeometry
open YMGap.Continuum.BF4SpatialUnionCompletedGap
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate twoStepRate_lt_one)
open YMGap.Continuum.CRealSeminormPairingCompletion (scalar_contraction_zero)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

theorem completedTime_preserves_orthogonal (n : Nat)
    (x : UnionCompletion hw0 hw1 hsmall hd hs) (hx : B x U = RCzero) :
    B (T n x) U = RCzero :=
  (completedUnitCoefficient_time hw0 hw1 hsmall hd hs n x).trans hx

/-- The actual unit complement in the SAME union carrier and completed form. -/
def UnitComplement : Type := { x : UnionCompletion hw0 hw1 hsmall hd hs // B x U = RCzero }

def unitComplementTime (n : Nat) (x : UnitComplement hw0 hw1 hsmall hd hs) :
    UnitComplement hw0 hw1 hsmall hd hs :=
  ⟨T n x.val, completedTime_preserves_orthogonal hw0 hw1 hsmall hd hs n x.val x.property⟩

theorem unitComplementTime_val (n : Nat) (x : UnitComplement hw0 hw1 hsmall hd hs) :
    (unitComplementTime hw0 hw1 hsmall hd hs n x).val = T n x.val := rfl

theorem unitComplementTime_zero (x : UnitComplement hw0 hw1 hsmall hd hs) :
    unitComplementTime hw0 hw1 hsmall hd hs 0 x = x :=
  Subtype.ext (completedTime_zero hw0 hw1 hsmall hd hs x.val)

theorem unitComplementTime_add (m n : Nat) (x : UnitComplement hw0 hw1 hsmall hd hs) :
    unitComplementTime hw0 hw1 hsmall hd hs (m+n) x =
      unitComplementTime hw0 hw1 hsmall hd hs m (unitComplementTime hw0 hw1 hsmall hd hs n x) :=
  Subtype.ext (completedTime_add hw0 hw1 hsmall hd hs m n x.val)

/-- Two actual discrete physical-time steps, not heat-bath dynamics. -/
def twoStepTransfer (x : UnitComplement hw0 hw1 hsmall hd hs) : UnitComplement hw0 hw1 hsmall hd hs :=
  unitComplementTime hw0 hw1 hsmall hd hs 2 x

theorem unitComplement_twoStep_form_gap (x : UnitComplement hw0 hw1 hsmall hd hs) :
    RCle (B x.val (twoStepTransfer hw0 hw1 hsmall hd hs x).val)
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd))) (B x.val x.val)) :=
  completed_twoStep_form_gap hw0 hw1 hsmall hd hs x.val x.property

theorem unitComplement_even_nonnegative (n : Nat) (x : UnitComplement hw0 hw1 hsmall hd hs) :
    RCnonneg (B x.val (unitComplementTime hw0 hw1 hsmall hd hs (2*n) x).val) :=
  completed_even_nonnegative hw0 hw1 hsmall hd hs n x.val x.property

/-- Time balance turns the strict two-step form bound into one-step norm decay. -/
theorem unitComplement_oneStep_norm_gap (x : UnitComplement hw0 hw1 hsmall hd hs) :
    RCle (B (T 1 x.val) (T 1 x.val))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate w hd))) (B x.val x.val)) := by
  rw [completedInner_time_balance, ← completedTime_add]
  exact completed_twoStep_form_gap hw0 hw1 hsmall hd hs x.val x.property

/-- The margin 1-q, not the potentially zero norm, is cancelled. -/
theorem fixed_twoStep_complement_eq_zero (x : UnitComplement hw0 hw1 hsmall hd hs)
    (hfixed : T 2 x.val = x.val) : x.val = completedZero hw0 hw1 hsmall hd hs := by
  have h := completed_twoStep_form_gap hw0 hw1 hsmall hd hs x.val x.property
  rw [hfixed] at h
  exact (completedInner_posdef hw0 hw1 hsmall hd hs x.val).mp
    (scalar_contraction_zero (twoStepRate w hd) (twoStepRate_lt_one hw0 hd hs)
      (B x.val x.val) (completedInner_nonnegative hw0 hw1 hsmall hd hs x.val) h)

theorem fixed_oneStep_complement_eq_zero (x : UnitComplement hw0 hw1 hsmall hd hs)
    (hfixed : T 1 x.val = x.val) : x.val = completedZero hw0 hw1 hsmall hd hs := by
  apply fixed_twoStep_complement_eq_zero hw0 hw1 hsmall hd hs x
  change T (1+1) x.val = x.val
  rw [completedTime_add, hfixed, hfixed]

end YMGap.Continuum.BF4SpatialUnionUnitComplement

#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.completedTime_preserves_orthogonal
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.UnitComplement
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.unitComplementTime
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.unitComplementTime_val
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.unitComplementTime_zero
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.unitComplementTime_add
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.twoStepTransfer
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.unitComplement_twoStep_form_gap
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.unitComplement_even_nonnegative
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.unitComplement_oneStep_norm_gap
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.fixed_twoStep_complement_eq_zero
#print axioms YMGap.Continuum.BF4SpatialUnionUnitComplement.fixed_oneStep_complement_eq_zero
