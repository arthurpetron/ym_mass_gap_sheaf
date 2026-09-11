/-
# Exact reserve decomposition of the truncated anchor face weight

The direct adjacent-even positivity route must use the complete face weight,
not one original character rank at a time.  This leaf performs the exact
rank-mixing rewrite

  1 + sum_{s=1}^K c_s U_s(x)
    = R_K + sum_{s=1}^K c_s ((s+1) + U_s(x)),

where `c_s = coeffW anchorCoupling s` and
`R_K = 1 - sum c_s (s+1)`.  The preceding reserve theorem proves
`R_K >= 1/2`.  Thus the only remaining local work is to replace each shifted
character `(s+1)+U_s` by its explicit even or odd Chebyshev/quaternion SOS.

No sign choice, square root, representation-rank selection, or classical
finite reindexing occurs here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceReserve

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceWeightDecomposition

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Cheb
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceReserve

local infix:50 " ≈ " => Q'.eqv

/-- The non-vacuum part of the truncated anchor class function, evaluated at
the rational class coordinate `x`. -/
def anchorExcitedCharacterValue (cutoff : Nat) (x : Q') : Q' :=
  finSum (fun index =>
    coeffW anchorCoupling (1 + index) * U (1 + index) x) cutoff

/-- The vacuum-normalized truncated anchor face weight. -/
def anchorTruncatedFaceClassValue (cutoff : Nat) (x : Q') : Q' :=
  (1 : Q') + anchorExcitedCharacterValue cutoff x

/-- The same face weight after transferring every excited dimension into a
single vacuum reserve. -/
def anchorReserveShiftedCharacterValue (cutoff : Nat) (x : Q') : Q' :=
  anchorVacuumReserve cutoff +
    finSum (fun index =>
      coeffW anchorCoupling (1 + index) *
        (dimQ (1 + index) + U (1 + index) x)) cutoff

/-- The shifted excited sum splits exactly into its dimension mass and its
original character part. -/
theorem anchorShiftedExcitedValue_eqv_mass_add_character
    (cutoff : Nat) (x : Q') :
    finSum (fun index =>
        coeffW anchorCoupling (1 + index) *
          (dimQ (1 + index) + U (1 + index) x)) cutoff ≈
      anchorExcitedCharacterDimensionMass cutoff +
        anchorExcitedCharacterValue cutoff x := by
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ (fun index =>
      Q'.mul_add_eqv
        (coeffW anchorCoupling (1 + index))
        (dimQ (1 + index)) (U (1 + index) x)) cutoff) ?_
  unfold anchorExcitedCharacterDimensionMass anchorExcitedCharacterValue
  exact finSum_add
    (fun index => coeffW anchorCoupling (1 + index) * dimQ (1 + index))
    (fun index => coeffW anchorCoupling (1 + index) * U (1 + index) x)
    cutoff

/-- **Exact local rank-mixing identity.**  The truncated face class function
is the positive vacuum reserve plus nonnegative coefficients multiplying the
dimension-shifted characters. -/
theorem anchorTruncatedFaceClassValue_eqv_reserveShifted
    (cutoff : Nat) (x : Q') :
    anchorTruncatedFaceClassValue cutoff x ≈
      anchorReserveShiftedCharacterValue cutoff x := by
  refine Q'.eqv_symm ?_
  unfold anchorReserveShiftedCharacterValue anchorTruncatedFaceClassValue
  calc
    anchorVacuumReserve cutoff +
        finSum (fun index =>
          coeffW anchorCoupling (1 + index) *
            (dimQ (1 + index) + U (1 + index) x)) cutoff
        ≈ anchorVacuumReserve cutoff +
            (anchorExcitedCharacterDimensionMass cutoff +
              anchorExcitedCharacterValue cutoff x) :=
          Q'.add_eqv_congr_left _ _ _
            (anchorShiftedExcitedValue_eqv_mass_add_character cutoff x)
    _ ≈ (anchorVacuumReserve cutoff +
            anchorExcitedCharacterDimensionMass cutoff) +
          anchorExcitedCharacterValue cutoff x :=
        Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    _ ≈ (1 : Q') + anchorExcitedCharacterValue cutoff x :=
        Q'.add_eqv_congr_right _ _ _
          (anchorVacuumReserve_add_excitedMass_eqv_one cutoff)

/-- The reserve coefficient used by the exact rewrite is constructively
nonnegative. -/
theorem anchorReserveShiftedCharacter_reserve_nonnegative (cutoff : Nat) :
    (0 : Q') ≤ anchorVacuumReserve cutoff :=
  anchorVacuumReserve_nonnegative cutoff

/-- In fact the exact rewrite retains a uniform half-unit of vacuum. -/
theorem anchorReserveShiftedCharacter_reserve_ge_half (cutoff : Nat) :
    dyad 1 ≤ anchorVacuumReserve cutoff :=
  anchorVacuumReserve_ge_half cutoff

/-- Every excited coefficient in the shifted rewrite is nonnegative. -/
theorem anchorReserveShiftedCharacter_coefficient_nonnegative
    (index : Nat) :
    (0 : Q') ≤ coeffW anchorCoupling (1 + index) :=
  coeffW_nonneg (by decide) (1 + index)

#print axioms anchorShiftedExcitedValue_eqv_mass_add_character
#print axioms anchorTruncatedFaceClassValue_eqv_reserveShifted
#print axioms anchorReserveShiftedCharacter_reserve_nonnegative
#print axioms anchorReserveShiftedCharacter_reserve_ge_half
#print axioms anchorReserveShiftedCharacter_coefficient_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceWeightDecomposition
