/-
# Uniform vacuum reserve for the anchor face weight

The corrected adjacent-even positivity route works directly with the full
active quadratic and is allowed to mix representation ranks.  Its first local
ingredient is the exact decomposition of the truncated anchor face weight

    1 + sum_{s=1}^K coeffW(anchor,s) chi_s

into a vacuum reserve and the shifted positive packets
`coeffW(anchor,s) * (dimQ s + chi_s)`.  The scalar mass subtracted from the
vacuum is therefore `sum coeffW(anchor,s) * dimQ s`.

This leaf identifies that mass with the already controlled degree-two
Casimir tail.  The existing anchor estimate makes it at most `1/2`, so the
vacuum reserve is constructively nonnegative and in fact at least `1/2`,
uniformly in the cutoff.  No representation rank is selected and no square
root is introduced.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceResummedKernel

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceReserve

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceResummedKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact identification with the degree-two Casimir tail -/

/-- Multiplying the heat-kernel character coefficient by one further
representation dimension is exactly the degree-two Casimir tail term. -/
theorem anchorExcitedCharacterDimensionTerm_eqv_tailTerm (fixed : Nat) :
    coeffW anchorCoupling fixed * dimQ fixed ≈
      tailTerm anchorCoupling 2 fixed := by
  unfold coeffW dimQ tailTerm
  rw [Nat.pow_two]
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat (fixed + 1))
        (qpow anchorCoupling (c4 fixed)) (Q'.ofNat (fixed + 1)))
      (Q'.mul_eqv_congr_left (Q'.ofNat (fixed + 1)) _ _
        (Q'.mul_comm_eqv
          (qpow anchorCoupling (c4 fixed))
          (Q'.ofNat (fixed + 1))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (Q'.ofNat (fixed + 1)) (Q'.ofNat (fixed + 1))
      (qpow anchorCoupling (c4 fixed)))) ?_
  exact Q'.mul_eqv_congr_right _ _
    (qpow anchorCoupling (c4 fixed))
    (Q'.eqv_symm
      (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv
        (fixed + 1) (fixed + 1)))

/-- The total non-vacuum dimension mass in the first `cutoff`
representations `s = 1, ..., cutoff`. -/
def anchorExcitedCharacterDimensionMass (cutoff : Nat) : Q' :=
  finSum (fun index =>
    coeffW anchorCoupling (1 + index) * dimQ (1 + index)) cutoff

/-- The excited dimension mass is exactly, up to rational equivalence, the
degree-two anchor tail window beginning at the first excited rank. -/
theorem anchorExcitedCharacterDimensionMass_eqv_tailWindow (cutoff : Nat) :
    anchorExcitedCharacterDimensionMass cutoff ≈
      tailWindow anchorCoupling 2 1 cutoff := by
  unfold anchorExcitedCharacterDimensionMass tailWindow
  exact RationalTail.finSum_eqv_congr _ _
    (fun index =>
      anchorExcitedCharacterDimensionTerm_eqv_tailTerm (1 + index)) cutoff

/-! ## 2. Uniform half-budget and the vacuum reserve -/

private theorem finSum_nonnegative_local
    (value : Nat → Q') (hvalue : ∀ index, (0 : Q') ≤ value index) :
    ∀ count, (0 : Q') ≤ finSum value count
  | 0 => Q'.le_refl' 0
  | count + 1 => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (finSum_nonnegative_local value hvalue count)
        (hvalue count)

theorem anchorExcitedCharacterDimensionMass_nonnegative (cutoff : Nat) :
    (0 : Q') ≤ anchorExcitedCharacterDimensionMass cutoff := by
  unfold anchorExcitedCharacterDimensionMass
  apply finSum_nonnegative_local
  intro index
  exact Q'.mul_nonneg _ _
    (coeffW_nonneg (by decide) (1 + index))
    (dimQ_nonneg (1 + index))

/-- The total excited dimension mass consumes at most one half of the
vacuum coefficient, uniformly in the representation cutoff. -/
theorem anchorExcitedCharacterDimensionMass_le_half (cutoff : Nat) :
    anchorExcitedCharacterDimensionMass cutoff ≤ dyad 1 := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (anchorExcitedCharacterDimensionMass_eqv_tailWindow cutoff))
    (anchorWeightedExcitedFaceTail_le_half cutoff)

theorem anchorExcitedCharacterDimensionMass_le_one (cutoff : Nat) :
    anchorExcitedCharacterDimensionMass cutoff ≤ (1 : Q') := by
  exact Q'.le_trans' _ _ _
    (anchorExcitedCharacterDimensionMass_le_half cutoff) (by
      unfold dyad YMGap.Constructive.HalfPow.half
      decide)

/-- The coefficient left in the vacuum after every excited character is
shifted by its dimension. -/
def anchorVacuumReserve (cutoff : Nat) : Q' :=
  (1 : Q') - anchorExcitedCharacterDimensionMass cutoff

theorem anchorVacuumReserve_nonnegative (cutoff : Nat) :
    (0 : Q') ≤ anchorVacuumReserve cutoff := by
  unfold anchorVacuumReserve
  exact Q'.sub_nonneg_of_le
    (anchorExcitedCharacterDimensionMass_le_one cutoff)

/-- The stronger quantitative reserve: at least one half of the vacuum
coefficient survives every finite cutoff. -/
theorem anchorVacuumReserve_ge_half (cutoff : Nat) :
    dyad 1 ≤ anchorVacuumReserve cutoff := by
  have hhalfComplement :
      dyad 1 ≤ (1 : Q') - dyad 1 := by
    unfold dyad YMGap.Constructive.HalfPow.half
    decide
  have hanti :
      (1 : Q') - dyad 1 ≤
        (1 : Q') - anchorExcitedCharacterDimensionMass cutoff := by
    exact Q'.add_le_add_left (1 : Q') _ _
      (Q'.neg_le_neg
        (anchorExcitedCharacterDimensionMass_le_half cutoff))
  unfold anchorVacuumReserve
  exact Q'.le_trans' _ _ _ hhalfComplement hanti

/-- Exact bookkeeping identity for the later face-weight SOS rewrite. -/
theorem anchorVacuumReserve_add_excitedMass_eqv_one (cutoff : Nat) :
    anchorVacuumReserve cutoff +
        anchorExcitedCharacterDimensionMass cutoff ≈ (1 : Q') := by
  unfold anchorVacuumReserve
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv 1
      (-anchorExcitedCharacterDimensionMass cutoff)
      (anchorExcitedCharacterDimensionMass cutoff)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ 0
      (Q'.neg_add_self_eqv
        (anchorExcitedCharacterDimensionMass cutoff))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' 1)

#print axioms anchorExcitedCharacterDimensionTerm_eqv_tailTerm
#print axioms anchorExcitedCharacterDimensionMass_eqv_tailWindow
#print axioms anchorExcitedCharacterDimensionMass_nonnegative
#print axioms anchorExcitedCharacterDimensionMass_le_half
#print axioms anchorExcitedCharacterDimensionMass_le_one
#print axioms anchorVacuumReserve_nonnegative
#print axioms anchorVacuumReserve_ge_half
#print axioms anchorVacuumReserve_add_excitedMass_eqv_one

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceReserve
