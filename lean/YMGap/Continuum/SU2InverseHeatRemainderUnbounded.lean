/-
# A computable escaping spin at every strict nome

The coefficient remainder from SU2InverseHeatRemainderObstruction is
unbounded in spin at EACH fixed 0<w<1, including arbitrarily near one.
The witness is a natural index computed by the existing rational geometric
cutoff; no limiting argument discards its modulus.

This rules out a spin-uniform bound for this separated scalar remainder.
It does not identify it with an interacting operator, discard the negative
square in the full expression, or refute the original weighted energy bound.
-/

import YMGap.Continuum.SU2InverseHeatRemainderObstruction
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

namespace YMGap.Continuum.SU2InverseHeatRemainderUnbounded

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2InverseHeatRemainderObstruction
open YMGap.Continuum.BondMovingScaledNorm (qpow_pos)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local infix:50 " ≈ " => Q'.eqv

private theorem prefactor_pos {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) : (0 : Q') < 1 + -(RGTransport.qpow w 2) := by
  have hsq : RGTransport.qpow w 2 ≤ w :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_eqv_pow w 2))
      (Q'.le_trans' _ _ _
        (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
          (by decide : 1 ≤ 2))
        (Q'.le_of_eqv (Q'.mul_one_eqv w)))
  exact HKPos.one_sub_pos (Q'.lt_of_le_of_lt hsq hw1)

/-- Computed from the nome and the proposed rational cap. The extra one
keeps the witness in the two-neighbor character range j>=1. -/
def escapeIndex (w C : Q') : Nat :=
  geometricCutoff w (1 + Q'.abs C) (1 + -(RGTransport.qpow w 2)) + 1

theorem escapeIndex_positive (w C : Q') : 0 < escapeIndex w C := Nat.zero_lt_succ _

/-- A stronger explicit witness than mere failure of an existential cap:
the remainder at the returned spin is at least 1+|C|. -/
theorem escapeIndex_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (C : Q') :
    1 + Q'.abs C ≤ inverseHeatRemainderAt w hw0 (escapeIndex w C) := by
  let j := escapeIndex w C
  let b : Q' := 1 + -(RGTransport.qpow w 2)
  let p := RGTransport.qpow w (2*j+3)
  have hb : (0 : Q') < b := prefactor_pos hw0 hw1
  have hp : (0 : Q') < p := qpow_pos hw0 _
  have hC : (0 : Q') ≤ 1 + Q'.abs C :=
    Q'.zero_le_add _ _ Q'.zero_le_one (Q'.abs_nonneg C)
  have hsmall : p * (1 + Q'.abs C) ≤ b :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (qpow_eqv_pow w (2*j+3))))
      (geometric_bound (Q'.le_of_lt hw0) hw1 hC hb (2*j+3)
        (by dsimp [j, b, escapeIndex]; omega))
  have hcancel : (p * (1 + Q'.abs C)) * Q'.recipPos p hp ≈ 1 + Q'.abs C :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv p (1 + Q'.abs C)))
      (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv p hp))
          (Q'.mul_one_eqv _)))
  have hleading : 1 + Q'.abs C ≤ b * Q'.recipPos p hp :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hsmall
        (Q'.le_of_lt (Q'.recipPos_pos p hp)))
  exact Q'.le_trans' _ _ _ hleading
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (qpow_pos hw0 (2*j+1))))
      (Q'.le_of_lt hb))

private theorem not_one_add_le_self (C : Q') : ¬ (1 : Q') + C ≤ C := by
  intro h
  have hd : (0 : Int) < (C.den : Int) := by exact_mod_cast C.den_pos
  change ((1 : Q') + C).num * (C.den : Int) ≤ C.num * (((1 : Q') + C).den : Int) at h
  simp only [Q'.add_num_cast, Q'.add_den_cast] at h
  change ((1 : Int) * (C.den : Int) + C.num * 1) * (C.den : Int) ≤
    C.num * (1 * (C.den : Int)) at h
  simp only [Int.one_mul, Int.mul_one, Int.add_mul] at h
  have hd2 := Int.mul_pos hd hd
  omega

/-- No rational cap can bound these coefficients at all positive spins,
even when the cap may depend arbitrarily on this fixed nome. -/
theorem no_spin_uniform_cap {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (C : Q') :
    ¬ (∀ j : Nat, 0 < j → inverseHeatRemainderAt w hw0 j ≤ C) := by
  intro h
  exact not_one_add_le_self C
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.le_abs_self C))
      (Q'.le_trans' _ _ _ (escapeIndex_bound hw0 hw1 C)
        (h (escapeIndex w C) (escapeIndex_positive w C))))

/-- The escaping value is a literal combination of adjacent physical heat
coefficients, not merely an unconnected factorized expression. -/
theorem raw_escapeIndex_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (C : Q') :
    1 + Q'.abs C ≤ rawAdjacentRemainder w hw0 (escapeIndex w C - 1) := by
  have hpin := rawAdjacentRemainder_eq_factorized w hw0 (escapeIndex w C - 1)
  have hj : escapeIndex w C - 1 + 1 = escapeIndex w C := by
    have := escapeIndex_positive w C
    omega
  rw [hj] at hpin
  exact Q'.le_trans' _ _ _ (escapeIndex_bound hw0 hw1 C) (Q'.ge_of_eqv hpin)

theorem no_raw_spin_uniform_cap {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (C : Q') :
    ¬ (∀ j : Nat, rawAdjacentRemainder w hw0 j ≤ C) := by
  intro h
  exact not_one_add_le_self C
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.le_abs_self C))
      (Q'.le_trans' _ _ _ (raw_escapeIndex_bound hw0 hw1 C)
        (h (escapeIndex w C - 1))))

end YMGap.Continuum.SU2InverseHeatRemainderUnbounded

#print axioms YMGap.Continuum.SU2InverseHeatRemainderUnbounded.escapeIndex
#print axioms YMGap.Continuum.SU2InverseHeatRemainderUnbounded.escapeIndex_positive
#print axioms YMGap.Continuum.SU2InverseHeatRemainderUnbounded.escapeIndex_bound
#print axioms YMGap.Continuum.SU2InverseHeatRemainderUnbounded.no_spin_uniform_cap
#print axioms YMGap.Continuum.SU2InverseHeatRemainderUnbounded.raw_escapeIndex_bound
#print axioms YMGap.Continuum.SU2InverseHeatRemainderUnbounded.no_raw_spin_uniform_cap
