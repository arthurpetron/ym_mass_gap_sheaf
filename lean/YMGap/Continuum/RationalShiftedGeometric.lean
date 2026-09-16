/-
# Absorbing a finite support loss into a positive rational prefactor

For 0<rho<1 and A>=0, the explicit amplitude A/rho^M+1 bounds
A*rho^(n+R+1-M) by amplitude*rho^n for every n,R,M, with natural
truncated subtraction. No lower bound on n is needed. The added one
makes the prefactor strictly positive even when A is zero.

This is scalar algebra only; it asserts no model-specific decay estimate.
-/

import YMGap.Continuum.MayerClustering
import YMGap.Continuum.TotalMajorantClose

namespace YMGap.Continuum.RationalShiftedGeometric

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusteringImpliesGap (pow_pos pow_eqv_congr)
open YMGap.Continuum.MayerClustering (pow_antitone_exp)

local infix:50 " ≈ " => Q'.eqv

/-- A computable prefactor; its definition needs only strict rate positivity. -/
def amplitude (rho A : Q') (h0 : (0 : Q') < rho) (M : Nat) : Q' :=
  A * Q'.recipPos (rho^M) (pow_pos h0 M) + 1

theorem amplitude_pos (rho A : Q') (h0 : (0 : Q') < rho)
    (hA : (0 : Q') ≤ A) (M : Nat) :
    (0 : Q') < amplitude rho A h0 M :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _
      (Q'.mul_nonneg _ _ hA (Q'.le_of_lt (Q'.recipPos_pos _ _))))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- The power estimate includes the initial segment where subtraction
truncates to zero, since M+(n+R+1-M) is always at least n. -/
theorem shifted_power_bound {rho : Q'} (h0 : (0 : Q') < rho)
    (h1 : rho < (1 : Q')) (M R n : Nat) :
    rho^(n+R+1-M) ≤ Q'.recipPos (rho^M) (pow_pos h0 M) * rho^n := by
  let i := Q'.recipPos (rho^M) (pow_pos h0 M)
  have h : rho^M * rho^(n+R+1-M) ≤ rho^n :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.pow_add_eqv rho M (n+R+1-M)))
      (pow_antitone_exp (Q'.le_of_lt h0) (Q'.le_of_lt h1) (by omega))
  have he : i * (rho^M * rho^(n+R+1-M)) ≈ rho^(n+R+1-M) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)))
        (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_left _ _ i h (Q'.le_of_lt (Q'.recipPos_pos _ _)))

/-- A uniform-in-n envelope with the explicit strictly positive amplitude. -/
theorem shifted_bound {rho A : Q'} (h0 : (0 : Q') < rho)
    (h1 : rho < (1 : Q')) (hA : (0 : Q') ≤ A) (M R n : Nat) :
    A * rho^(n+R+1-M) ≤ amplitude rho A h0 M * rho^n := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ A (shifted_power_bound h0 h1 M R n) hA
  exact Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
        (Q'.pow_nonneg _ (Q'.le_of_lt h0) n)))

/-- Reuse the general power-of-power law to pin the even geometric rate. -/
theorem even_power (rho : Q') (n : Nat) : rho^(2*n) ≈ (rho*rho)^n :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (TotalMajorantClose.pow_mul rho 2 n))
    (pow_eqv_congr _ _ (Q'.mul_eqv_congr_left rho _ _ (Q'.mul_one_eqv rho)) n)

end YMGap.Continuum.RationalShiftedGeometric

#print axioms YMGap.Continuum.RationalShiftedGeometric.amplitude
#print axioms YMGap.Continuum.RationalShiftedGeometric.amplitude_pos
#print axioms YMGap.Continuum.RationalShiftedGeometric.shifted_power_bound
#print axioms YMGap.Continuum.RationalShiftedGeometric.shifted_bound
#print axioms YMGap.Continuum.RationalShiftedGeometric.even_power
