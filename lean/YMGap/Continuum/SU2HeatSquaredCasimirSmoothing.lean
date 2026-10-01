/-
# Squared finite-heat attenuation pays one Casimir

This is scalar arithmetic for the ORIGINAL SU(2) harmonic attenuation.  The
cutoff branch is exactly zero on both sides.  No operator, source, spectator
channel, or terminal-message inequality is asserted here.
-/

import YMGap.Continuum.SU2HeatCutoffCasimirBound

namespace YMGap.Continuum.SU2HeatSquaredCasimirSmoothing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2HeatCutoffCasimirBound

local infix:50 " ≈ " => Q'.eqv

/-- The finite geometric sum bounds one Casimir-weighted heat power.  This
division-free form is also valid at `w=0`, `w=1`, and `lambda=0`. -/
theorem casimir_power_le_one {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (lambda : Nat) :
    (((1 : Q') - w) * Q'.ofNat lambda) * qpow w lambda ≤ 1 := by
  let h : Q' := (1 : Q') - w
  let p : Q' := qpow w lambda
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le hw1
  have hp : (0 : Q') ≤ p := qpow_nonneg w hw0 lambda
  have hpower : p ≤ qpow w (lambda - 1) :=
    qpow_antitone hw0 hw1 (lambda - 1) lambda (Nat.sub_le lambda 1)
  have htimes : Q'.ofNat lambda * p ≤ geomSum w lambda :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hpower (zero_le_ofNat lambda))
      (geomSum_ge_pow hw0 hw1 lambda)
  have hscaled : h * (Q'.ofNat lambda * p) ≤ h * geomSum w lambda :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htimes hh
  have hfactor : h * geomSum w lambda ≈ (1 : Q') - p :=
    Q'.eqv_symm (oneSub_pow_factor w lambda)
  have hsub : (1 : Q') - p ≤ 1 := by
    have hplus : (1 : Q') ≤ 1 + p :=
      Q'.add_le_self_of_nonneg 1 p hp
    have hswap : (1 : Q') ≤ p + 1 :=
      Q'.le_trans' _ _ _ hplus (Q'.le_of_eqv (Q'.add_comm_eqv 1 p))
    exact Q'.sub_le_of_le_add hswap
  have hleft : (h * Q'.ofNat lambda) * p ≈
      h * (Q'.ofNat lambda * p) :=
    Q'.mul_assoc_eqv h (Q'.ofNat lambda) p
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hsub))

/-- Two identical retained heat multipliers give a one-sided `1/(1-w)`
Casimir smoothing budget without division.  This is a scalar spectral input,
not a pointwise signed Casimir bound on the heat kernel. -/
theorem qpow_squared_casimir_smoothing {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (lambda : Nat) :
    (((1 : Q') - w) * Q'.ofNat lambda) *
        (qpow w lambda * qpow w lambda) ≤ qpow w lambda := by
  let c : Q' := ((1 : Q') - w) * Q'.ofNat lambda
  let p : Q' := qpow w lambda
  have hp : (0 : Q') ≤ p := qpow_nonneg w hw0 lambda
  have hbase : c * p ≤ (1 : Q') :=
    casimir_power_le_one hw0 hw1 lambda
  have hmul : (c * p) * p ≤ (1 : Q') * p :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hp
  have hregroup : c * (p * p) ≈ (c * p) * p :=
    Q'.eqv_symm (Q'.mul_assoc_eqv c p p)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv p)))

/-- The actual finite cutoff: every omitted label has attenuation zero, so
both sides vanish.  No cutoff largeness guard is needed for this scalar law. -/
theorem attenuation_squared_casimir_smoothing {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K d : Nat) :
    (((1 : Q') - w) * Q'.ofNat (d * (d + 2))) *
        (attenuation w K d * attenuation w K d) ≤
      attenuation w K d := by
  unfold attenuation
  by_cases hd : d ≤ K
  · rw [if_pos hd]
    exact qpow_squared_casimir_smoothing hw0 hw1 (d * (d + 2))
  · rw [if_neg hd]
    have hzero : ((0 : Q') * 0) ≈ 0 := Q'.zero_mul_eqv 0
    have hinner :
        (((1 : Q') - w) * Q'.ofNat (d * (d + 2))) * (0 * 0) ≈
          (((1 : Q') - w) * Q'.ofNat (d * (d + 2))) * 0 :=
      Q'.mul_eqv_congr_left _ _ _ hzero
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ hinner (Q'.mul_zero_eqv _))

#print axioms casimir_power_le_one
#print axioms qpow_squared_casimir_smoothing
#print axioms attenuation_squared_casimir_smoothing

end YMGap.Continuum.SU2HeatSquaredCasimirSmoothing
