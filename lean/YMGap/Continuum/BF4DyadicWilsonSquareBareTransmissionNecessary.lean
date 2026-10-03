/-
# Necessary heat-loss bounds for bare square transmission certificates

The original square's reference transmission is w^(12*s). If a nonnegative
certificate rate rho is at most this reference, a positive floor on rho^s
requires the cleared bound kappa*(1+12*s*s*(1-w)) <= 1. A single reference
transmission floor similarly requires kappa*(1+12*s*(1-w)) <= 1.

These are rational necessities for the displayed certificate coefficients.
No inequality comparing an actual interacting response with the bare
reference is asserted. No coupling schedule or physical AF identification,
logarithmic estimate, source replacement, or continuum conclusion is used.
-/

import YMGap.Continuum.ReciprocalBernoulliUpper
import YMGap.Continuum.HeatKernelConv

namespace YMGap.Continuum.BF4DyadicWilsonSquareBareTransmissionNecessary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow qpow_add qpow_eqv_congr
  poly_identity_of_normal_eq)
open YMGap.Continuum.ReciprocalBernoulliUpper

local infix:50 " ≈ " => Q'.eqv

private theorem qpow_rg (w : Q') : ∀ n : Nat,
    qpow w n = RGTransport.qpow w n
  | 0 => rfl
  | n+1 => congrArg (fun z : Q' => z*w) (qpow_rg w n)

private theorem block_power_pin (w : Q') (block : Nat) : ∀ s : Nat,
    (qpow w block)^s ≈ qpow w (block*s)
  | 0 => by
      simp only [Nat.mul_zero, Q'.pow_zero, RingNormaliser.qpow_zero]
      exact Q'.eqv_refl _
  | s+1 => by
      change qpow w block * (qpow w block)^s ≈ qpow w (block*(s+1))
      have h := Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (qpow w block) _ _ (block_power_pin w block s))
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.eqv_symm (qpow_add w (block*s) block)))
      simpa only [Nat.mul_succ] using h

private theorem power_floor_necessary {w kappa : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (_hkappa : (0 : Q') < kappa) (n : Nat)
    (hfloor : kappa ≤ qpow w n) :
    kappa * (1 + Q'.ofNat n * (1-w)) ≤ (1 : Q') := by
  let loss : Q' := 1-w
  have hloss0 : (0 : Q') ≤ loss := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hloss1 : loss ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt hw0)))
      (Q'.le_of_eqv (by change (1 : Q') + -0 ≈ 1; decide))
  have hbase : oneSub loss ≈ w := poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
    (.var 0) (by decide) (fun _ => w)
  have hpower : RGTransport.qpow (oneSub loss) n ≈ qpow w n := by
    rw [← qpow_rg (oneSub loss) n]
    exact qpow_eqv_congr hbase n
  have hbern : qpow w n * bernDen loss n ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ (bernDen loss n) hpower))
      (oneSub_pow_mul_bernDen_le hloss0 hloss1 n)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ (bernDen loss n)
    hfloor (Q'.le_of_lt (bernDen_pos hloss0 n))
  exact Q'.le_trans' _ _ _ hscaled hbern

/-- A positive floor on the SINGLE bare reference transmission requires
small total word-scale heat loss. This is not an actual-response ceiling. -/
theorem bare_transmission_floor_necessary {w kappa : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hkappa : (0 : Q') < kappa) (s : Nat)
    (hfloor : kappa ≤ qpow w (12*s)) :
    kappa * (1 + Q'.ofNat (12*s) * (1-w)) ≤ (1 : Q') :=
  power_floor_necessary hw0 hw1 hkappa (12*s) hfloor

/-- A positive floor on s repetitions of a nonnegative rate bounded by
the bare reference transmission requires total s-squared heat loss control.
The premise compares certificate rates only, not interacting responses. -/
theorem repeated_bare_transmission_floor_necessary {w kappa rho : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hkappa : (0 : Q') < kappa) (s : Nat)
    (hrho0 : (0 : Q') ≤ rho) (hrho : rho ≤ qpow w (12*s))
    (hfloor : kappa ≤ rho^s) :
    kappa * (1 + Q'.ofNat (12*s*s) * (1-w)) ≤ (1 : Q') := by
  have hmono : rho^s ≤ (qpow w (12*s))^s :=
    HKConv.pow_le_pow_base hrho0 hrho s
  have hbare : kappa ≤ qpow w (12*s*s) := Q'.le_trans' _ _ _ hfloor
    (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv (block_power_pin w (12*s) s)))
  exact power_floor_necessary hw0 hw1 hkappa (12*s*s) hbare

end YMGap.Continuum.BF4DyadicWilsonSquareBareTransmissionNecessary

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareBareTransmissionNecessary.bare_transmission_floor_necessary
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareBareTransmissionNecessary.repeated_bare_transmission_floor_necessary
