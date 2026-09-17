/-
# A dyadic response band for the SAME normalized Wilson excitation

Completed Cauchy--Schwarz and time balance give C(t)^2 <= C(2t) for
the existing norm-one vector. Starting from its proved positive TWO-step
response yields rho^(2^k) <= C(2 * 2^k). The existing completed norm
decay supplies the upper bound q^(2^k), on this very same vector and map.

All parameters remain fixed at the checked small nome 1/1024. These are
discrete-time response estimates on the existing Wilson union completion.
They do not construct a changing-spacing family, a surviving continuum
excitation, a Hamiltonian, a physical mass calibration, or a continuum QFT.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
import YMGap.Continuum.BF4WilsonSpatialUnionRelaxation

namespace YMGap.Continuum.BF4WilsonSpatialUnionDyadicResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm (completedTime)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner completedInner_cauchySchwarz)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
  (completedInner_even_diagonal)
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation (even_autocorrelation_decay)
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs

private theorem rc_one_mul (x : RC) :
    RCmul (Quotient.mk crealSetoid cone) x = x := by
  refine Quotient.inductionOn x ?_
  exact fun a => Quotient.sound (CRealAlg.cone_mul a)

private theorem rc_square_mono {x y : RC} (hx : RCnonneg x) (hxy : RCle x y) :
    RCle (RCmul x x) (RCmul y y) := by
  have hfirst := RCmul_mono_nonneg_left hx hxy
  have hsecond := RCmul_mono_nonneg_left (RCle_trans hx hxy) hxy
  rw [RCmul_comm y x] at hsecond
  exact RCle_trans hfirst hsecond

/-- The actual completed coefficient at twice a lag dominates its square.
No one-step positivity assumption is introduced. -/
theorem unitExcitation_response_square (t : Nat) :
    RCle
      (RCmul (B unitExcitation (T t unitExcitation))
        (B unitExcitation (T t unitExcitation)))
      (B unitExcitation (T (2*t) unitExcitation)) := by
  have h := completedInner_cauchySchwarz nome_pos nome_lt_one hsmall hd hs
    unitExcitation (T t unitExcitation)
  rw [unitExcitation_norm, rc_one_mul,
    ← completedInner_even_diagonal] at h
  exact h

/-- A geometric LOWER bound at arbitrarily large dyadic TWO-step times,
using the existing normalized excitation and its proved Rayleigh floor. -/
theorem unitExcitation_dyadic_lower : ∀ k : Nat,
    RCle (Quotient.mk crealSetoid (ofQ' (rayleighFloor ^ (2^k))))
      (B unitExcitation (T (2*(2^k)) unitExcitation))
  | 0 => by
      have hp : Quotient.mk crealSetoid (ofQ' (rayleighFloor ^ (1 : Nat))) =
          Quotient.mk crealSetoid (ofQ' rayleighFloor) :=
        Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
          (fun _ => Q'.mul_one_eqv rayleighFloor))
      simp only [Nat.pow_zero, Nat.mul_one]
      rw [hp, normalizedResponse_pin]
      exact normalizedResponse_floor
  | k+1 => by
      have hn : (2 : Nat)^(k+1) = 2^k + 2^k := by
        rw [Nat.pow_succ, Nat.mul_two]
      have htime : 2*(2*(2^k)) = 2*(2^(k+1)) := by
        rw [hn]
        omega
      have hpower :
          Quotient.mk crealSetoid (ofQ' (rayleighFloor ^ (2^(k+1)))) =
            RCmul (Quotient.mk crealSetoid (ofQ' (rayleighFloor ^ (2^k))))
              (Quotient.mk crealSetoid (ofQ' (rayleighFloor ^ (2^k)))) := by
        rw [hn]
        exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
          (fun _ => YMGap.Continuum.Q'.pow_add_eqv rayleighFloor (2^k) (2^k)))
      have hnonneg : RCnonneg
          (Quotient.mk crealSetoid (ofQ' (rayleighFloor ^ (2^k)))) :=
        leEv_ofQ'_of_approx_ge (fun _ =>
          Q'.pow_nonneg rayleighFloor (Q'.le_of_lt rayleighFloor_positive) (2^k))
      have h := RCle_trans (rc_square_mono hnonneg (unitExcitation_dyadic_lower k))
        (unitExcitation_response_square (2*(2^k)))
      rw [htime] at h
      rw [hpower]
      exact h

/-- The matching UPPER bound is the previously proved norm decay, on the
same vector, at the same lag and with the same two-step rate. -/
theorem unitExcitation_dyadic_upper (k : Nat) :
    RCle (B unitExcitation (T (2*(2^k)) unitExcitation))
      (Quotient.mk crealSetoid (ofQ' (rayleighCeiling ^ (2^k)))) := by
  have h := even_autocorrelation_decay nome_pos nome_lt_one hsmall hd hs
    unitExcitation unitExcitation_orthogonal (2^k)
  rw [unitExcitation_norm] at h
  have hp : RCscale (rayleighCeiling ^ (2^k)) (Quotient.mk crealSetoid cone) =
      Quotient.mk crealSetoid (ofQ' (rayleighCeiling ^ (2^k))) :=
    Quotient.sound (CRealAlg.cmul_cone (ofQ' (rayleighCeiling ^ (2^k))))
  change RCle _ (RCscale (rayleighCeiling ^ (2^k))
    (Quotient.mk crealSetoid cone)) at h
  rw [hp] at h
  exact h

/-- Both endpoints concern ONE normalized excitation and ONE completed time
map. This band is fixed-spacing data, not continuum survival data. -/
theorem unitExcitation_dyadic_band (k : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' (rayleighFloor ^ (2^k))))
        (B unitExcitation (T (2*(2^k)) unitExcitation)) ∧
      RCle (B unitExcitation (T (2*(2^k)) unitExcitation))
        (Quotient.mk crealSetoid (ofQ' (rayleighCeiling ^ (2^k)))) :=
  ⟨unitExcitation_dyadic_lower k, unitExcitation_dyadic_upper k⟩

#print axioms unitExcitation_response_square
#print axioms unitExcitation_dyadic_lower
#print axioms unitExcitation_dyadic_upper
#print axioms unitExcitation_dyadic_band

end YMGap.Continuum.BF4WilsonSpatialUnionDyadicResponse
