/-
# All-even-time response lower bounds on the SAME Wilson completion

Write r_n = B(x,T(2*n)x). The actual completed vector
T(n+2)x - rho T(n)x has squared norm

  (r_(n+2) - rho r_(n+1)) - rho (r_(n+1) - rho r_n).

Its positivity propagates a nonnegative first increment. Induction then
gives rho^n B(x,x) <= r_n from the initial two-step Rayleigh floor, with
no division, spectral representation, or one-step positivity assumption.
For the EXISTING norm-one unitExcitation, the proved floor and ceiling
therefore give a band at EVERY even integer time and a positive norm
floor for its image at EVERY integer time.

The carrier, original time action and small-nome guards are unchanged.
The unconditional excitation statements remain at nome 1/1024 and fixed
lattice spacing. They do not construct a changing-spacing family,
fixed-physical-time continuum survival, a Hamiltonian, physical mass
calibration, full QFT axioms, or the every-group Clay theorem.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
import YMGap.Continuum.BF4WilsonSpatialUnionRelaxation

namespace YMGap.Continuum.BF4WilsonSpatialUnionResponseLower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionLinear (completedSmul)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
  (completedZero completedInner_zero_left)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_sub_self rc_sub_add)
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation (even_autocorrelation_decay)
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 (A.approx n))
      (QPoly.q_add_zero_eqv (A.approx n))))

private theorem rc_mul_eq_scale (rho : Q') (a : RC) :
    RCmul (Quotient.mk crealSetoid (ofQ' rho)) a = RCscale rho a := by
  refine Quotient.inductionOn a ?_
  exact fun _ => rfl

private theorem rc_sub_nonnegative_of_le {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rw [rc_sub_self] at h'
  exact h'

private theorem rc_le_of_sub_nonnegative {a b : RC}
    (h : RCnonneg (RCsub a b)) : RCle b a := by
  have h' := RCadd_le_add h (RCle_refl b)
  rw [rc_zero_add, rc_sub_add] at h'
  exact h'

section General

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs

/-- A positive SQUARE on the actual completed carrier. The scalar need not
be positive for this second-difference inequality. -/
theorem evenResponse_second_difference (x : V) (rho : Q') (n : Nat) :
    RCle
      (RCscale rho (RCsub (B x (T (2*(n+1)) x))
        (RCscale rho (B x (T (2*n) x)))))
      (RCsub (B x (T (2*(n+2)) x))
        (RCscale rho (B x (T (2*(n+1)) x)))) := by
  have h := completedInner_nonnegative hw0 hw1 hsmall hd hs
    (completedSub hw0 hw1 hsmall hd hs (T (n+2) x)
      (completedSmul hw0 hw1 hsmall hd hs rho (T n x)))
  have h0 : n+n = 2*n := by omega
  have h1 : (n+2)+n = 2*(n+1) := by omega
  have h2 : n+(n+2) = 2*(n+1) := by omega
  have h3 : (n+2)+(n+2) = 2*(n+2) := by omega
  simp only [completedInner_sub_left, completedInner_sub_right,
    completedInner_smul_left, completedInner_smul_right, rc_mul_eq_scale,
    completedInner_time_sum, h0, h1, h2, h3] at h
  exact rc_le_of_sub_nonnegative h

/-- The initial two-step floor propagates to every adjacent EVEN response.
No division by a response and no one-step positivity is used. -/
theorem evenResponse_step_lower (x : V) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (hfloor : RCle (RCscale rho (B x x)) (B x (T 2 x))) : ∀ n : Nat,
    RCle (RCscale rho (B x (T (2*n) x))) (B x (T (2*(n+1)) x))
  | 0 => by
      simpa only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, completedTime_zero] using hfloor
  | n+1 => by
      have h := RCscale_mono hrho
        (rc_sub_nonnegative_of_le (evenResponse_step_lower x rho hrho hfloor n))
      rw [RCscale_RCzero] at h
      exact rc_le_of_sub_nonnegative (RCle_trans h
        (evenResponse_second_difference hw0 hw1 hsmall hd hs x rho n))

/-- General all-integer-time lower bound from an actual two-step Rayleigh
floor on THIS completed carrier. The floor is an input here, not assumed
for arbitrary vectors; the fixed excitation instance below constructs it. -/
theorem evenResponse_geometric_lower (x : V) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (hfloor : RCle (RCscale rho (B x x)) (B x (T 2 x))) : ∀ n : Nat,
    RCle (RCscale (rho^n) (B x x)) (B x (T (2*n) x))
  | 0 => by
      rw [Nat.mul_zero, completedTime_zero, show rho^0 = (1 : Q') from rfl,
        RCscale_one]
      exact RCle_refl _
  | n+1 => by
      have h := RCle_trans
        (RCscale_mono hrho (evenResponse_geometric_lower x rho hrho hfloor n))
        (evenResponse_step_lower hw0 hw1 hsmall hd hs x rho hrho hfloor n)
      rw [RCscale_RCscale] at h
      exact h

end General

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs

private theorem rc_scale_one_constant (rho : Q') :
    RCscale rho (Quotient.mk crealSetoid cone) =
      Quotient.mk crealSetoid (ofQ' rho) :=
  Quotient.sound (CRealAlg.cmul_cone (ofQ' rho))

/-- The SAME norm-one excitation has its explicit rational lower bound
at EVERY even integer lag, not only dyadic lags. -/
theorem unitExcitation_even_lower (n : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' (rayleighFloor^n)))
      (B unitExcitation (T (2*n) unitExcitation)) := by
  have hf : RCle (RCscale rayleighFloor (B unitExcitation unitExcitation))
      (B unitExcitation (T 2 unitExcitation)) := by
    rw [unitExcitation_norm, rc_scale_one_constant, normalizedResponse_pin]
    exact normalizedResponse_floor
  have h := evenResponse_geometric_lower nome_pos nome_lt_one hsmall hd hs
    unitExcitation rayleighFloor (Q'.le_of_lt rayleighFloor_positive) hf n
  rw [unitExcitation_norm, rc_scale_one_constant] at h
  exact h

/-- Previously proved decay, evaluated at the same vector and the same lag. -/
theorem unitExcitation_even_upper (n : Nat) :
    RCle (B unitExcitation (T (2*n) unitExcitation))
      (Quotient.mk crealSetoid (ofQ' (rayleighCeiling^n))) := by
  have h := even_autocorrelation_decay nome_pos nome_lt_one hsmall hd hs
    unitExcitation unitExcitation_orthogonal n
  rw [unitExcitation_norm] at h
  change RCle _ (RCscale (rayleighCeiling^n) (Quotient.mk crealSetoid cone)) at h
  rw [rc_scale_one_constant] at h
  exact h

/-- A two-sided response band for ONE actual normalized excitation at all
even lags, with the existing explicit positive floor and strict ceiling. -/
theorem unitExcitation_even_band (n : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' (rayleighFloor^n)))
        (B unitExcitation (T (2*n) unitExcitation)) ∧
      RCle (B unitExcitation (T (2*n) unitExcitation))
        (Quotient.mk crealSetoid (ofQ' (rayleighCeiling^n))) :=
  ⟨unitExcitation_even_lower n, unitExcitation_even_upper n⟩

/-- Explicit squared-norm floor for the SAME image at every integer time. -/
theorem unitExcitation_time_norm_floor (n : Nat) :
    RCle (Quotient.mk crealSetoid (ofQ' (rayleighFloor^n)))
      (B (T n unitExcitation) (T n unitExcitation)) := by
  rw [← completedInner_even_diagonal]
  exact unitExcitation_even_lower n

private theorem rayleighFloor_pow_positive : ∀ n : Nat,
    (0 : Q') < rayleighFloor^n
  | 0 => by decide
  | n+1 => Q'.mul_pos rayleighFloor_positive (rayleighFloor_pow_positive n)

/-- No finite discrete-time image is the actual completed zero. This is
fixed-spacing nontriviality, not survival through a continuum limit. -/
theorem unitExcitation_time_ne_zero (n : Nat) :
    T n unitExcitation ≠ completedZero nome_pos nome_lt_one hsmall hd hs := by
  intro hz
  have h := unitExcitation_time_norm_floor n
  rw [hz, completedInner_zero_left] at h
  have hle : rayleighFloor^n ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (rayleighFloor_pow_positive n) hle)

#print axioms evenResponse_second_difference
#print axioms evenResponse_step_lower
#print axioms evenResponse_geometric_lower
#print axioms unitExcitation_even_lower
#print axioms unitExcitation_even_upper
#print axioms unitExcitation_even_band
#print axioms unitExcitation_time_norm_floor
#print axioms unitExcitation_time_ne_zero

end YMGap.Continuum.BF4WilsonSpatialUnionResponseLower
