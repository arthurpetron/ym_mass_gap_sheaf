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

/-! Bare finite coefficient norms only.  The following sums use the literal
SU(2) dimensions `n+1` and Casimirs `n*(n+2)`.  They supply an optional scalar
heat input; no interacting variance, shifted H1 estimate, physical mass gap,
or transport through a complete incident plaquette star is asserted. -/

open YMGap.Constructive.RationalTail

/-- Squared bare heat coefficient at doubled-spin label `n`. -/
def heatCoefficientNormTerm (w : Q') (n : Nat) : Q' :=
  Q'.ofNat ((n + 1) * (n + 1)) * qpow w (2 * (n * (n + 2)))

/-- The inclusive bare coefficient norm `N_K`, including label zero. -/
def heatCoefficientNorm (w : Q') (K : Nat) : Q' :=
  finSum (heatCoefficientNormTerm w) (K + 1)

/-- The inclusive Casimir-weighted bare coefficient norm `E_K`. -/
def heatCoefficientEnergy (w : Q') (K : Nat) : Q' :=
  finSum (fun n => Q'.ofNat (n * (n + 2)) * heatCoefficientNormTerm w n) (K + 1)

private def halfPowerTerm (w : Q') (n : Nat) : Q' :=
  Q'.ofNat ((n + 1) * (n + 1)) * qpow w (n * (n + 2))

private theorem mul_front_swap (a b c : Q') : a * (b * c) ≈ b * (a * c) := by
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b))
      (Q'.mul_assoc_eqv b a c))

private theorem heat_energy_term_smoothing {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (n : Nat) :
    ((1 : Q') - w) *
        (Q'.ofNat (n * (n + 2)) * heatCoefficientNormTerm w n) ≤
      halfPowerTerm w n := by
  let delta := (1 : Q') - w
  let C := Q'.ofNat (n * (n + 2))
  let D := Q'.ofNat ((n + 1) * (n + 1))
  let p := qpow w (n * (n + 2))
  have hpow : qpow w (2 * (n * (n + 2))) ≈ p * p := by
    have he : 2 * (n * (n + 2)) = n * (n + 2) + n * (n + 2) := by omega
    rw [he]
    exact qpow_add w (n * (n + 2)) (n * (n + 2))
  have hregroup : delta * (C * (D * qpow w (2 * (n * (n + 2))))) ≈
      D * ((delta * C) * (p * p)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv delta C _)) ?_
    refine Q'.eqv_trans _ _ _ (mul_front_swap (delta * C) D _) ?_
    exact Q'.mul_eqv_congr_left D _ _
      (Q'.mul_eqv_congr_left (delta * C) _ _ hpow)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
    (Q'.mul_le_mul_of_nonneg_left _ _ D
      (qpow_squared_casimir_smoothing hw0 hw1 (n * (n + 2)))
      (zero_le_ofNat _))

/-- Either member of an even/odd pair costs at most four times the shorter
label's squared coefficient.  No division or positive-nome guard is used. -/
private theorem halfPowerTerm_pair_le {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (r n : Nat)
    (hlo : 2 * r ≤ n) (hhi : n ≤ 2 * r + 1) :
    halfPowerTerm w n ≤ (4 : Q') * heatCoefficientNormTerm w r := by
  have hdim : (n + 1) * (n + 1) ≤ 4 * ((r + 1) * (r + 1)) := by
    have h : n + 1 ≤ 2 * (r + 1) := by omega
    calc
      (n + 1) * (n + 1) ≤ (2 * (r + 1)) * (2 * (r + 1)) :=
        Nat.mul_le_mul h h
      _ = (2 * 2) * ((r + 1) * (r + 1)) := by ac_rfl
      _ = 4 * ((r + 1) * (r + 1)) := rfl
  have hcas : 2 * (r * (r + 2)) ≤ n * (n + 2) := by
    calc
      2 * (r * (r + 2)) = (2 * r) * (r + 2) := by rw [Nat.mul_assoc]
      _ ≤ n * (n + 2) := Nat.mul_le_mul hlo (by omega)
  have hpower := qpow_antitone hw0 hw1 _ _ hcas
  have hdimQ := CReal.ofNat_le_ofNat hdim
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat ((n + 1) * (n + 1))) hpower (zero_le_ofNat _)
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _
    (qpow w (2 * (r * (r + 2)))) hdimQ (qpow_nonneg w hw0 _)
  have hfactor :
      Q'.ofNat (4 * ((r + 1) * (r + 1))) * qpow w (2 * (r * (r + 2))) ≈
        (4 : Q') * heatCoefficientNormTerm w r := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_eqv 4 ((r + 1) * (r + 1)))) ?_
    exact Q'.mul_assoc_eqv 4 (Q'.ofNat ((r + 1) * (r + 1))) _
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hfactor))

private theorem halfPower_paired_prefix_le {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ R, finSum (halfPowerTerm w) (2 * R) ≤
      (8 : Q') * finSum (heatCoefficientNormTerm w) R
  | 0 => Q'.ge_of_eqv (Q'.mul_zero_eqv 8)
  | R + 1 => by
    have he := halfPowerTerm_pair_le hw0 hw1 R (2 * R) (by omega) (by omega)
    have ho := halfPowerTerm_pair_le hw0 hw1 R (2 * R + 1) (by omega) (by omega)
    have hlen : 2 * (R + 1) = (2 * R + 1) + 1 := by omega
    rw [hlen, finSum_succ, finSum_succ]
    have hfirst : finSum (halfPowerTerm w) (2 * R) + halfPowerTerm w (2 * R) ≤
        (8 : Q') * finSum (heatCoefficientNormTerm w) R +
          (4 : Q') * heatCoefficientNormTerm w R :=
      Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ (halfPower_paired_prefix_le hw0 hw1 R))
        (Q'.add_le_add_left _ _ _ he)
    have hboth :
        (finSum (halfPowerTerm w) (2 * R) + halfPowerTerm w (2 * R)) +
            halfPowerTerm w (2 * R + 1) ≤
          ((8 : Q') * finSum (heatCoefficientNormTerm w) R +
            (4 : Q') * heatCoefficientNormTerm w R) +
            (4 : Q') * heatCoefficientNormTerm w R :=
      Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hfirst)
        (Q'.add_le_add_left _ _ _ ho)
    have hdouble :
        (4 : Q') * heatCoefficientNormTerm w R +
          (4 : Q') * heatCoefficientNormTerm w R ≈
        (8 : Q') * heatCoefficientNormTerm w R :=
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv 4 4 (heatCoefficientNormTerm w R)))
        (Q'.mul_eqv_congr_right _ _ _ (by decide : ((4 : Q') + 4) ≈ 8))
    have hfactor :
        ((8 : Q') * finSum (heatCoefficientNormTerm w) R +
          (4 : Q') * heatCoefficientNormTerm w R) +
          (4 : Q') * heatCoefficientNormTerm w R ≈
        (8 : Q') * finSum (heatCoefficientNormTerm w) (R + 1) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hdouble) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv 8 _ _)
    exact Q'.le_trans' _ _ _ hboth (Q'.le_of_eqv hfactor)

/-- Even/odd pairing bounds the single-power inclusive coefficient sum by
eight times the squared-power sum at the SAME inclusive cutoff. -/
theorem heatCoefficient_half_power_norm_le {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) :
    finSum (fun n => Q'.ofNat ((n + 1) * (n + 1)) *
        qpow w (n * (n + 2))) (K + 1) ≤ (8 : Q') * heatCoefficientNorm w K := by
  have hnonneg : ∀ n, (0 : Q') ≤ halfPowerTerm w n := fun n =>
    Q'.mul_nonneg _ _ (zero_le_ofNat _) (qpow_nonneg w hw0 _)
  exact Q'.le_trans' _ _ _
    (finSum_monotone_of_nonneg (halfPowerTerm w) hnonneg
      (K + 1) (2 * (K + 1)) (by omega))
    (halfPower_paired_prefix_le hw0 hw1 (K + 1))

/-- Division-free, cutoff-independent bare SU(2) heat coefficient estimate:
`(1-w)*E_K ≤ 8*N_K`.  EVERY inclusive cutoff is covered, including `K=0`,
and both endpoints `w=0` and `w=1`; no `headCutoff` or positivity hypothesis.
This is not an interacting variance, shifted H1 bound, or mass-gap claim. -/
theorem heatCoefficient_energy_le_eight_norm {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) :
    ((1 : Q') - w) * heatCoefficientEnergy w K ≤
      (8 : Q') * heatCoefficientNorm w K := by
  have hscale := const_mul_finSum
    (fun n => Q'.ofNat (n * (n + 2)) * heatCoefficientNormTerm w n)
    ((1 : Q') - w) (K + 1)
  have hterms := YMGap.Continuum.SpectralGap.finSum_le_of_termwise
    (fun n => ((1 : Q') - w) *
      (Q'.ofNat (n * (n + 2)) * heatCoefficientNormTerm w n))
    (halfPowerTerm w) (heat_energy_term_smoothing hw0 hw1) (K + 1)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale)
    (Q'.le_trans' _ _ _ hterms (heatCoefficient_half_power_norm_le hw0 hw1 K))

#print axioms heatCoefficientNormTerm
#print axioms heatCoefficientNorm
#print axioms heatCoefficientEnergy
#print axioms heatCoefficient_half_power_norm_le
#print axioms heatCoefficient_energy_le_eight_norm

end YMGap.Continuum.SU2HeatSquaredCasimirSmoothing
