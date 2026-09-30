/-
# Quantitative convergence of the actual nested roots to the identity

If the unshifted dyadic state quotients of an original input converge to a
supplied output, the quotient norms have an explicit eventual cap. The exact
inverse dyadic scaling then gives a constructive modulus for convergence of
the original roots to their input. No input range assumption is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeStateQuotientDistance
import YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy
import YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
import YMGap.Continuum.BF4WilsonAllNomeGraphDistance
import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeRootContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg pow_half_le_invSucc invSucc_den_le)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (dist_zero_right)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (defect)
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (half_power_normalizes)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation (stateQuotient)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "PD" => seminorm hw0 hw1 (width := width)
local notation "P" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

private def rootStateCap (Y : (PD).Cauchy) : Q' :=
  Q'.max' 0 ((1+1)+(normCeiling P Y + normCeiling P Y))

private theorem rootStateCap_nonnegative (Y : (PD).Cauchy) :
    (0 : Q') ≤ rootStateCap hw0 hw1 Y := by
  unfold rootStateCap
  exact Q'.le_max'_left _ _

/-- Computed root convergence threshold from the supplied quotient modulus
and the output representative's explicit norm ceiling. -/
def rootModulus (Y : (PD).Cauchy) (modulus : Q' → Nat) (epsilon : Q') : Nat :=
  max (modulus 1)
    (linearTolerance (rootStateCap hw0 hw1 Y)
      (rootStateCap_nonnegative hw0 hw1 Y) epsilon).den

private theorem rat_four_sum (a b : Q') :
    RCadd (RCadd (rat a) (rat a)) (RCadd (rat b) (rat b)) =
      rat ((a+a)+(b+b)) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

private theorem quotient_norm_cap
    (U Y : (PD).Cauchy) (modulus : Q' → Nat)
    (bound : ∀ (epsilon : Q'), (0 : Q') < epsilon → ∀ k,
      modulus epsilon ≤ k →
      RCle (d (stateQuotient hw0 hw1 k (Class U)) (Class Y)) (rat epsilon))
    (k : Nat) (hk : modulus 1 ≤ k) :
    RCle (B (stateQuotient hw0 hw1 k (Class U))
      (stateQuotient hw0 hw1 k (Class U)))
      (rat ((1+1)+(normCeiling P Y + normCeiling P Y))) := by
  have hq := bound 1 (by decide) k hk
  have hY := completedInner_diagonal_le_normCeiling P Y
  have htri := completedDist_triangle hw0 hw1
    (stateQuotient hw0 hw1 k (Class U)) (Class Y) Z
  rw [dist_zero_right, dist_zero_right] at htri
  have hsum := RCadd_le_add (RCadd_le_add hq hq) (RCadd_le_add hY hY)
  rw [rat_four_sum] at hsum
  exact RCle_trans htri hsum

private theorem stateQuotient_inverse_scale (k : Nat) (u : V) :
    completedSub hw0 hw1 u (root hw0 hw1 k u) =
      completedSmul hw0 hw1 (half^k) (stateQuotient hw0 hw1 k u) := by
  change defect hw0 hw1 k u =
    completedSmul hw0 hw1 (half^k)
      (completedSmul hw0 hw1 (Q'.ofNat (2^k)) (defect hw0 hw1 k u))
  calc
    defect hw0 hw1 k u = completedSmul hw0 hw1 1 (defect hw0 hw1 k u) :=
      (completedSmul_one hw0 hw1 _).symm
    _ = completedSmul hw0 hw1 (half^k * Q'.ofNat (2^k))
        (defect hw0 hw1 k u) :=
      completedSmul_congr hw0 hw1
        (Q'.eqv_symm (half_power_normalizes k)) (defect hw0 hw1 k u)
    _ = completedSmul hw0 hw1 (half^k)
        (completedSmul hw0 hw1 (Q'.ofNat (2^k)) (defect hw0 hw1 k u)) :=
      (completedSmul_mul hw0 hw1 (half^k) (Q'.ofNat (2^k))
        (defect hw0 hw1 k u)).symm

/-- For every requested error, all sufficiently fine original roots approach
their supplied input in the original completed squared distance. -/
theorem root_close
    (U Y : (PD).Cauchy) (modulus : Q' → Nat)
    (bound : ∀ (epsilon : Q'), (0 : Q') < epsilon → ∀ k,
      modulus epsilon ≤ k →
      RCle (d (stateQuotient hw0 hw1 k (Class U)) (Class Y)) (rat epsilon))
    (epsilon : Q') (he : (0 : Q') < epsilon) (k : Nat)
    (hk : rootModulus hw0 hw1 Y modulus epsilon ≤ k) :
    RCle (d (root hw0 hw1 k (Class U)) (Class U)) (rat epsilon) := by
  let cap := rootStateCap hw0 hw1 Y
  have hcap : (0 : Q') ≤ cap := rootStateCap_nonnegative hw0 hw1 Y
  have hmod : modulus 1 ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have htol : (linearTolerance cap hcap epsilon).den ≤ k :=
    Nat.le_trans (Nat.le_max_right _ _) hk
  let delta := linearTolerance cap hcap epsilon
  have hdelta : (0 : Q') < delta := linearTolerance_pos cap hcap he
  have hpow : half^k ≤ delta := Q'.le_trans' _ _ _ (pow_half_le_invSucc k)
    (Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le htol)
      (invSucc_den_le delta hdelta))
  have hnear := quotient_norm_cap hw0 hw1 U Y modulus bound k hmod
  have hnearCap : RCle
      (B (stateQuotient hw0 hw1 k (Class U))
        (stateQuotient hw0 hw1 k (Class U))) (rat cap) :=
    RCle_trans hnear (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_right _ _))
  have hbudget : half^k * cap ≤ epsilon := by
    have hmul : cap * delta ≤ epsilon := linearTolerance_budget cap hcap he
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hpow hcap) hmul)
  have hscaled := RCscale_mono (Q'.pow_nonneg half half_nonneg k) hnearCap
  have hrat : RCscale (half^k) (rat cap) = rat (half^k*cap) :=
    Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
  rw [hrat] at hscaled
  have hsmall : RCle
      (RCscale (half^k)
        (B (stateQuotient hw0 hw1 k (Class U))
          (stateQuotient hw0 hw1 k (Class U)))) (rat epsilon) :=
    RCle_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ => hbudget))
  have ha_nonneg : (0 : Q') ≤ half^k := Q'.pow_nonneg half half_nonneg k
  have ha_le_one : half^k ≤ 1 :=
    YMGap.Continuum.HKPos.pow_le_one half_nonneg (by decide) k
  have hsq : half^k * half^k ≤ half^k := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ ha_le_one ha_nonneg)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hdist : d (root hw0 hw1 k (Class U)) (Class U) =
      RCscale (half^k * half^k)
        (B (stateQuotient hw0 hw1 k (Class U))
          (stateQuotient hw0 hw1 k (Class U))) := by
    calc
      _ = d (Class U) (root hw0 hw1 k (Class U)) :=
        completedDist_symm hw0 hw1 _ _
      _ = B (completedSub hw0 hw1 (Class U) (root hw0 hw1 k (Class U)))
          (completedSub hw0 hw1 (Class U) (root hw0 hw1 k (Class U))) := rfl
      _ = B (completedSmul hw0 hw1 (half^k)
            (stateQuotient hw0 hw1 k (Class U)))
          (completedSmul hw0 hw1 (half^k)
            (stateQuotient hw0 hw1 k (Class U))) := by
          rw [stateQuotient_inverse_scale]
      _ = RCscale (half^k * half^k)
          (B (stateQuotient hw0 hw1 k (Class U))
            (stateQuotient hw0 hw1 k (Class U))) := by
          rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  rw [hdist]
  exact RCle_trans
    (RCscale_scalar_mono hsq
      (completedInner_nonnegative hw0 hw1
        (stateQuotient hw0 hw1 k (Class U)))) hsmall

#print axioms rootStateCap
#print axioms rootModulus
#print axioms root_close

end YMGap.Continuum.BF4WilsonAllNomeDerivativeRootContinuity
