/-
# Diagnostic dyadic-time, harmonic-nome schedule for one Wilson defect

The scalar nome below is a proposed test schedule, not a Yang--Mills
continuum trajectory. Exponential physical-time steps beat the degree-24
normalization cost of this SAME literal completed defect.
-/

import YMGap.Continuum.BF4RelativePredictionNomeBudget
import YMGap.Continuum.BF4WilsonAllNomePolynomialDefectBudget
import YMGap.Continuum.PolynomialGeometricDecay
import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
import YMGap.Continuum.AFRateCalibration
import YMGap.Constructive.CRealLogRatCongruence
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.BF4WilsonNomeDyadicDefectSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.TotalMajorantClose
open YMGap.Continuum.PartitionUpperBound (ofNat_pow_mul)
open YMGap.Continuum.BF4RelativePredictionNomeBudget (cubicDeficit)
open YMGap.Continuum.BF4WilsonAllNomePolynomialDefectBudget
  (polynomialNormBudget polynomialNormBudget_positive normWeight)
open YMGap.Continuum.PolynomialGeometricDecay (polynomialCutoff polynomial_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (half_power_normalizes)
open YMGap.Continuum.AFRateCalibration (one_sub_one_sub_eqv)

local infix:50 " ≈ " => Q'.eqv

/-- A harmonic nome approaching one. No physical lattice spacing is assigned. -/
def nome (j : Nat) : Q' := 1 + -Q'.invSucc (j+1)

/-- Dyadic physical-time step count for the diagnostic test. -/
def steps (j : Nat) : Nat := 2^(j+1)

/-- Candidate spacing, displayed only to record `steps * spacing ≈ 1`. -/
def spacing (j : Nat) : Q' := HalfPow.half^(j+1)

theorem nome_positive (j : Nat) : (0 : Q') < nome j := by
  have h : Q'.invSucc (j+1) ≤ Q'.invSucc 1 := ExpNeg.invSucc_le_of_le (by omega)
  exact HKPos.one_sub_pos (HKPos.q_lt_of_le_of_lt h (by decide))

theorem nome_lt_one (j : Nat) : nome j < (1 : Q') :=
  BakryEmery.one_sub_lt_one (Q'.invSucc_pos (j+1))

theorem steps_spacing_normalizes (j : Nat) :
    Q'.ofNat (steps j) * spacing j ≈ 1 := by
  unfold steps spacing
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (half_power_normalizes (j+1))

private theorem half_pow_num : ∀ k : Nat, (HalfPow.half^k).num = 1
  | 0 => rfl
  | k+1 => by
      change (HalfPow.half * HalfPow.half^k).num = 1
      rw [Q'.mul_num_cast, half_pow_num k]
      rfl

private theorem half_pow_den : ∀ k : Nat, (HalfPow.half^k).den = 2^k
  | 0 => rfl
  | k+1 => by
      change 2 * (HalfPow.half^k).den = 2^(k+1)
      rw [half_pow_den k, Nat.pow_succ]
      exact Nat.mul_comm 2 (2^k)

private theorem reciprocal_dyadic_le_half (k : Nat) :
    Q'.invSucc (2^k) ≤ HalfPow.half^k := by
  show (Q'.invSucc (2^k)).num * ((HalfPow.half^k).den : Int) ≤
    (HalfPow.half^k).num * ((Q'.invSucc (2^k)).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_den, half_pow_num, half_pow_den]
  push_cast
  omega

private theorem deficit_pin (j : Nat) :
    (1 : Q') + -(nome j) ≈ Q'.invSucc (j+1) := by
  change (1 : Q') + -(1 + -Q'.invSucc (j+1)) ≈ Q'.invSucc (j+1)
  exact one_sub_one_sub_eqv _

private theorem cubic_pin (j : Nat) :
    cubicDeficit (nome j) ≈ (Q'.invSucc (j+1))^3 := by
  let x := Q'.invSucc (j+1)
  have hd := deficit_pin j
  change ((1 + -nome j)*(1 + -nome j))*(1 + -nome j) ≈ x^3
  have hpair := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hd)
    (Q'.mul_eqv_congr_left _ _ _ hd)
  have h := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hpair)
    (Q'.mul_eqv_congr_left _ _ _ hd)
  refine Q'.eqv_trans _ _ _ h ?_
  change (x*x)*x ≈ x*(x*(x*1))
  exact poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 0)) (.var 0))
    (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.const 1))))
    (by decide) (fun _ => x)

theorem normWeight_nome_pin (j : Nat) :
    normWeight (nome j) ≈ (Q'.invSucc (j+1))^24 := by
  let x := Q'.invSucc (j+1)
  let d := cubicDeficit (nome j)
  have hc : d ≈ x^3 := cubic_pin j
  have hp := Q'.pow_eqv_congr hc 4
  have h12 : d^4 ≈ x^12 := Q'.eqv_trans _ _ _ hp
    (by simpa only [show 3*4=12 by decide] using pow_mul x 3 4)
  change d^4 * d^4 ≈ x^24
  have hboth := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h12)
    (Q'.mul_eqv_congr_left _ _ _ h12)
  exact Q'.eqv_trans _ _ _ hboth
    (Q'.eqv_symm (by simpa only [show 12+12=24 by decide] using Q'.pow_add_eqv x 12 12))

private theorem denominator_pin (k : Nat) :
    Q'.ofNat ((k+1)^24) * (Q'.invSucc k)^24 ≈ 1 := by
  have hbase : Q'.ofNat (k+1) * Q'.invSucc k ≈ 1 :=
    Q'.ofNat_succ_mul_invSucc k
  exact Q'.eqv_trans _ _ _ (ofNat_pow_mul (k+1) (Q'.invSucc k) 24)
    (Q'.eqv_trans _ _ _ (Q'.pow_eqv_congr hbase 24) (by decide))

/-- Constructive cutoff for the diagnostic scalar schedule. -/
def scaleModulus (epsilon : Q') : Nat :=
  polynomialCutoff (HalfPow.half * HalfPow.half)
    (4 * polynomialNormBudget) 24 epsilon

/-- At the displayed schedule the absolute orbit coefficient is at most
epsilon times the SAME source's nome-weight. No continuum scaling claim. -/
theorem scalar_budget (epsilon : Q') (he : (0 : Q') < epsilon)
    (j : Nat) (hj : scaleModulus epsilon ≤ j) :
    ((Q'.invSucc (steps j) * Q'.invSucc (steps j))*4)*polynomialNormBudget ≤
      epsilon * normWeight (nome j) := by
  let k := j+1
  let x := Q'.invSucc k
  let r := Q'.invSucc (steps j)
  let b := HalfPow.half^k
  let C := 4 * polynomialNormBudget
  let D := Q'.ofNat ((k+1)^24)
  have hr : r ≤ b := reciprocal_dyadic_le_half k
  have hr0 : (0 : Q') ≤ r := Q'.invSucc_nonneg _
  have hb0 : (0 : Q') ≤ b := Q'.pow_nonneg _ HalfPow.half_nonneg _
  have hC0 : (0 : Q') ≤ C := Q'.le_of_lt
    (Q'.mul_pos (by decide : (0 : Q') < 4) polynomialNormBudget_positive)
  have hsquare : r*r ≤ b*b := HKConv.mul_le_mul' hr0 hb0 hr hr
  have hA : ((r*r)*4)*polynomialNormBudget * D ≤
      ((b*b)*4)*polynomialNormBudget * D := by
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare (by decide))
        (Q'.le_of_lt polynomialNormBudget_positive))
      (ClusterCount.ofNat_nonneg _)
  have hpoly : (HalfPow.half*HalfPow.half)^k *
      (C * Q'.ofNat ((k+1)^24)) ≤ epsilon :=
    polynomial_bound
      (Q'.mul_nonneg _ _ HalfPow.half_nonneg HalfPow.half_nonneg)
      (by decide : HalfPow.half*HalfPow.half < (1 : Q'))
      hC0 he 24 k (by
        change scaleModulus epsilon ≤ j+1
        exact Nat.le_trans hj (Nat.le_succ j))
  have hbpow : b*b ≈ (HalfPow.half*HalfPow.half)^k :=
    Q'.eqv_symm (mul_pow HalfPow.half HalfPow.half k)
  have hshape : ((b*b)*4)*polynomialNormBudget * D ≈
      (HalfPow.half*HalfPow.half)^k * (C*D) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hbpow)))
      (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.var 0) (.const 4)) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.mul (.const 4) (.var 1)) (.var 2)))
        (by decide) (fun
          | 0 => (HalfPow.half*HalfPow.half)^k
          | 1 => polynomialNormBudget
          | _ => D))
  have hfactor : ((r*r)*4)*polynomialNormBudget * D ≤ epsilon :=
    Q'.le_trans' _ _ _ hA (Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape) hpoly)
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _ hfactor
    (Q'.pow_nonneg x (Q'.invSucc_nonneg k) 24)
  have hden := denominator_pin k
  have hleft : ((((r*r)*4)*polynomialNormBudget * D)*x^24) ≈
      ((r*r)*4)*polynomialNormBudget := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hden)
        (Q'.mul_one_eqv _))
  have hright : epsilon*x^24 ≈ epsilon*normWeight (nome j) :=
    Q'.mul_eqv_congr_left epsilon _ _ (Q'.eqv_symm (normWeight_nome_pin j))
  change ((r*r)*4)*polynomialNormBudget ≤ epsilon*normWeight (nome j)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hright))

#print axioms nome
#print axioms steps
#print axioms spacing
#print axioms nome_positive
#print axioms nome_lt_one
#print axioms steps_spacing_normalizes
#print axioms normWeight_nome_pin
#print axioms scaleModulus
#print axioms scalar_budget

end YMGap.Continuum.BF4WilsonNomeDyadicDefectSchedule
