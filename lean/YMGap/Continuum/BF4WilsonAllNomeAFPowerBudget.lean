/-
# Explicit all-tail fixed-power budgets on the actual AF nome schedule

The actual rational schedule has `3*(j+1)*afGap j >= 1`. The existing
polynomial-geometric modulus therefore computes an index beyond which
`side j * (afGap j)^p` exceeds any supplied rational cap, for every FIXED
natural power p (including zero).

This is only a scalar selected-budget obstruction. A separate positive
Taylor payment with a nonzero fixed-power coefficient cannot meet an
`O(1/side)` budget solely by this scalar ceiling. No lower bound on the
actual energy or signed remainder, failure of cancellation, impossibility
of Yang--Mills, or physical-spacing calibration is asserted. The final
adaptive-power contrast is scalar as well, not a Taylor-error producer.
-/

import YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
import YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy
import YMGap.Continuum.PolynomialGeometricDecay
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.BF4WilsonAllNomeAFPowerBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
  (afE afGap afGap_den afGap_pos afGap_anti)
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (half_power_normalizes)
open YMGap.Continuum.PolynomialGeometricDecay
  (polynomialCutoff polynomial_bound)
open YMGap.Continuum.PartitionUpperBound (ofNat_pow_mul)
open YMGap.Continuum.ClusterCount (ofNat_mul_eqv)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- An actual denominator bound, including index zero. -/
theorem afGap_linear_floor (j : Nat) :
    (1 : Q') ≤ Q'.ofNat (3*(j+1))*afGap j := by
  have hlog : Nat.log2 (j+1) ≤ j := by
    have h := (Nat.log2_lt (n := j+1) (k := j+1) (by omega)).mpr
      Nat.lt_two_pow_self
    omega
  have he : afE j ≤ 172*j+484 := by
    unfold afE
    omega
  have hn : 1000*afE j ≤ (3*(j+1))*234982 := by omega
  show (1 : Int)*((Q'.ofNat (3*(j+1))*afGap j).den : Int) ≤
    (Q'.ofNat (3*(j+1))*afGap j).num*1
  rw [Q'.mul_den_cast, Q'.mul_num_cast, Q'.ofNat_den_cast, afGap_den]
  have hnum : (afGap j).num = 234982 := rfl
  rw [hnum]
  simp only [Q'.ofNat_num_cast, Int.one_mul, Int.mul_one]
  have hc := Int.ofNat_le.mpr hn
  simpa only [Int.natCast_mul] using hc

private def positiveCap (C : Q') : Q' := Q'.max' 0 C + 1

private theorem positiveCap_nonnegative (C : Q') :
    (0 : Q') ≤ positiveCap C := by
  have h : (0 : Q') + 1 ≤ positiveCap C :=
    Q'.add_le_add_right _ _ _ (Q'.le_max'_left 0 C)
  exact Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (0 : Q')+1) h

private theorem lt_add_one (q : Q') : q < q+1 := by
  show q.num*((q+1).den : Int) < (q+1).num*(q.den : Int)
  have h1n : (1 : Q').num = (1 : Int) := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  simp only [Q'.add_num_cast, Q'.add_den_cast, h1n, h1d,
    Int.mul_one, Int.one_mul]
  rw [Int.add_mul]
  have hd : (0 : Int) < (q.den : Int) := Int.ofNat_lt.mpr (Q'.den_pos q)
  have hs := Int.mul_pos hd hd
  omega

private theorem lt_positiveCap (C : Q') : C < positiveCap C :=
  Q'.lt_of_le_of_lt (Q'.le_max'_right 0 C) (lt_add_one (Q'.max' 0 C))

/-- Computed ALL-TAIL cutoff; its rational amplitude is positive even for a
negative supplied cap. No existential modulus is extracted. -/
def afPowerBudgetCutoff (p : Nat) (C : Q') : Nat :=
  polynomialCutoff half (positiveCap C * Q'.ofNat (3^p)) p half

private theorem power_factor_pin (p j : Nat) :
    (Q'.ofNat (3^p)*Q'.ofNat ((j+1)^p))*(afGap j)^p ≈
      (Q'.ofNat (3*(j+1))*afGap j)^p := by
  have hcast : Q'.ofNat (3^p)*Q'.ofNat ((j+1)^p) ≈
      Q'.ofNat ((3*(j+1))^p) := by
    rw [Nat.mul_pow]
    exact Q'.eqv_symm (ofNat_mul_eqv (3^p) ((j+1)^p))
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hcast)
    (ofNat_pow_mul (3*(j+1)) (afGap j) p)

/-- Every index past the explicit cutoff beats the supplied cap. The power
is fixed before choosing the cutoff, and zero is admitted. -/
theorem afPowerBudget_gt (p : Nat) (C : Q') (j : Nat)
    (hj : afPowerBudgetCutoff p C ≤ j) :
    C < Q'.ofNat (side j)*(afGap j)^p := by
  let B := Q'.ofNat (side j)*(afGap j)^p
  let A := positiveCap C * Q'.ofNat (3^p)
  have hB : (0 : Q') ≤ B := Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _)
    (Q'.pow_nonneg _ (Q'.le_of_lt (afGap_pos j)) p)
  have hA : (0 : Q') ≤ A := Q'.mul_nonneg _ _
    (positiveCap_nonnegative C) (Q'.ofNat_nonneg _)
  have hsmall : half^j*(A*Q'.ofNat ((j+1)^p)) ≤ half :=
    polynomial_bound half_nonneg (by decide : half < (1 : Q')) hA
      (by decide : (0 : Q') < half) p j hj
  have hpaid := Q'.mul_le_mul_of_nonneg_right _ _ B hsmall hB
  have hnormalize :
      (half^j*(A*Q'.ofNat ((j+1)^p)))*B ≈
        positiveCap C * (Q'.ofNat (3*(j+1))*afGap j)^p := by
    have hshuffle :
        (half^j*(A*Q'.ofNat ((j+1)^p)))*B ≈
          (half^j*Q'.ofNat (side j)) *
            (positiveCap C *
              ((Q'.ofNat (3^p)*Q'.ofNat ((j+1)^p))*(afGap j)^p)) := by
      dsimp only [A, B]
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
          (.mul (.var 4) (.var 5)))
        (.mul (.mul (.var 0) (.var 4))
          (.mul (.var 1) (.mul (.mul (.var 2) (.var 3)) (.var 5))))
        (by decide) (fun
          | 0 => half^j
          | 1 => positiveCap C
          | 2 => Q'.ofNat (3^p)
          | 3 => Q'.ofNat ((j+1)^p)
          | 4 => Q'.ofNat (side j)
          | _ => (afGap j)^p)
    have hn : half^j*Q'.ofNat (side j) ≈ 1 := half_power_normalizes j
    exact Q'.eqv_trans _ _ _ hshuffle
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hn)
        (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
          (Q'.mul_eqv_congr_left _ _ _ (power_factor_pin p j))))
  have hfloor : positiveCap C ≤
      positiveCap C * (Q'.ofNat (3*(j+1))*afGap j)^p :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (TotalMajorantClose.one_le_qpow (afGap_linear_floor j) p)
        (positiveCap_nonnegative C))
  have hhalf : half*B ≤ B := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ B
      (by decide : half ≤ (1 : Q')) hB)
    (Q'.le_of_eqv (Q'.one_mul_eqv B))
  exact ClusteringImpliesGap.lt_of_lt_of_le (lt_positiveCap C)
    (Q'.le_trans' _ _ _ hfloor
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hnormalize)
        (Q'.le_trans' _ _ _ hpaid hhalf)))

/-- No eventual uniform scalar cap for ANY fixed natural power. This says
nothing about a signed interacting energy or a cancellation order. -/
theorem afPowerBudget_no_uniform_cap (p : Nat) (C : Q') (start : Nat) :
    ¬ (∀ j, start ≤ j → Q'.ofNat (side j)*(afGap j)^p ≤ C) := by
  intro h
  let j := max start (afPowerBudgetCutoff p C)
  have hgt := afPowerBudget_gt p C j (Nat.le_max_right _ _)
  have hle := h j (Nat.le_max_left _ _)
  exact ClusteringImpliesGap.lt_irrefl' C
    (ClusteringImpliesGap.lt_of_lt_of_le hgt hle)

/-- In contrast, the index-dependent power j has a bounded scalar budget.
This is not a constructed high-order Taylor or interacting-source estimate. -/
theorem afPowerBudget_adaptive_le_one (j : Nat) :
    Q'.ofNat (side j)*(afGap j)^j ≤ (1 : Q') := by
  have hgap : ∀ n : Nat, afGap n ≤ half := by
    intro n
    induction n with
    | zero => decide
    | succ n ih => exact Q'.le_trans' _ _ _ (afGap_anti n) ih
  have hp := TotalMajorantClose.pow_le_pow_base
    (Q'.le_of_lt (afGap_pos j)) (hgap j) j
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hp (Q'.ofNat_nonneg _))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_of_eqv (half_power_normalizes j)))

#print axioms afGap_linear_floor
#print axioms afPowerBudgetCutoff
#print axioms afPowerBudget_gt
#print axioms afPowerBudget_no_uniform_cap
#print axioms afPowerBudget_adaptive_le_one

end YMGap.Continuum.BF4WilsonAllNomeAFPowerBudget
