/-
# Exact face-ratio exponent for the chronological cost

This only identifies the already-checked positive finite comparison
coefficient. The exponent has two copies of every crossing or incident face;
no larger exponent and no cutoff-dependent quantity is introduced.
-/

import YMGap.Continuum.BF4ExactSlabChronologicalCostBound
import YMGap.Constructive.CRealLogRatCongruence
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.BF4ExactSlabChronologicalCostPower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabChronologicalCostBound

local infix:50 " ≈ " => Q'.eqv

private theorem mul_pow_eqv (a b : Q') : ∀ n : Nat,
    (a*b)^n ≈ a^n*b^n
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | n+1 => by
      have ih := mul_pow_eqv a b n
      show (a*b)*(a*b)^n ≈ (a*a^n)*(b*b^n)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (a*b) _ _ ih) (by ring_qeqv)

private theorem one_pow_eqv_one : ∀ n : Nat, ((1 : Q')^n) ≈ 1
  | 0 => Q'.eqv_refl 1
  | n+1 => by
      change (1 : Q') * 1^n ≈ 1
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 1 _ _ (one_pow_eqv_one n))
        (Q'.one_mul_eqv 1)

/-- The product of a cut-square power and two six-star powers has exactly
the exponent used in the area budget. -/
theorem paired_power_pin (q : Q') (C : Nat) :
    (q*q)^C * (q^6*q^6) ≈ q^(2*C+12) := by
  have hnat : (C+6)+(C+6) = 2*C+12 := by omega
  calc
    (q*q)^C * (q^6*q^6)
        ≈ (q^C*q^C)*(q^6*q^6) :=
          Q'.mul_eqv_congr_right _ _ _ (mul_pow_eqv q q C)
    _ ≈ (q^C*q^6)*(q^C*q^6) := by ring_qeqv
    _ ≈ q^(C+6)*(q^C*q^6) :=
      Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.pow_add_eqv q C 6))
    _ ≈ q^(C+6)*q^(C+6) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.pow_add_eqv q C 6))
    _ ≈ q^((C+6)+(C+6)) := Q'.eqv_symm (Q'.pow_add_eqv q (C+6) (C+6))
    _ = q^(2*C+12) := by rw [hnat]

/-- The positive area cost is precisely the indicated face ratio raised to
two copies of the area-crossing count plus twelve incident-star factors. -/
theorem areaCost_eqv_faceRatio_pow {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) :
    areaCost hw0 hw1 extent ≈
      (faceRatio hw0 hw1)^(2*areaFaces extent+12) := by
  let ell := headFloor w
  let U := prefixCap w
  let d := areaFaces extent
  let E := 2*d+12
  let r := Q'.recipPos ell (headFloor_positive hw0 hw1)
  let cost := areaCost hw0 hw1 extent
  let floor := areaFloor w extent
  let cap := areaCap w extent
  have hf : (0 : Q') < floor := areaFloor_positive hw0 hw1 extent
  have hfloor : floor ≈ ell^E := paired_power_pin ell d
  have hcap : cap ≈ U^E := paired_power_pin U d
  have hr : r*ell ≈ 1 := Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv r ell) (Q'.mul_recipPos_eqv ell (headFloor_positive hw0 hw1))
  have hrpow : r^E*ell^E ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (mul_pow_eqv r ell E))
      (Q'.eqv_trans _ _ _ (Q'.pow_eqv_congr hr E) (one_pow_eqv_one E))
  have hcost : cost*floor ≈ cap := by
    change (Q'.recipPos floor hf * cap)*floor ≈ cap
    calc
      (Q'.recipPos floor hf * cap)*floor
          ≈ cap*(floor*Q'.recipPos floor hf) := by ring_qeqv
      _ ≈ cap*1 := Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv floor hf)
      _ ≈ cap := Q'.mul_one_eqv _
  have hpow : (faceRatio hw0 hw1)^E*floor ≈ cap := by
    change (r*U)^E*floor ≈ cap
    calc
      (r*U)^E*floor ≈ (r*U)^E*ell^E := Q'.mul_eqv_congr_left _ _ _ hfloor
      _ ≈ (r^E*U^E)*ell^E :=
        Q'.mul_eqv_congr_right _ _ _ (mul_pow_eqv r U E)
      _ ≈ U^E*(r^E*ell^E) := by ring_qeqv
      _ ≈ U^E*1 := Q'.mul_eqv_congr_left _ _ _ hrpow
      _ ≈ U^E := Q'.mul_one_eqv _
      _ ≈ cap := Q'.eqv_symm hcap
  have hboth : floor*cost ≈ floor*(faceRatio hw0 hw1)^E := by
    calc
      floor*cost ≈ cost*floor := Q'.mul_comm_eqv _ _
      _ ≈ cap := hcost
      _ ≈ (faceRatio hw0 hw1)^E*floor := Q'.eqv_symm hpow
      _ ≈ floor*(faceRatio hw0 hw1)^E := Q'.mul_comm_eqv _ _
  exact Q'.mul_left_cancel_of_pos hf hboth

#print axioms paired_power_pin
#print axioms areaCost_eqv_faceRatio_pow

end YMGap.Continuum.BF4ExactSlabChronologicalCostPower
