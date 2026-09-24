/-
# Absorption of the finite SU(2) fusion endpoint

The elementary sufficient heat cutoff is large enough that the retained
lower neighbour absorbs the otherwise unmatched upper fusion endpoint.
This is scalar arithmetic only; the quadratic-form consumer is separate.
-/

import YMGap.Continuum.SU2HeatCutoffCasimirBound
import YMGap.Continuum.SU2HeatFusionCutoffError
import YMGap.Continuum.ReciprocalBernoulliUpper

namespace YMGap.Continuum.SU2HeatFusionCutoffPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.ReciprocalBernoulliUpper

local infix:50 " ≈ " => Q'.eqv

/-- The computed cutoff is a positive label. -/
theorem one_le_cutoff {w : Q'} (_hw1 : w < (1 : Q')) {K : Nat}
    (hK : sufficientCutoff w ≤ K) : 1 ≤ K := by
  have hd : 1 ≤ ((1 : Q')-w).den := ((1 : Q')-w).den_pos
  exact Nat.le_trans hd hK

/-- The denominator cutoff pays one full unit of linear nome defect. -/
theorem one_le_defect_mul_cutoff {w : Q'} (hw1 : w < (1 : Q')) {K : Nat}
    (hK : sufficientCutoff w ≤ K) :
    (1 : Q') ≤ ((1 : Q')-w) * Q'.ofNat K := by
  let d := (1 : Q')-w
  have hdpos : (0 : Q') < d := HKPos.one_sub_pos hw1
  have hnum : (1 : Int) ≤ d.num := by
    have := Q'.num_pos_of_pos hdpos
    omega
  have hden : d.den ≤ K := by simpa only [d, sufficientCutoff] using hK
  show (1 : Q').num * (((d * Q'.ofNat K).den : Nat) : Int) ≤
    (d * Q'.ofNat K).num * ((1 : Q').den : Int)
  show (1 : Int) * ((d.den : Int) * 1) ≤
    (d.num * (K : Int)) * (1 : Int)
  simp only [Int.one_mul, Int.mul_one]
  have hden' : (d.den : Int) ≤ (K : Int) := Int.ofNat_le.mpr hden
  have hK0 : (0 : Int) ≤ (K : Int) := Int.natCast_nonneg K
  have hscaled : (K : Int) ≤ d.num * (K : Int) := by
    simpa only [Int.one_mul] using Int.mul_le_mul_of_nonneg_right hnum hK0
  exact Int.le_trans hden' hscaled

private theorem endpoint_power_bound {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) {K : Nat} (hK : sufficientCutoff w ≤ K) :
    Q'.ofNat (2*(K+1)) * qpow w (2*K+4) ≤ Q'.ofNat K := by
  let u := (1 : Q')-w
  let n := 2*K+4
  have hu0 : (0 : Q') ≤ u := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hu1 : u ≤ (1 : Q') := by
    dsimp only [u]
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 (-w) 0 (Q'.neg_le_neg hw0))
      (Q'.le_of_eqv (by decide : (1 : Q') + 0 ≈ 1))
  have hunit := one_le_defect_mul_cutoff hw1 hK
  have hden : Q'.ofNat (2*(K+1)) ≤ Q'.ofNat K * bernDen u n := by
    have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat n)
      hunit (Q'.ofNat_nonneg n)
    have hs' : Q'.ofNat n ≤ Q'.ofNat n * (u * Q'.ofNat K) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv (Q'.ofNat n))) hs
    exact Q'.le_trans' _ _ _
      (CReal.ofNat_le_ofNat (by dsimp [n]; omega))
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.ofNat_add_eqv K n))
        (Q'.le_trans' _ _ _
          (Q'.add_le_add (Q'.le_refl' _) hs')
          (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
            (.add (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 0))))
            (.mul (.var 0) (.add (.const 1) (.mul (.var 1) (.var 2))))
            (by decide)
            (fun | 0 => Q'.ofNat K | 1 => Q'.ofNat n | _ => u)))))
  have hp := oneSub_pow_mul_bernDen_le hu0 hu1 n
  have hwbase : (oneSub u).eqv w := by
    dsimp only [u, oneSub]
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) (fun _ => w)
  have qpow_congr : ∀ {a b : Q'}, a.eqv b → ∀ m,
      (qpow a m).eqv (qpow b m) := by
    intro a b hab m
    induction m with
    | zero => exact Q'.eqv_refl _
    | succ m ih =>
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ a ih)
          (Q'.mul_eqv_congr_left _ _ _ hab)
  have hpow : (qpow (oneSub u) n).eqv (qpow w n) := qpow_congr hwbase n
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (qpow w n) hden
    (qpow_nonneg w hw0 n)
  exact Q'.le_trans' _ _ _ hm
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (Q'.ofNat K) (bernDen u n) (qpow w n))
        (Q'.mul_eqv_congr_left (Q'.ofNat K) _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
            (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hpow))))))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat K) hp (Q'.ofNat_nonneg K))
        (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.ofNat K)))))

/-- At the computed cutoff, the retained lower neighbour absorbs the literal
upper endpoint of fundamental SU(2) fusion. -/
theorem endpoint_coeff_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) {K : Nat} (hK : sufficientCutoff w ≤ K) :
    coeffW w 1 * coeffW w K ≤ coeffW w (K-1) := by
  have hK1 := one_le_cutoff hw1 hK
  have hp := endpoint_power_bound hw0 hw1 hK
  unfold coeffW dimQ c4
  have he : 1 * (1+2) + K*(K+2) = (K-1)*(K-1+2) + (2*K+4) := by
    cases K with
    | zero => omega
    | succ k =>
        simp only [Nat.add_sub_cancel, Nat.mul_add, Nat.add_mul]
        omega
  have hpow := HeatKernelRGStep.qpow_add w ((K-1)*(K-1+2)) (2*K+4)
  have hcombine :
      (qpow w 3 * qpow w (K*(K+2))).eqv
        (qpow w ((K-1)*(K-1+2)) * qpow w (2*K+4)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (HeatKernelRGStep.qpow_add w 3 (K*(K+2)))) ?_
    rw [he]
    exact hpow
  have hleft :
      (Q'.ofNat (1+1) * qpow w (1*(1+2))) *
          (Q'.ofNat (K+1) * qpow w (K*(K+2))) ≈
        qpow w ((K-1)*(K-1+2)) *
          (Q'.ofNat (2*(K+1)) * qpow w (2*K+4)) := by
    exact Q'.eqv_trans _ _ _
      (RingNormaliser.poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.const 2) (.var 1)) (.mul (.var 0) (.var 2)))
        (by decide)
        (fun
          | 0 => qpow w 3 | 1 => Q'.ofNat (K+1)
          | _ => qpow w (K*(K+2))))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 2 (K+1))))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat (2*(K+1))) _ _ hcombine)
          (RingNormaliser.poly_identity_of_normal_eq
            (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
            (fun
              | 0 => Q'.ofNat (2*(K+1))
              | 1 => qpow w ((K-1)*(K-1+2))
              | _ => qpow w (2*K+4)))))
  have hKpred : K-1+1=K := by omega
  have hfinal :
      (qpow w ((K-1)*(K-1+2)) * Q'.ofNat K).eqv
        (Q'.ofNat (K-1+1) * qpow w ((K-1)*(K-1+2))) := by
    rw [hKpred]
    exact Q'.mul_comm_eqv _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hp
        (qpow_nonneg w hw0 ((K-1)*(K-1+2))))
      (Q'.le_of_eqv hfinal))

end YMGap.Continuum.SU2HeatFusionCutoffPositive

#print axioms YMGap.Continuum.SU2HeatFusionCutoffPositive.one_le_cutoff
#print axioms YMGap.Continuum.SU2HeatFusionCutoffPositive.one_le_defect_mul_cutoff
#print axioms YMGap.Continuum.SU2HeatFusionCutoffPositive.endpoint_coeff_le
