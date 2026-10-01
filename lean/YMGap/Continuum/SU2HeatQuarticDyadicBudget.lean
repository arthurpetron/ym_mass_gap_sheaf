/-
# A subleading quartic budget with an explicit rational modulus

On the diagnostic heat schedule h=2^(-3m), S=2^(2m), the existing complete
head-plus-tail budget is at most 2968*2^(-4m), for m>=6. Hence the quartic
correction is o(h), with a computed tolerance cutoff. This bounds a genuine
original-weight insertion through the downstream consumer; it is NOT a
relative-variance estimate or a justified physical spacing trajectory.
-/

import YMGap.Continuum.SU2HeatQuarticDyadicSchedule
import YMGap.Continuum.SU2QuaternionHeatQuarticBound
import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy

namespace YMGap.Continuum.SU2HeatQuarticDyadicBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half half_nonneg pow_half_le)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.HeatKernelRGStep (ofNat_mul_eqv)
open YMGap.Continuum.SU2HeatQuarticDyadicSchedule
open YMGap.Continuum.SU2HeatQuarticBulkCoefficient (relativeBudget)
open YMGap.Continuum.SU2QuaternionHeatQuarticBound (quarticBudget)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (half_power_normalizes)

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem half_product (a b : Nat) : half^a * half^b ≈ half^(a+b) :=
  Q'.eqv_symm (Q'.pow_add_eqv half a b)

/-- Cancellation of the displayed dyadic dimension factor, not an estimate. -/
theorem dyadic_cancel (a b : Nat) :
    Q'.ofNat (2^a) * half^(a+b) ≈ half^b := by
  have hp : Q'.ofNat (2^a) * half^a ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (half_power_normalizes a)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.pow_add_eqv half a b))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hp) (Q'.one_mul_eqv _)))

private theorem exponent_dominates : ∀ m : Nat, 6 ≤ m → 10*m ≤ 2^m
  | 0, h => by omega
  | m+1, h => by
      by_cases hm : 6 ≤ m
      · have ih := exponent_dominates m hm
        rw [Nat.pow_succ]
        omega
      · have he : m = 5 := by omega
        subst m
        decide

private theorem square_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    a*a ≤ b*b :=
  Q'.mul_le_mul_of_nonneg hab hab (Q'.le_trans' _ _ _ ha hab) ha

private theorem fourth_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    (a*a)*(a*a) ≤ (b*b)*(b*b) :=
  square_mono (Q'.mul_nonneg _ _ ha ha) (square_mono ha hab)

private theorem defect_pin (m : Nat) : 1 + -(nome m) ≈ defect m :=
  poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
    (.var 0) (by decide) (fun _ => defect m)

private theorem split_defect (m : Nat) :
    Q'.ofNat (split m) * defect m ≈ half^m := by
  unfold split defect
  have he : 3*m = 2*m+m := by omega
  rw [he]
  exact dyadic_cancel (2*m) m

private theorem head_factor (m : Nat) :
    Q'.ofNat (split m+2) * defect m ≤ 3*half^m := by
  have hs : 1 ≤ split m := split_ge_one m
  have hn := CReal.ofNat_le_ofNat (show split m+2 ≤ 3*split m by omega)
  have hn' : Q'.ofNat (split m+2) ≤ 3*Q'.ofNat (split m) :=
    Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (ofNat_mul_eqv 3 (split m)))
  have he : (3*Q'.ofNat (split m))*defect m ≈ 3*half^m :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (split_defect m))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hn' (Q'.pow_nonneg half half_nonneg _))
    (Q'.le_of_eqv he)

private theorem head_fourth (m : Nat) :
    ((Q'.ofNat (split m+2)*Q'.ofNat (split m+2))*
      (Q'.ofNat (split m+2)*Q'.ofNat (split m+2)))*
      ((defect m*defect m)*(defect m*defect m)) ≤ 81*half^(4*m) := by
  let n := Q'.ofNat (split m+2)
  let h := defect m
  let r := half^m
  have hr : (r*r)*(r*r) ≈ half^(4*m) := by
    have he := Q'.eqv_trans _ _ _ (mul_congr (half_product m m) (half_product m m))
      (half_product (m+m) (m+m))
    simpa only [show (m+m)+(m+m)=4*m by omega] using he
  have hleft : ((n*n)*(n*n))*((h*h)*(h*h)) ≈ ((n*h)*(n*h))*((n*h)*(n*h)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
        (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => n | _ => h)
  have hright : ((3*r)*(3*r))*((3*r)*(3*r)) ≈ 81*half^(4*m) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.const 3) (.var 0)) (.mul (.const 3) (.var 0)))
          (.mul (.mul (.const 3) (.var 0)) (.mul (.const 3) (.var 0))))
        (.mul (.const 81) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))
        (by decide) (fun _ => r)) (Q'.mul_eqv_congr_left _ _ _ hr)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _
      (fourth_mono (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _)
        (Q'.pow_nonneg half half_nonneg _)) (head_factor m))
      (Q'.le_of_eqv hright))

private theorem defect_square (m : Nat) : defect m*defect m ≤ half^(4*m) := by
  have he : defect m*defect m ≈ half^(6*m) := by
    have h := half_product (3*m) (3*m)
    simpa only [show 3*m+3*m=6*m by omega] using h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (half_pow_antitone (4*m) (6*m) (by omega))

private theorem tail_budget (m : Nat) (hm : 6 ≤ m) :
    Q'.ofNat ((split m)^3) * RGTransport.qpow (nome m) (split m*split m) ≤
      half^(4*m) := by
  have hq := Q'.le_trans' _ _ _ (tail_guard hm)
    (half_pow_antitone (10*m) (2^m) (exponent_dominates m hm))
  have he : (split m)^3 = 2^(6*m) := by
    unfold split
    rw [← Nat.pow_mul, show (2*m)*3 = 6*m by omega]
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat ((split m)^3)) hq
    (Q'.ofNat_nonneg _)
  rw [he] at h
  have hc := dyadic_cancel (6*m) (4*m)
  rw [show 6*m+4*m=10*m by omega] at hc
  rw [he]
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hc)

/-- Explicit bound on the complete existing quartic budget. -/
theorem budget_bound (m : Nat) (hm : 6 ≤ m) :
    quarticBudget (nome m) (split m) ≤ 2968*half^(4*m) := by
  let h := defect m
  let n := Q'.ofNat (split m+2)
  let z := half^(4*m)
  have hb : relativeBudget n (1 + -(nome m)) ≈ relativeBudget n h :=
    Q'.add_eqv_congr'
      (mul_congr (Q'.eqv_refl _) (mul_congr
        (mul_congr (defect_pin m) (defect_pin m))
        (mul_congr (defect_pin m) (defect_pin m))))
      (Q'.mul_eqv_congr_left _ _ _ (mul_congr (defect_pin m) (defect_pin m)))
  have hfour : 32*((n*n)*(n*n))*((h*h)*(h*h)) ≤ 2592*z :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (32:Q') (head_fourth m) (by decide))
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.const 32) (.mul (.const 81) (.var 0)))
          (.mul (.const 2592) (.var 0)) (by decide) (fun _ => z))))
  have hsq : 296*(h*h) ≤ 296*z :=
    Q'.mul_le_mul_of_nonneg_left _ _ (296:Q') (defect_square m) (by decide)
  have ht : 80*Q'.ofNat ((split m)^3)*RGTransport.qpow (nome m) (split m*split m) ≤ 80*z :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ (80:Q') (tail_budget m hm) (by decide))
  have hsum : (2592*z+296*z)+80*z ≈ 2968*z :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.const 2592) (.var 0)) (.mul (.const 296) (.var 0)))
        (.mul (.const 80) (.var 0)))
      (.mul (.const 2968) (.var 0)) (by decide) (fun _ => z)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add (Q'.le_trans' _ _ _ (Q'.le_of_eqv hb) (Q'.add_le_add hfour hsq)) ht)
    (Q'.le_of_eqv hsum)

/-- Rational tolerance and a closed-form all-tail cutoff, retaining data. -/
def scaledTolerance (e : Q') : Q' := e * Q'.mkPos 1 2968 (by decide)

def smallModulus (e : Q') : Nat := max 6 (scaledTolerance e).den

theorem modulus_ge_six (e : Q') : 6 ≤ smallModulus e := Nat.le_max_left _ _

/-- The actual quartic budget is o(1-w), with its modulus returned above. -/
theorem budget_small (e : Q') (he : (0 : Q') < e) (m : Nat)
    (hm : smallModulus e ≤ m) :
    quarticBudget (nome m) (split m) ≤ e*defect m := by
  have htol : (0 : Q') < scaledTolerance e := Q'.mul_pos he (by decide)
  have hpow : half^m ≤ scaledTolerance e :=
    Q'.le_trans' _ _ _
      (half_pow_antitone (scaledTolerance e).den m
        (Nat.le_trans (Nat.le_max_right _ _) hm))
      (pow_half_le _ htol)
  have hc : 2968*scaledTolerance e ≈ e :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ e (by decide :
            (2968:Q')*Q'.mkPos 1 2968 (by decide) ≈ 1)) (Q'.one_mul_eqv e)))
  have hb : 2968*half^m ≤ e := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (2968:Q') hpow (by decide)) (Q'.le_of_eqv hc)
  have hp : 2968*half^(4*m) ≈ (2968*half^m)*defect m := by
    have hindex : 4*m=m+3*m := by omega
    rw [hindex]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.pow_add_eqv half m (3*m)))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  exact Q'.le_trans' _ _ _ (budget_bound m (Nat.le_trans (modulus_ge_six e) hm))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hb (Q'.pow_nonneg half half_nonneg _)))

#print axioms dyadic_cancel
#print axioms budget_bound
#print axioms scaledTolerance
#print axioms smallModulus
#print axioms modulus_ge_six
#print axioms budget_small

end YMGap.Continuum.SU2HeatQuarticDyadicBudget
