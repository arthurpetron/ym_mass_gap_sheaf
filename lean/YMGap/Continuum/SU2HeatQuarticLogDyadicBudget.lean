/-
# A logarithmically split original heat-quartic budget

This is a scalar diagnostic schedule, not a physical spacing trajectory.  At
`w = nome (2*r)` the nome defect is `2^(-6*r)`.  The moving split
`r*2^(3*r)` makes the retained head fourth order up to a polynomial in `r`,
while its squared-spin tail is paid by `2^(-r*r)`.  No source or variance is
changed or estimated in this module.
-/

import YMGap.Continuum.SU2HeatQuarticDyadicBudget

namespace YMGap.Continuum.SU2HeatQuarticLogDyadicBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.HeatKernelRGStep (qpow_qpow ofNat_mul_eqv)
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.R1CornerAtoms (oneSub_qpow_le)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (half_power_normalizes)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)
open YMGap.Continuum.RouteDHigherRepTail (qpow_base_mono)
open YMGap.Continuum.SU2HeatQuarticDyadicSchedule
open YMGap.Continuum.SU2HeatQuarticDyadicBudget (dyadic_cancel)
open YMGap.Continuum.SU2HeatQuarticBulkCoefficient (relativeBudget)
open YMGap.Continuum.SU2QuaternionHeatQuarticBound (quarticBudget)

local infix:50 " ≈ " => Q'.eqv

/-- The explicit square-root-of-the-heat-scale split with a polynomial margin. -/
def logSplit (r : Nat) : Nat := r * 2^(3*r)

def logNome (r : Nat) : Q' := nome (2*r)

def logDefect (r : Nat) : Q' := defect (2*r)

def logRate (r : Nat) : Q' :=
  888*(Q'.ofNat (r^4)*(logDefect r*logDefect r))

/-- A fixed, computable onset suffices for all scalar guards and the tail. -/
def logOnset : Nat := 22

theorem logNome_pos (r : Nat) (hr : logOnset ≤ r) :
    (0 : Q') < logNome r := by
  exact nome_pos (by unfold logOnset at hr; omega : 6 ≤ 2*r)

theorem logNome_lt_one (r : Nat) : logNome r < (1 : Q') :=
  nome_lt_one (2*r)

theorem logSplit_ge_one (r : Nat) (hr : logOnset ≤ r) :
    1 ≤ logSplit r := by
  have hp : 1 ≤ 2^(3*r) := Nat.pow_pos (by decide)
  have hm := Nat.mul_le_mul_left r hp
  unfold logSplit logOnset at *
  omega

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem half_product (a b : Nat) : half^a * half^b ≈ half^(a+b) :=
  Q'.eqv_symm (Q'.pow_add_eqv half a b)

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

private theorem defect_pin (r : Nat) :
    1 + -(nome (2*r)) ≈ defect (2*r) := by
  unfold nome
  exact poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
    (.var 0) (by decide) (fun _ => defect (2*r))

private theorem defect_square (r : Nat) :
    defect (2*r) * defect (2*r) ≈ half^(12*r) := by
  unfold defect
  have he : 3*(2*r)+3*(2*r)=12*r := by omega
  exact Q'.eqv_trans _ _ _ (half_product _ _) (by rw [he]; exact Q'.eqv_refl _)

private theorem exp_dominates : ∀ r : Nat, logOnset ≤ r → 16*r ≤ 2^(3*r)
  | 0, h => by omega
  | r+1, h => by
      by_cases hr : logOnset ≤ r
      · have ih := exp_dominates r hr
        rw [show 3*(r+1)=3*r+3 by omega, Nat.pow_add]
        change 16*(r+1) ≤ 2^(3*r)*8
        have hp : 1 ≤ 2^(3*r) := Nat.pow_pos (by decide)
        change 22 ≤ r at hr
        omega
      · have he : r=21 := by unfold logOnset at *; omega
        subst r
        decide

private theorem split_ge_two (r : Nat) (hr : logOnset ≤ r) :
    2 ≤ logSplit r := by
  have hp : 1 ≤ 2^(3*r) := Nat.pow_pos (by decide)
  have hm := Nat.mul_le_mul_left r hp
  unfold logSplit
  unfold logOnset at hr
  omega

private theorem half_guard_natural (r : Nat) (hr : logOnset ≤ r) :
    2*(4*(logSplit r+2)) ≤ 2^(6*r) := by
  let P := 2^(3*r)
  have hP : 16*r ≤ P := exp_dominates r hr
  have hS : 2 ≤ logSplit r := split_ge_two r hr
  have hfirst : 8*(logSplit r+2) ≤ 16*logSplit r := by omega
  have hmul := Nat.mul_le_mul_left P hP
  have hpow : P*P = 2^(6*r) := by
    dsimp [P]
    rw [← Nat.pow_add]
    congr 1
    omega
  have hmiddle : 16*logSplit r ≤ P*P := by
    calc
      16*logSplit r = P*(16*r) := by dsimp [logSplit, P]; ac_rfl
      _ ≤ P*P := hmul
  calc
    2*(4*(logSplit r+2)) = 8*(logSplit r+2) := by omega
    _ ≤ 16*logSplit r := hfirst
    _ ≤ P*P := hmiddle
    _ = 2^(6*r) := hpow

private theorem defect_mul_guard_le_half (r : Nat) (hr : logOnset ≤ r) :
    Q'.ofNat (4*(logSplit r+2)) * defect (2*r) ≤ half := by
  change ((4*(logSplit r+2) : Nat) : Int) * (HalfPow.half^(3*(2*r))).num * 2 ≤
    1 * ((1 * (HalfPow.half^(3*(2*r))).den : Nat) : Int)
  rw [show 3*(2*r)=6*r by omega, half_pow_num, half_pow_den]
  simp only [Int.mul_one, Int.one_mul, Nat.one_mul]
  have hnat : (4*(logSplit r+2))*2 ≤ 2^(6*r) := by
    simpa only [Nat.mul_comm] using half_guard_natural r hr
  exact_mod_cast hnat

/-- The selected middle spin remains in the finite heat half corridor. -/
theorem logHalf_guard (r : Nat) (hr : logOnset ≤ r) :
    (1 : Q') ≤ 2*(nome (2*r))^(4*(logSplit r+2)) := by
  let k := 4*(logSplit r+2)
  let x := qpow (nome (2*r)) k
  have hm : 6 ≤ 2*r := by unfold logOnset at hr; omega
  have hw0 := Q'.le_of_lt (nome_pos hm)
  have hw1 := Q'.le_of_lt (nome_lt_one (2*r))
  have hlin : (1 : Q') + -x ≤ Q'.ofNat k * defect (2*r) :=
    Q'.le_trans' _ _ _ (oneSub_qpow_le hw0 hw1 k)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (defect_pin r)))
  have hraw : (1 : Q') + -x ≤ half :=
    Q'.le_trans' _ _ _ hlin (defect_mul_guard_le_half r hr)
  have hadd := Q'.add_le_add_right _ _ (x + -half) hraw
  have hl : ((1 : Q') + -x) + (x + -half) ≈ half := by
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.const 1) (.neg (.var 0)))
          (.add (.var 0) (.neg (.var 1))))
        (.add (.const 1) (.neg (.var 1)))
        (by decide) (fun | 0 => x | _ => half))
      (by decide : (1 : Q') + -half ≈ half)
  have hr' : half + (x + -half) ≈ x :=
    poly_identity_of_normal_eq
      (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (.var 0)
      (by decide) (fun | 0 => x | _ => half)
  have hx : half ≤ x :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hl))
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hr'))
  have htwice := Q'.mul_le_mul_of_nonneg_left _ _ 2 hx (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (1 : Q') ≈ 2*half))
    (Q'.le_trans' _ _ _ htwice
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left 2 _ _ (qpow_eqv_pow (nome (2*r)) k))))

private theorem block_defect (r : Nat) :
    defect (2*r) * Q'.ofNat (2^(6*r)) ≈ 1 := by
  unfold defect
  simpa only [show 3*(2*r)=6*r by omega] using half_power_normalizes (6*r)

private theorem bern_block (r : Nat) :
    bernDen (defect (2*r)) (2^(6*r)) ≈ 2 := by
  unfold bernDen
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv _ _) (block_defect r))) (by decide)

private theorem qpow_nome_block_le_half (r : Nat) (hr : logOnset ≤ r) :
    qpow (nome (2*r)) (2^(6*r)) ≤ half := by
  have hm : 6 ≤ 2*r := by unfold logOnset at hr; omega
  have hbern := oneSub_pow_mul_bernDen_le
    (Q'.le_of_lt (defect_pos (2*r)))
    (Q'.le_trans' _ _ _ (defect_le_half hm) (by decide)) (2^(6*r))
  change qpow (nome (2*r)) (2^(6*r)) *
    bernDen (defect (2*r)) (2^(6*r)) ≤ 1 at hbern
  have he : qpow (nome (2*r)) (2^(6*r)) * 2 ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (bern_block r)))) hbern
  have hh : half * 2 ≈ (1 : Q') := by decide
  have hmul : qpow (nome (2*r)) (2^(6*r)) * 2 ≤ half * 2 :=
    Q'.le_trans' _ _ _ he (Q'.ge_of_eqv hh)
  exact BakryEmery.le_of_mul_le_mul_right_pos (by decide) hmul

private theorem split_square (r : Nat) :
    logSplit r * logSplit r = 2^(6*r) * (r*r) := by
  unfold logSplit
  rw [show (r*2^(3*r))*(r*2^(3*r)) =
      (2^(3*r)*2^(3*r))*(r*r) by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]]
  rw [← Nat.pow_add]
  rw [show 3*r+3*r=6*r by omega]

/-- The complete high-spin exponent has a quadratic polynomial margin. -/
theorem logTail_guard (r : Nat) (hr : logOnset ≤ r) :
    qpow (nome (2*r)) (logSplit r * logSplit r) ≤ half^(r*r) := by
  rw [split_square]
  have hm : 6 ≤ 2*r := by unfold logOnset at hr; omega
  have hpow := qpow_base_mono
    (RGTransport.qpow_nonneg _ (Q'.le_of_lt (nome_pos hm)) (2^(6*r)))
    (qpow_nome_block_le_half r hr) (r*r)
  have he := qpow_qpow (nome (2*r)) (2^(6*r)) (r*r)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm he))
    (Q'.le_trans' _ _ _ hpow
      (Q'.le_of_eqv (qpow_eqv_pow half (r*r))))

theorem logTail_le_eighth (r : Nat) (hr : logOnset ≤ r) :
    qpow (nome (2*r)) (logSplit r * logSplit r) ≤
      Q'.mkPos 1 8 (by decide) := by
  have hmul := Nat.mul_le_mul_right r
    (show 21 ≤ r by unfold logOnset at hr; omega)
  have h3 : 3 ≤ r*r := by unfold logOnset at hr; omega
  have he : r*r = 3+(r*r-3) := by omega
  exact Q'.le_trans' _ _ _ (logTail_guard r hr)
    (Q'.le_trans' _ _ _ (by rw [he]; exact ExpNeg.pow_half_antitone 3 (r*r-3))
      (by decide))

private theorem square_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    a*a ≤ b*b :=
  Q'.mul_le_mul_of_nonneg hab hab (Q'.le_trans' _ _ _ ha hab) ha

private theorem fourth_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    (a*a)*(a*a) ≤ (b*b)*(b*b) :=
  square_mono (Q'.mul_nonneg _ _ ha ha) (square_mono ha hab)

private theorem split_defect (r : Nat) :
    Q'.ofNat (logSplit r) * defect (2*r) ≈
      Q'.ofNat r * half^(3*r) := by
  unfold logSplit defect
  have he : 3*(2*r) = 3*r+3*r := by omega
  rw [he]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (ofNat_mul_eqv r (2^(3*r))))
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (dyadic_cancel (3*r) (3*r))))

private theorem head_factor (r : Nat) (hr : logOnset ≤ r) :
    Q'.ofNat (logSplit r+2) * defect (2*r) ≤
      2*(Q'.ofNat r * half^(3*r)) := by
  have hs : 2 ≤ logSplit r := split_ge_two r hr
  have hn := CReal.ofNat_le_ofNat
    (show logSplit r+2 ≤ 2*logSplit r by omega)
  have hn' : Q'.ofNat (logSplit r+2) ≤ 2*Q'.ofNat (logSplit r) :=
    Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (ofNat_mul_eqv 2 (logSplit r)))
  have he : (2*Q'.ofNat (logSplit r))*defect (2*r) ≈
      2*(Q'.ofNat r*half^(3*r)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (split_defect r))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hn'
      (Q'.pow_nonneg half half_nonneg _))
    (Q'.le_of_eqv he)

private theorem fourth_ofNat (r : Nat) :
    (Q'.ofNat r*Q'.ofNat r)*(Q'.ofNat r*Q'.ofNat r) ≈
      Q'.ofNat (r^4) := by
  have hs : Q'.ofNat r*Q'.ofNat r ≈ Q'.ofNat (r*r) :=
    Q'.eqv_symm (ofNat_mul_eqv r r)
  have h := Q'.eqv_trans _ _ _ (mul_congr hs hs)
    (Q'.eqv_symm (ofNat_mul_eqv (r*r) (r*r)))
  have hn : (r*r)*(r*r)=r^4 := by
    simp only [Nat.pow_succ, Nat.pow_zero]
    ac_rfl
  simpa only [hn] using h

private theorem head_fourth (r : Nat) (hr : logOnset ≤ r) :
    ((Q'.ofNat (logSplit r+2)*Q'.ofNat (logSplit r+2))*
        (Q'.ofNat (logSplit r+2)*Q'.ofNat (logSplit r+2)))*
      ((defect (2*r)*defect (2*r))*(defect (2*r)*defect (2*r))) ≤
      16*(Q'.ofNat (r^4)*half^(12*r)) := by
  let n := Q'.ofNat (logSplit r+2)
  let h := defect (2*r)
  let R := Q'.ofNat r
  let z := half^(3*r)
  have hz : (z*z)*(z*z) ≈ half^(12*r) := by
    have he := Q'.eqv_trans _ _ _
      (mul_congr (half_product (3*r) (3*r)) (half_product (3*r) (3*r)))
      (half_product (3*r+3*r) (3*r+3*r))
    simpa only [show (3*r+3*r)+(3*r+3*r)=12*r by omega] using he
  have hleft : ((n*n)*(n*n))*((h*h)*(h*h)) ≈
      ((n*h)*(n*h))*((n*h)*(n*h)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
        (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => n | _ => h)
  have hright : (((2 : Q')*(R*z))*(2*(R*z)))*
        ((2*(R*z))*(2*(R*z))) ≈
      16*(Q'.ofNat (r^4)*half^(12*r)) := by
    have hp : (((2 : Q')*(R*z))*(2*(R*z)))*
        ((2*(R*z))*(2*(R*z))) ≈
        16*(((R*R)*(R*R))*((z*z)*(z*z))) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.mul (.const 2) (.mul (.var 0) (.var 1)))
          (.mul (.const 2) (.mul (.var 0) (.var 1))))
          (.mul (.mul (.const 2) (.mul (.var 0) (.var 1)))
            (.mul (.const 2) (.mul (.var 0) (.var 1)))))
        (.mul (.const 16)
          (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
            (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1)))))
        (by decide) (fun | 0 => R | _ => z)
    exact Q'.eqv_trans _ _ _ hp
      (Q'.mul_eqv_congr_left _ _ _ (mul_congr (fourth_ofNat r) hz))
  change ((n*n)*(n*n))*((h*h)*(h*h)) ≤ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _
      (fourth_mono (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _)
        (Q'.pow_nonneg half half_nonneg _)) (head_factor r hr))
      (Q'.le_of_eqv hright))

private theorem split_cube (r : Nat) :
    (logSplit r)^3 = r^3 * 2^(9*r) := by
  unfold logSplit
  rw [Nat.mul_pow, ← Nat.pow_mul]
  rw [show 3*r*3=9*r by omega]

private theorem exponent_dominates (r : Nat) (hr : logOnset ≤ r) :
    21*r ≤ r*r := by
  have h : 21 ≤ r := by unfold logOnset at hr; omega
  exact Nat.mul_le_mul_right r h

private theorem tail_budget (r : Nat) (hr : logOnset ≤ r) :
    Q'.ofNat ((logSplit r)^3) *
        qpow (nome (2*r)) (logSplit r*logSplit r) ≤
      Q'.ofNat (r^4) * half^(12*r) := by
  have hq : qpow (nome (2*r)) (logSplit r*logSplit r) ≤ half^(21*r) :=
    Q'.le_trans' _ _ _ (logTail_guard r hr)
      (half_pow_antitone (21*r) (r*r) (exponent_dominates r hr))
  have hs := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat ((logSplit r)^3)) hq (Q'.ofNat_nonneg _)
  have he : Q'.ofNat ((logSplit r)^3) * half^(21*r) ≈
      Q'.ofNat (r^3) * half^(12*r) := by
    rw [split_cube, show 21*r=9*r+12*r by omega]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (ofNat_mul_eqv (r^3) (2^(9*r))))
      (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.mul_eqv_congr_left _ _ _ (dyadic_cancel (9*r) (12*r))))
  have hnat : r^3 ≤ r^4 := by
    have h1 : 1 ≤ r := by unfold logOnset at hr; omega
    calc
      r^3 = r^3*1 := by omega
      _ ≤ r^3*r := Nat.mul_le_mul_left _ h1
      _ = r^4 := (Nat.pow_succ r 3).symm
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (CReal.ofNat_le_ofNat hnat) (Q'.pow_nonneg half half_nonneg _)))

/-- An explicit quartic rate on the narrower logarithmic dyadic split.
The rate is `888*r^4*(1-w)^2`; the fourth-moment theorem using this budget
continues to retain its original terminal source and edge density. -/
theorem logBudget_bound (r : Nat) (hr : logOnset ≤ r) :
    quarticBudget (nome (2*r)) (logSplit r) ≤
      888*(Q'.ofNat (r^4)*
        (defect (2*r)*defect (2*r))) := by
  let h := defect (2*r)
  let n := Q'.ofNat (logSplit r+2)
  let z := half^(12*r)
  let R4 := Q'.ofNat (r^4)
  have hb : relativeBudget n (1+-(nome (2*r))) ≈ relativeBudget n h := by
    unfold relativeBudget
    exact Q'.add_eqv_congr'
      (mul_congr (Q'.eqv_refl _)
        (mul_congr (mul_congr (defect_pin r) (defect_pin r))
          (mul_congr (defect_pin r) (defect_pin r))))
      (Q'.mul_eqv_congr_left _ _ _ (mul_congr (defect_pin r) (defect_pin r)))
  have hh : 32*((n*n)*(n*n))*((h*h)*(h*h)) ≤ 512*(R4*z) := by
    have hm : 32*(((n*n)*(n*n))*((h*h)*(h*h))) ≤ 32*(16*(R4*z)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ 32 (head_fourth r hr) (by decide)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _ hm
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.const 32) (.mul (.const 16) (.var 0)))
          (.mul (.const 512) (.var 0)) (by decide) (fun _ => R4*z))))
  have h1 : 1 ≤ R4 :=
    CReal.ofNat_le_ofNat (show (1 : Nat) ≤ r^4 from by
      have hp : 0 < r := by unfold logOnset at hr; omega
      have hp4 : 0 < r^4 := Nat.pow_pos hp
      exact hp4)
  have hsq : 296*(h*h) ≤ 296*(R4*z) := by
    have he : h*h ≈ z := defect_square r
    have hz : (0 : Q') ≤ z := Q'.pow_nonneg half half_nonneg _
    have hc : z ≤ R4*z := by
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ _ h1 hz
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv z))) hm
    exact Q'.mul_le_mul_of_nonneg_left _ _ 296
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hc) (by decide)
  have ht : 80*Q'.ofNat ((logSplit r)^3)*
        qpow (nome (2*r)) (logSplit r*logSplit r) ≤ 80*(R4*z) := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ 80 (tail_budget r hr) (by decide))
  have hsum : (512*(R4*z)+296*(R4*z))+80*(R4*z) ≈
      888*(R4*z) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.const 512) (.var 0))
        (.mul (.const 296) (.var 0))) (.mul (.const 80) (.var 0)))
      (.mul (.const 888) (.var 0)) (by decide) (fun _ => R4*z)
  have hright : 888*(R4*z) ≈ 888*(R4*(h*h)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (defect_square r)))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hb) (Q'.add_le_add hh hsq)) ht)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hsum hright))

#print axioms logSplit
#print axioms logNome
#print axioms logDefect
#print axioms logRate
#print axioms logOnset
#print axioms logNome_pos
#print axioms logNome_lt_one
#print axioms logSplit_ge_one
#print axioms logHalf_guard
#print axioms logTail_guard
#print axioms logTail_le_eighth
#print axioms logBudget_bound

end YMGap.Continuum.SU2HeatQuarticLogDyadicBudget
