/-
# The full original heat coefficients obstruct signed squared-nome domination

This is not the finite-prefix K+2 edge obstruction. For every strict nome
and nonnegative affine multiplier, an executable all-later spin threshold
makes the ORIGINAL untruncated quartic coefficient larger than the
squared-nome heat coefficient times that multiplier. A constant vacuum
error has no effect at these positive spins.

Only coefficient inequalities are proved. No completed Haar negative
quadratic witness, counterexample for the actual terminal Wilson source,
or response/scaling conclusion is assembled here. The positive-source
pointwise/Haar quartic certificate is unaffected.
-/

import YMGap.Continuum.SU2HeatQuarticFiniteRegroup
import YMGap.Continuum.ReciprocalBernoulliUpper
import YMGap.Constructive.RatNat

namespace YMGap.Continuum.SU2HeatQuarticFullCoefficientObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow qpow_nonneg c4 dimQ)
open YMGap.Continuum.BondMovingStep (coeffW coeffW_nonneg)
open YMGap.Continuum.HeatKernelRGStep (qpow_add qpow_antitone lt_of_lt_of_le)
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SU2HeatQuarticFiniteRegroup (quarticCoeff)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem qr (a b : PolyExpr) (h : RingNormaliser.normalize a = RingNormaliser.normalize b)
    (env : Nat → Q') : RingNormaliser.eval env a ≈ RingNormaliser.eval env b :=
  poly_identity_of_normal_eq a b h env

private theorem nat_mul (a b : Nat) : Q'.ofNat (a*b) ≈ Q'.ofNat a*Q'.ofNat b := by
  change ((a*b : Nat) : Int)*(1*1) = ((a : Int)*(b : Int))*1
  simp only [Int.natCast_mul,Int.mul_one]

private theorem power_positive {q : Q'} (hq : (0 : Q') < q) :
    ∀ n, (0 : Q') < qpow q n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (power_positive hq n) hq

private theorem power_congr {a b : Q'} (h : a ≈ b) : ∀ n, qpow a n ≈ qpow b n
  | 0 => Q'.eqv_refl 1
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (power_congr h n))
      (Q'.mul_eqv_congr_left _ _ _ h)

private theorem square_power (q : Q') : ∀ n, qpow (q*q) n ≈ qpow q (n+n)
  | 0 => Q'.eqv_refl 1
  | n+1 => by
      change qpow (q*q) n*(q*q) ≈ qpow q ((n+1)+(n+1))
      rw [show (n+1)+(n+1)=(n+n+1)+1 by omega]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (square_power q n))
        (qr (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.mul (.mul (.var 0) (.var 1)) (.var 1)) (by decide)
          (fun
            | 0 => qpow q (n+n)
            | _ => q))

private theorem gap_positive {q : Q'} (hq : q < (1 : Q')) : (0 : Q') < 1-q := by
  have hn : q.num < (q.den : Int) := by
    change q.num*1 < 1*(q.den : Int) at hq
    simpa only [Int.mul_one,Int.one_mul] using hq
  change 0*((1-q).den : Int) < (1-q).num*1
  change 0*(1*(q.den : Int)) < (1*(q.den : Int)+(-q.num)*1)*1
  simp only [Int.zero_mul,Int.one_mul,Int.mul_one]
  omega

private theorem gap_le_one {q : Q'} (hq : (0 : Q') ≤ q) : 1-q ≤ (1 : Q') := by
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hq))
    (Q'.le_of_eqv (by decide : (1 : Q')+ -0 ≈ 1))

private theorem bernoulli {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (n : Nat) : qpow q n*(1+Q'.ofNat n*(1-q)) ≤ (1 : Q') := by
  have h := oneSub_pow_mul_bernDen_le (Q'.le_of_lt (gap_positive hq1)) (gap_le_one hq0) n
  have hp : oneSub (1-q) ≈ q := qr
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
    (.var 0) (by decide) (fun _ => q)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
    (Q'.mul_eqv_congr_right _ _ _ (power_congr hp n))) h

private theorem scaled_gap {h : Q'} (hh : (0 : Q') < h) (a n : Nat)
    (hn : a*h.den ≤ n) : Q'.ofNat a ≤ Q'.ofNat n*h := by
  have hp : 1 ≤ h.num := by have := Q'.num_pos_of_pos hh; omega
  have hcast : (a : Int)*(h.den : Int) ≤ (n : Int) := by exact_mod_cast hn
  have hmul : (n : Int) ≤ (n : Int)*h.num := by
    have hm := Int.mul_le_mul_of_nonneg_left hp (Int.natCast_nonneg n)
    simpa only [Int.mul_one] using hm
  change (a : Int)*((Q'.ofNat n*h).den : Int) ≤ (Q'.ofNat n*h).num*1
  rw [Q'.mul_den_cast]
  change (a : Int)*(1*(h.den : Int)) ≤ ((n : Int)*h.num)*1
  simp only [Int.one_mul,Int.mul_one]
  exact Int.le_trans hcast hmul

/-- Actual Nat data. The denominator is that of the positive original nome gap. -/
def fullCoefficientCutoff (q c : Q') : Nat :=
  (48+6*c.num.toNat)*(1-q).den+2

private theorem cutoff_gaps {q c : Q'} (hq1 : q < (1 : Q')) (hc : (0 : Q') ≤ c)
    (k : Nat) (hk : (48+6*c.num.toNat)*(1-q).den ≤ k) :
    (48 : Q') ≤ 1+Q'.ofNat (2*k+3)*(1-q) ∧
      6*c ≤ Q'.ofNat (k*k+10*k+16)*(1-q) := by
  have hp := gap_positive hq1
  have h48 : 48*(1-q).den ≤ 2*k+3 := by
    have hm := Nat.mul_le_mul_right (1-q).den (show 48 ≤ 48+6*c.num.toNat by omega)
    omega
  have h6 : (6*c.num.toNat)*(1-q).den ≤ k*k+10*k+16 := by
    have hm := Nat.mul_le_mul_right (1-q).den (show 6*c.num.toNat ≤ 48+6*c.num.toNat by omega)
    have hlinear : k ≤ k*k+10*k+16 := by omega
    exact Nat.le_trans (Nat.le_trans hm hk) hlinear
  constructor
  · exact Q'.le_trans' _ _ _ (scaled_gap hp 48 _ h48)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ 1 (by decide))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  · exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 6
        (RatNat.le_ofNat_toNat c hc) (by decide))
        (Q'.le_of_eqv (Q'.eqv_symm (nat_mul 6 c.num.toNat))))
      (scaled_gap hp _ _ h6)

private theorem coefficient_shift_le {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q'))
    (k s gap factor : Nat) (he : c4 (k+s)=c4 k+gap)
    (hd : k+s+1 ≤ factor*(k+1)) (hg : 2*k+3 ≤ gap) :
    coeffW q (k+s) ≤ Q'.ofNat factor*(coeffW q k*qpow q (2*k+3)) := by
  have hp := qpow_antitone hq0 hq1 (2*k+3) gap hg
  have hdim : Q'.ofNat (k+s+1) ≤ Q'.ofNat factor*Q'.ofNat (k+1) :=
    Q'.le_trans' _ _ _ (Q'.ofNat_le_ofNat hd) (Q'.le_of_eqv (nat_mul factor (k+1)))
  have hpow := Q'.mul_le_mul_of_nonneg_left _ _ (qpow q (c4 k)) hp (qpow_nonneg q hq0 _)
  have hm := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hdim (qpow_nonneg q hq0 (c4 k+gap)))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_add q (c4 k) gap)) hpow)
      (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) (Q'.ofNat_nonneg _)))
  unfold coeffW dimQ
  rw [he]
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (qr
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (by decide)
    (fun
      | 0 => Q'.ofNat factor
      | 1 => Q'.ofNat (k+1)
      | 2 => qpow q (c4 k)
      | _ => qpow q (2*k+3))))

private theorem quartic_lower {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (k : Nat) (hden : (48 : Q') ≤ 1+Q'.ofNat (2*k+3)*(1-q)) :
    coeffW q k ≤ 2*quarticCoeff (coeffW q) (k+2) := by
  let a := coeffW q k
  let t := qpow q (2*k+3)
  have ha : (0 : Q') ≤ a := coeffW_nonneg hq0 k
  have ht := qpow_nonneg q hq0 (2*k+3)
  have h48 : 48*t ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ t hden ht)) (bernoulli hq0 hq1 (2*k+3))
  have h1 := coefficient_shift_le hq0 (Q'.le_of_lt hq1) k 1 (2*k+3) 2
    (by simp only [c4,Nat.mul_add,Nat.add_mul]; omega) (by omega) (Nat.le_refl _)
  have h3 := coefficient_shift_le hq0 (Q'.le_of_lt hq1) k 3 (6*k+15) 4
    (by simp only [c4,Nat.mul_add,Nat.add_mul]; omega) (by omega) (by omega)
  have hp : 8*(coeffW q (k+1)+coeffW q (k+3)) ≤ a := by
    have hs := Q'.mul_le_mul_of_nonneg_left _ _ 8 (Q'.add_le_add h1 h3) (by decide)
    have hb := Q'.mul_le_mul_of_nonneg_right _ _ a h48 ha
    exact Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ (Q'.le_of_eqv (qr
      (.mul (.const 8) (.add (.mul (.const 2) (.mul (.var 0) (.var 1)))
        (.mul (.const 4) (.mul (.var 0) (.var 1)))))
      (.mul (.mul (.const 48) (.var 1)) (.var 0)) (by decide)
      (fun
        | 0 => a
        | _ => t)))
      (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (Q'.one_mul_eqv a))))
  have hn := Q'.zero_le_add _ _ (Q'.sub_nonneg_of_le hp)
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 12) (coeffW_nonneg hq0 (k+2)))
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (coeffW_nonneg hq0 (k+4))))
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (qr
    (.add (.add (.var 0) (.neg (.mul (.const 8) (.add (.var 1) (.var 3)))))
      (.add (.mul (.const 12) (.var 2)) (.mul (.const 2) (.var 4))))
    (.add (.mul (.const 2) (.add (.add
      (.add (.mul (.const 6) (.var 2)) (.neg (.mul (.const 4) (.add (.var 1) (.var 3)))))
      (.var 0)) (.var 4))) (.neg (.var 0))) (by decide)
    (fun
      | 0 => a
      | 1 => coeffW q (k+1)
      | 2 => coeffW q (k+2)
      | 3 => coeffW q (k+3)
      | _ => coeffW q (k+4))))

private theorem lt_of_sub_pos {a b : Q'} (h : (0 : Q') < b-a) : a < b := by
  have hn := Q'.num_pos_of_pos h
  change a.num*(b.den : Int) < b.num*(a.den : Int)
  change 0 < b.num*(a.den : Int)+(-a.num)*(b.den : Int) at hn
  rw [Int.neg_mul] at hn
  omega

private theorem cancel_double_lt {a b : Q'} (h : 2*a < 2*b) : a < b := by
  change (2*a).num*((2*b).den : Int) < (2*b).num*((2*a).den : Int) at h
  rw [Q'.mul_den_cast,Q'.mul_den_cast] at h
  change (2*a.num)*(1*(b.den : Int)) < (2*b.num)*(1*(a.den : Int)) at h
  simp only [Int.one_mul,Int.mul_assoc] at h
  exact Int.lt_of_mul_lt_mul_left h (by decide : (0 : Int) ≤ 2)

private theorem widened_smaller {q c : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hc : (0 : Q') ≤ c) (k : Nat)
    (hgap : 6*c ≤ Q'.ofNat (k*k+10*k+16)*(1-q)) :
    2*(c*coeffW (q*q) (k+2)) < coeffW q k := by
  let a := coeffW q k
  let p := qpow q (k*k+10*k+16)
  have ha : (0 : Q') < a := Q'.mul_pos (Q'.ofNat_succ_pos k) (power_positive hq0 (c4 k))
  have hp : (0 : Q') < p := power_positive hq0 _
  have hb : p*(1+6*c) ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ p (Q'.add_le_add_left 1 _ _ hgap) (Q'.le_of_lt hp))
    (bernoulli (Q'.le_of_lt hq0) hq1 _)
  have hrem : p ≤ 1-6*c*p := by
    have h := Q'.add_le_add_right _ _ (-(6*c*p)) hb
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qr
      (.add (.mul (.var 0) (.add (.const 1) (.mul (.const 6) (.var 1))))
        (.neg (.mul (.mul (.const 6) (.var 1)) (.var 0)))) (.var 0)
      (by decide) (fun
        | 0 => p
        | _ => c))) h
  have he : c4 (k+2)+c4 (k+2)=c4 k+(k*k+10*k+16) := by
    simp only [c4,Nat.mul_add,Nat.add_mul]; omega
  have hpower : qpow (q*q) (c4 (k+2)) ≈ qpow q (c4 k)*p := by
    exact Q'.eqv_trans _ _ _ (square_power q _) (by rw [he]; exact qpow_add q _ _)
  have hdim : Q'.ofNat (k+3) ≤ 3*Q'.ofNat (k+1) :=
    Q'.le_trans' _ _ _ (Q'.ofNat_le_ofNat (by omega : k+3 ≤ 3*(k+1)))
      (Q'.le_of_eqv (nat_mul 3 (k+1)))
  have hcoeff : coeffW (q*q) (k+2) ≤ 3*(a*p) := by
    unfold coeffW dimQ
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hpower))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hdim
        (Q'.mul_nonneg _ _ (qpow_nonneg q (Q'.le_of_lt hq0) _) (Q'.le_of_lt hp)))
        (Q'.le_of_eqv (qr (.mul (.mul (.const 3) (.var 0)) (.mul (.var 1) (.var 2)))
          (.mul (.const 3) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
          (by decide) (fun
            | 0 => Q'.ofNat (k+1)
            | 1 => qpow q (c4 k)
            | _ => p))))
  have hupper : 2*(c*coeffW (q*q) (k+2)) ≤ 6*c*a*p :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv 2 c _))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (2*c) hcoeff
      (Q'.mul_nonneg _ _ (by decide) hc)) (Q'.le_of_eqv (qr
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 3) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.mul (.const 6) (.var 0)) (.var 1)) (.var 2))
      (by decide) (fun
        | 0 => c
        | 1 => a
        | _ => p))))
  have hnon := Q'.add_le_add_left a _ _ (Q'.neg_le_neg hupper)
  have hpos : (0 : Q') < a-6*c*a*p :=
    Q'.pos_of_lt_of_le (Q'.mul_pos ha (Q'.pos_of_lt_of_le hp hrem))
      (Q'.le_of_eqv (qr (.mul (.var 0) (.add (.const 1)
        (.neg (.mul (.mul (.const 6) (.var 1)) (.var 2)))))
        (.add (.var 0) (.neg (.mul (.mul (.mul (.const 6) (.var 1)) (.var 0)) (.var 2))))
        (by decide) (fun
          | 0 => a
          | 1 => c
          | _ => p)))
  exact lt_of_sub_pos (Q'.pos_of_lt_of_le hpos hnon)

/-- Every later ORIGINAL full-series quartic coefficient beats the fixed
squared-nome multiplier. No truncated coefficient or supplied cutoff is used. -/
theorem full_quartic_coefficient_gt {q c : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hc : (0 : Q') ≤ c) (j : Nat)
    (hj : fullCoefficientCutoff q c ≤ j) :
    c*coeffW (q*q) j < quarticCoeff (coeffW q) j := by
  have hj2 : 2 ≤ j := by unfold fullCoefficientCutoff at hj; omega
  let k := j-2
  have hjk : j=k+2 := by dsimp [k]; omega
  have hk : (48+6*c.num.toNat)*(1-q).den ≤ k := by
    unfold fullCoefficientCutoff at hj
    dsimp [k]
    omega
  have hg := cutoff_gaps hq1 hc k hk
  rw [hjk]
  exact cancel_double_lt (lt_of_lt_of_le (widened_smaller hq0 hq1 hc k hg.2)
    (quartic_lower (Q'.le_of_lt hq0) hq1 k hg.1))

#print axioms fullCoefficientCutoff
#print axioms full_quartic_coefficient_gt

end YMGap.Continuum.SU2HeatQuarticFullCoefficientObstruction
