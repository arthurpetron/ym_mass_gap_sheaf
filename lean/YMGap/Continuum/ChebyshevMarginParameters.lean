/-
# Rational reciprocal-pair parameters from an explicit squared margin

This is scalar calibration only. It does not assert a coercivity margin or
an operator contraction on the original gauge-theory carrier.
-/

import YMGap.Continuum.RationalSqrtCalibration
import YMGap.Continuum.ChebyshevReciprocalPair
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.ChebyshevMarginParameters

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem diff_pos {a b : Q'} (h : a < b) : (0 : Q') < b + -a := by
  have hh : a.num * (b.den : Int) < b.num * (a.den : Int) := h
  show (0 : Int) * ((b + -a).den : Int) < (b + -a).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  change 0 < b.num * (a.den : Int) + (-a.num) * (b.den : Int)
  rw [Int.neg_mul]
  omega

private theorem divPos_lt_one_of_lt {a b : Q'}
    (hb : (0 : Q') < b) (hab : a < b) :
    Q'.divPos a b hb < (1 : Q') := by
  have hh : a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  show (Q'.divPos a b hb).num * ((1 : Q').den : Int) <
    (1 : Q').num * ((Q'.divPos a b hb).den : Int)
  change (a * Q'.recipPos b hb).num * (1 : Int) <
    (1 : Int) * ((a * Q'.recipPos b hb).den : Int)
  rw [Int.mul_one, Int.one_mul, Q'.mul_den_cast]
  change a.num * (Q'.recipPos b hb).num <
    (a.den : Int) * ((Q'.recipPos b hb).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_den]
  rw [Int.mul_comm (a.den : Int) b.num]
  exact hh

def qbar (eta : Q') (hEta : (0 : Q') < eta) : Q' :=
  (1 : Q') + -(RationalSqrtCalibration.rho eta hEta *
    RationalSqrtCalibration.rho eta hEta)

def plus (eta : Q') (hEta : (0 : Q') < eta) : Q' :=
  (1 : Q') + RationalSqrtCalibration.rho eta hEta

def minus (eta : Q') (hEta : (0 : Q') < eta) : Q' :=
  (1 : Q') + -RationalSqrtCalibration.rho eta hEta

theorem qbar_pos (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) : (0 : Q') < qbar eta hEta :=
  diff_pos (Q'.lt_of_le_of_lt (RationalSqrtCalibration.rho_sq_upper eta hEta)
    hEta1)

theorem plus_pos (eta : Q') (hEta : (0 : Q') < eta) :
    (0 : Q') < plus eta hEta :=
  Q'.add_pos (by decide) (RationalSqrtCalibration.rho_pos eta hEta)

theorem minus_pos (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) : (0 : Q') < minus eta hEta :=
  diff_pos (RationalSqrtCalibration.rho_lt_one eta hEta hEta1)

def r (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) : Q' :=
  Q'.divPos (plus eta hEta) (minus eta hEta)
    (minus_pos eta hEta hEta1)

def s (eta : Q') (hEta : (0 : Q') < eta)
    (_hEta1 : eta < (1 : Q')) : Q' :=
  Q'.divPos (minus eta hEta) (plus eta hEta) (plus_pos eta hEta)

theorem r_pos (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) : (0 : Q') < r eta hEta hEta1 :=
  Q'.divPos_pos _ _ (minus_pos eta hEta hEta1) (plus_pos eta hEta)

theorem s_pos (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) : (0 : Q') < s eta hEta hEta1 :=
  Q'.divPos_pos _ _ (plus_pos eta hEta) (minus_pos eta hEta hEta1)

private theorem minus_lt_plus (eta : Q') (hEta : (0 : Q') < eta) :
    minus eta hEta < plus eta hEta := by
  let t := RationalSqrtCalibration.rho eta hEta
  have htn : (0 : Int) < t.num := Q'.num_pos_of_pos
    (RationalSqrtCalibration.rho_pos eta hEta)
  have htd : (0 : Int) < (t.den : Int) := by exact_mod_cast Q'.den_pos t
  have hh : -t.num < t.num := by omega
  have hs := Int.mul_lt_mul_of_pos_right hh htd
  show ((1 : Q') + -t).num * (((1 : Q') + t).den : Int) <
    ((1 : Q') + t).num * (((1 : Q') + -t).den : Int)
  simp only [Cheb.add_num, Q'.add_den_cast, Cheb.neg_num, Q'.neg_den,
    show ((1 : Q').den : Int) = 1 from rfl,
    show (1 : Q').num = (1 : Int) from rfl, Int.one_mul, Int.mul_one]
  rw [Int.add_mul, Int.add_mul]
  omega

theorem s_lt_one (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) : s eta hEta hEta1 < (1 : Q') :=
  divPos_lt_one_of_lt (plus_pos eta hEta) (minus_lt_plus eta hEta)

theorem rs (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) :
    r eta hEta hEta1 * s eta hEta hEta1 ≈ (1 : Q') := by
  let p := plus eta hEta
  let m := minus eta hEta
  let im := Q'.recipPos m (minus_pos eta hEta hEta1)
  let ip := Q'.recipPos p (plus_pos eta hEta)
  have hp : p * ip ≈ (1 : Q') := Q'.mul_recipPos_eqv p (plus_pos eta hEta)
  have hm : m * im ≈ (1 : Q') := Q'.mul_recipPos_eqv m (minus_pos eta hEta hEta1)
  change (p * im) * (m * ip) ≈ (1 : Q')
  have hreorder : (p * im) * (m * ip) ≈ (p * ip) * (m * im) := by
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1)))
      (by decide) (fun | 0 => p | 1 => im | 2 => m | _ => ip)
  exact Q'.eqv_trans _ _ _ hreorder
    (Q'.eqv_trans _ _ _ (Cheb.mul_eqv_congr _ _ _ _ hp hm) (by decide))

private theorem qbar_factor (eta : Q') (hEta : (0 : Q') < eta) :
    qbar eta hEta ≈ minus eta hEta * plus eta hEta := by
  let t := RationalSqrtCalibration.rho eta hEta
  exact poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
    (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.var 0)))
    (by decide) (fun _ => t)

private theorem half_square_sum (eta : Q') (hEta : (0 : Q') < eta) :
    HalfPow.half * (plus eta hEta * plus eta hEta +
      minus eta hEta * minus eta hEta) ≈ (2 : Q') + -qbar eta hEta := by
  let t := RationalSqrtCalibration.rho eta hEta
  have hfirst : HalfPow.half * ((1 + t) * (1 + t) +
      (1 + -t) * (1 + -t)) ≈
      (HalfPow.half * (2 : Q')) * ((1 : Q') + t * t) := by
    exact poly_identity_of_normal_eq
      (.mul (.var 1)
        (.add (.mul (.add (.const 1) (.var 0)) (.add (.const 1) (.var 0)))
          (.mul (.add (.const 1) (.neg (.var 0)))
            (.add (.const 1) (.neg (.var 0))))))
      (.mul (.mul (.var 1) (.const 2))
        (.add (.const 1) (.mul (.var 0) (.var 0))))
      (by decide) (fun | 0 => t | _ => HalfPow.half)
  have hmiddle : (HalfPow.half * (2 : Q')) * ((1 : Q') + t * t) ≈
      (1 : Q') + t * t :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide)) (Q'.one_mul_eqv _)
  have hlast : (1 : Q') + t * t ≈ (2 : Q') + -((1 : Q') + -(t * t)) := by
    exact poly_identity_of_normal_eq
      (.add (.const 1) (.mul (.var 0) (.var 0)))
      (.add (.const 2) (.neg (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))))
      (by decide) (fun _ => t)
  exact Q'.eqv_trans _ _ _ hfirst (Q'.eqv_trans _ _ _ hmiddle hlast)

private theorem center_times_qbar (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) :
    ChebyshevReciprocalPair.center (r eta hEta hEta1) (s eta hEta hEta1) *
      qbar eta hEta ≈ (2 : Q') + -qbar eta hEta := by
  let p := plus eta hEta
  let m := minus eta hEta
  let rr := r eta hEta hEta1
  let ss := s eta hEta hEta1
  have hr : rr * m ≈ p := Q'.divPos_mul_eqv p m (minus_pos eta hEta hEta1)
  have hs : ss * p ≈ m := Q'.divPos_mul_eqv m p (plus_pos eta hEta)
  have hfactor : (HalfPow.half * (rr + ss)) * (m * p) ≈
      HalfPow.half * ((rr * m) * p + (ss * p) * m) := by
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.mul (.var 3) (.var 4)))
      (.mul (.var 0) (.add (.mul (.mul (.var 1) (.var 3)) (.var 4))
        (.mul (.mul (.var 2) (.var 4)) (.var 3))))
      (by decide)
      (fun | 0 => HalfPow.half | 1 => rr | 2 => ss | 3 => m | _ => p)
  have hreplace : HalfPow.half * ((rr * m) * p + (ss * p) * m) ≈
      HalfPow.half * (p * p + m * m) :=
    Q'.mul_eqv_congr_left _ _ _
      (Cheb.add_eqv_congr _ _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hr)
        (Q'.mul_eqv_congr_right _ _ _ hs))
  unfold ChebyshevReciprocalPair.center
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (qbar_factor eta hEta))
    (Q'.eqv_trans _ _ _ hfactor
      (Q'.eqv_trans _ _ _ hreplace (half_square_sum eta hEta)))

private theorem target_times_qbar (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) :
    (Q'.divPos 2 (qbar eta hEta) (qbar_pos eta hEta hEta1) + -(1 : Q')) *
      qbar eta hEta ≈ (2 : Q') + -qbar eta hEta := by
  let q := qbar eta hEta
  let iq := Q'.recipPos q (qbar_pos eta hEta hEta1)
  have hrecip : iq * q ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv q _)
  have hfirst : ((2 : Q') * iq + -(1 : Q')) * q ≈
      (2 : Q') * (iq * q) + -q := by
    exact poly_identity_of_normal_eq
      (.mul (.add (.mul (.const 2) (.var 0)) (.neg (.const 1))) (.var 1))
      (.add (.mul (.const 2) (.mul (.var 0) (.var 1))) (.neg (.var 1)))
      (by decide) (fun | 0 => iq | _ => q)
  change ((2 : Q') * iq + -(1 : Q')) * q ≈ (2 : Q') + -q
  exact Q'.eqv_trans _ _ _ hfirst
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hrecip))
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv 2)))

/-- The calibrated reciprocal-pair center is exactly the usual affine
Chebyshev parameter for the rational margin `qbar`. -/
theorem center_eq_margin (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) :
    ChebyshevReciprocalPair.center (r eta hEta hEta1) (s eta hEta hEta1) ≈
      Q'.divPos 2 (qbar eta hEta) (qbar_pos eta hEta hEta1) + -(1 : Q') := by
  let q := qbar eta hEta
  have hc := center_times_qbar eta hEta hEta1
  have ht := target_times_qbar eta hEta hEta1
  have hright :
      (ChebyshevReciprocalPair.center (r eta hEta hEta1) (s eta hEta hEta1)) * q ≈
      (Q'.divPos 2 q (qbar_pos eta hEta hEta1) + -(1 : Q')) * q :=
    Q'.eqv_trans _ _ _ hc (Q'.eqv_symm ht)
  have hleft :
      q * ChebyshevReciprocalPair.center (r eta hEta hEta1) (s eta hEta hEta1) ≈
      q * (Q'.divPos 2 q (qbar_pos eta hEta hEta1) + -(1 : Q')) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.eqv_trans _ _ _ hright (Q'.mul_comm_eqv _ _))
  exact Q'.mul_left_cancel_of_pos (qbar_pos eta hEta hEta1) hleft

/-- The checked reciprocal-pair bound becomes geometric with this explicit
calibration. This is a rational scalar inequality, not an operator estimate. -/
theorem calibrated_recip_le (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) (n : Nat) :
    Q'.recipPos
      (Cheb.T n (ChebyshevReciprocalPair.center
        (r eta hEta hEta1) (s eta hEta hEta1)))
      (ChebyshevReciprocalPair.T_center_pos _ _
        (rs eta hEta hEta1) (r_pos eta hEta hEta1)
        (s_pos eta hEta hEta1) n) ≤
      (2 : Q') * s eta hEta hEta1 ^ n :=
  ChebyshevReciprocalPair.T_center_recip_le _ _
    (rs eta hEta hEta1) (r_pos eta hEta hEta1)
    (s_pos eta hEta hEta1) n

/-- A computable scalar normalization cutoff. Positivity of `epsilon` is
needed by its correctness theorem, not to compute the index. -/
def normalizationCutoff (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) (epsilon : Q') : Nat :=
  HKConvGen.powBaseCutoff (s eta hEta hEta1)
    (Q'.divPos epsilon 2 (by decide))

/-- Every index beyond the returned cutoff makes the positive scalar
Chebyshev normalization at most `epsilon`. No operator margin is assumed
or produced by this scalar theorem. -/
theorem normalization_small (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) (epsilon : Q') (hEpsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : normalizationCutoff eta hEta hEta1 epsilon ≤ n) :
    Q'.recipPos
      (Cheb.T n (ChebyshevReciprocalPair.center
        (r eta hEta hEta1) (s eta hEta hEta1)))
      (ChebyshevReciprocalPair.T_center_pos _ _
        (rs eta hEta hEta1) (r_pos eta hEta hEta1)
        (s_pos eta hEta hEta1) n) ≤ epsilon := by
  have hhalf : (0 : Q') < Q'.divPos epsilon 2 (by decide) :=
    Q'.divPos_pos epsilon 2 (by decide) hEpsilon
  have hcut := HKConvGen.pow_base_le_cutoff
    (s_pos eta hEta hEta1) (s_lt_one eta hEta hEta1) hhalf
  have hpow : s eta hEta hEta1 ^ n ≤ Q'.divPos epsilon 2 (by decide) :=
    Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt (s_pos eta hEta hEta1))
        (Q'.le_of_lt (s_lt_one eta hEta hEta1)) hn) hcut
  have htwo : (2 : Q') * Q'.divPos epsilon 2 (by decide) ≈ epsilon :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.divPos_mul_eqv epsilon 2 (by decide))
  exact Q'.le_trans' _ _ _ (calibrated_recip_le eta hEta hEta1 n)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q') hpow (by decide))
      (Q'.le_of_eqv htwo))

#print axioms qbar
#print axioms plus
#print axioms minus
#print axioms qbar_pos
#print axioms plus_pos
#print axioms minus_pos
#print axioms r
#print axioms s
#print axioms r_pos
#print axioms s_pos
#print axioms s_lt_one
#print axioms rs
#print axioms center_eq_margin
#print axioms calibrated_recip_le
#print axioms normalizationCutoff
#print axioms normalization_small

end YMGap.Continuum.ChebyshevMarginParameters
