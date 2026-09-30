/-
# Explicit square-root calibrated decay of Chebyshev reciprocals

For x>1 put eta=(x-1)/(x+1), choose the existing rational Heron
calibration eta/4 <= t^2 <= eta, and set s=(1-t)/(1+t).
The reciprocal-pair center lies between 1 and x, so monotonicity transfers
the exact reciprocal-pair estimate to the original denominator T_n(x).
All parameters and the convergence modulus are data. No operator estimate
or scaling-uniform margin is assumed or produced by this scalar result.
-/

import YMGap.Continuum.ChebyshevAboveOneMonotone
import YMGap.Continuum.ChebyshevMarginParameters

namespace YMGap.Continuum.ChebyshevSqrtRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem diff_pos {a b : Q'} (h : a < b) : (0 : Q') < b + -a := by
  have hh : a.num * (b.den : Int) < b.num * (a.den : Int) := h
  show (0 : Int) * ((b + -a).den : Int) < (b + -a).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  change 0 < b.num * (a.den : Int) + (-a.num) * (b.den : Int)
  rw [Int.neg_mul]
  omega

private theorem plus_pos (x : Q') (hx : (1 : Q') < x) :
    (0 : Q') < x + 1 :=
  Q'.add_pos (Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) (Q'.le_of_lt hx))
    (by decide)

/-- Squared-margin parameter of the original argument, not a free margin. -/
def eta (x : Q') (hx : (1 : Q') < x) : Q' :=
  Q'.divPos (x + -(1 : Q')) (x + 1) (plus_pos x hx)

theorem eta_pos (x : Q') (hx : (1 : Q') < x) : (0 : Q') < eta x hx :=
  Q'.divPos_pos _ _ (plus_pos x hx) (diff_pos hx)

theorem eta_lt_one (x : Q') (hx : (1 : Q') < x) : eta x hx < (1 : Q') := by
  have hd : (0 : Int) < (x.den : Int) := by exact_mod_cast x.den_pos
  show (eta x hx).num * (1 : Int) < (1 : Int) * ((eta x hx).den : Int)
  unfold eta Q'.divPos
  rw [Int.mul_one, Int.one_mul, Q'.mul_den_cast]
  change (x + -(1 : Q')).num * (Q'.recipPos (x + 1) (plus_pos x hx)).num <
    ((x + -(1 : Q')).den : Int) *
      ((Q'.recipPos (x + 1) (plus_pos x hx)).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_den]
  simp only [Cheb.add_num, Cheb.neg_num, Q'.add_den_cast, Q'.neg_den,
    show ((1 : Q').den : Int) = 1 from rfl,
    show (1 : Q').num = (1 : Int) from rfl, Int.one_mul, Int.mul_one,
    Int.neg_one_mul]
  have h : x.num + - (x.den : Int) < x.num + (x.den : Int) := by omega
  simpa only [Int.mul_comm] using Int.mul_lt_mul_of_pos_right h hd

private def calibratedCenter (x : Q') (hx : (1 : Q') < x) : Q' :=
  ChebyshevReciprocalPair.center
    (ChebyshevMarginParameters.r (eta x hx) (eta_pos x hx) (eta_lt_one x hx))
    (ChebyshevMarginParameters.s (eta x hx) (eta_pos x hx) (eta_lt_one x hx))

private theorem center_bounds (x : Q') (hx : (1 : Q') < x) :
    (1 : Q') ≤ calibratedCenter x hx ∧ calibratedCenter x hx ≤ x := by
  let e := eta x hx
  let t := RationalSqrtCalibration.rho e (eta_pos x hx)
  let b := ChebyshevMarginParameters.qbar e (eta_pos x hx)
  have hb : (0 : Q') < b := ChebyshevMarginParameters.qbar_pos e
    (eta_pos x hx) (eta_lt_one x hx)
  have hsq : (0 : Q') ≤ t * t := Q'.mul_nonneg _ _
    (Q'.le_of_lt (RationalSqrtCalibration.rho_pos e (eta_pos x hx)))
    (Q'.le_of_lt (RationalSqrtCalibration.rho_pos e (eta_pos x hx)))
  have hb1 : b ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hsq))
    (by decide : (1 : Q') + -(0 : Q') ≤ 1)
  have hlow : (2 : Q') ≤ Q'.divPos 2 b hb :=
    Q'.le_divPos_of_mul_le _ _ _ (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 2 hb1 (by decide))
      (Q'.le_of_eqv (Q'.mul_one_eqv 2)))
  have heb : (1 : Q') + -e ≤ b :=
    Q'.add_le_add_left 1 _ _
      (Q'.neg_le_neg (RationalSqrtCalibration.rho_sq_upper e (eta_pos x hx)))
  have heq : (x + 1) * ((1 : Q') + -e) ≈ (2 : Q') := by
    have hring : (x + 1) * ((1 : Q') + -e) ≈
        (x + 1) + -(e * (x + 1)) := by
      exact poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.const 1)) (.add (.const 1) (.neg (.var 1))))
        (.add (.add (.var 0) (.const 1))
          (.neg (.mul (.var 1) (.add (.var 0) (.const 1)))))
        (by decide) (fun | 0 => x | _ => e)
    have heprod : e * (x + 1) ≈ x + -(1 : Q') :=
      Q'.divPos_mul_eqv _ _ (plus_pos x hx)
    have hlast : (x + 1) + -(x + -(1 : Q')) ≈ (2 : Q') := by
      exact poly_identity_of_normal_eq
        (.add (.add (.var 0) (.const 1))
          (.neg (.add (.var 0) (.neg (.const 1)))))
        (.const 2) (by decide) (fun _ => x)
    exact Q'.eqv_trans _ _ _ hring (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ heprod)) hlast)
  have hhigh : Q'.divPos 2 b hb ≤ x + 1 :=
    Q'.divPos_le_of_le_mul _ _ _ (Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ heb (Q'.le_of_lt (plus_pos x hx))))
  have hc : calibratedCenter x hx ≈ Q'.divPos 2 b hb + -(1 : Q') :=
    ChebyshevMarginParameters.center_eq_margin e (eta_pos x hx) (eta_lt_one x hx)
  constructor
  · exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ (2 : Q') + -(1 : Q'))
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-(1 : Q')) hlow)
        (Q'.ge_of_eqv hc))
  · have hend : (x + 1) + -(1 : Q') ≈ x := by
      exact poly_identity_of_normal_eq
        (.add (.add (.var 0) (.const 1)) (.neg (.const 1)))
        (.var 0) (by decide) (fun _ => x)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hc)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-(1 : Q')) hhigh)
        (Q'.le_of_eqv hend))

/-- Computable rational decay base using the square root of the actual margin. -/
def rate (x : Q') (hx : (1 : Q') < x) : Q' :=
  ChebyshevMarginParameters.s (eta x hx) (eta_pos x hx) (eta_lt_one x hx)

theorem rate_pos (x : Q') (hx : (1 : Q') < x) : (0 : Q') < rate x hx :=
  ChebyshevMarginParameters.s_pos _ _ _

theorem rate_lt_one (x : Q') (hx : (1 : Q') < x) : rate x hx < (1 : Q') :=
  ChebyshevMarginParameters.s_lt_one _ _ _

/-- Quantitative square-root gain: the squared decay deficit controls one
quarter of the actual squared-margin parameter. No numerical root oracle. -/
theorem rate_deficit_sq_lower (x : Q') (hx : (1 : Q') < x) :
    Q'.divPos (eta x hx) 4 (by decide) ≤
      ((1 : Q') + -rate x hx) * ((1 : Q') + -rate x hx) := by
  let e := eta x hx
  let t := RationalSqrtCalibration.rho e (eta_pos x hx)
  let p := ChebyshevMarginParameters.plus e (eta_pos x hx)
  let m := ChebyshevMarginParameters.minus e (eta_pos x hx)
  have ht : (0 : Q') ≤ t :=
    Q'.le_of_lt (RationalSqrtCalibration.rho_pos e (eta_pos x hx))
  have hm : (0 : Q') ≤ m := Q'.le_of_lt
    (ChebyshevMarginParameters.minus_pos e (eta_pos x hx) (eta_lt_one x hx))
  have hp : (1 : Q') ≤ p := Q'.add_le_self_of_nonneg 1 t ht
  have hs : rate x hx ≤ m := Q'.divPos_le_of_le_mul _ _ _
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv m))
      (Q'.mul_le_mul_of_nonneg_left _ _ m hp hm))
  have hring : (1 : Q') + -m ≈ t := by
    exact poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) (fun _ => t)
  have hgap : t ≤ (1 : Q') + -rate x hx := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hring) (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hs))
  have hgap0 : (0 : Q') ≤ (1 : Q') + -rate x hx := Q'.le_trans' _ _ _ ht hgap
  exact Q'.le_trans' _ _ _ (RationalSqrtCalibration.rho_sq_lower e (eta_pos x hx))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ t hgap ht)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hgap hgap0))

private theorem recip_antitone (p q : Q') (hp : (0 : Q') < p)
    (hq : (0 : Q') < q) (h : p ≤ q) :
    Q'.recipPos q hq ≤ Q'.recipPos p hp := by
  show (Q'.recipPos q hq).num * ((Q'.recipPos p hp).den : Int) ≤
    (Q'.recipPos p hp).num * ((Q'.recipPos q hq).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_num, Q'.recipPos_den, Q'.recipPos_den]
  have hh : p.num * (q.den : Int) ≤ q.num * (p.den : Int) := h
  simpa only [Int.mul_comm] using hh

private theorem reciprocal_le_calibrated (x : Q') (hx : (1 : Q') < x) (n : Nat) :
    Q'.recipPos (Cheb.T n x) (ChebyshevAboveOne.T_positive x (Q'.le_of_lt hx) n) ≤
      Q'.recipPos (Cheb.T n (calibratedCenter x hx))
        (ChebyshevAboveOne.T_positive _ (center_bounds x hx).1 n) :=
  recip_antitone _ _ _ _ (ChebyshevAboveOneMonotone.T_mono _ _
    (center_bounds x hx).1 (center_bounds x hx).2 n)

/-- The original Chebyshev reciprocal retains the square-root calibrated rate. -/
theorem reciprocal_T_le (x : Q') (hx : (1 : Q') < x) (n : Nat) :
    Q'.recipPos (Cheb.T n x) (ChebyshevAboveOne.T_positive x (Q'.le_of_lt hx) n) ≤
      (2 : Q') * rate x hx ^ n :=
  Q'.le_trans' _ _ _ (reciprocal_le_calibrated x hx n)
    (ChebyshevMarginParameters.calibrated_recip_le
      (eta x hx) (eta_pos x hx) (eta_lt_one x hx) n)

/-- Explicit degree modulus for the original denominator. -/
def degreeModulus (x : Q') (hx : (1 : Q') < x) (epsilon : Q') : Nat :=
  ChebyshevMarginParameters.normalizationCutoff
    (eta x hx) (eta_pos x hx) (eta_lt_one x hx) epsilon

theorem normalization_small (x : Q') (hx : (1 : Q') < x)
    (epsilon : Q') (hEpsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : degreeModulus x hx epsilon ≤ n) :
    Q'.recipPos (Cheb.T n x) (ChebyshevAboveOne.T_positive x (Q'.le_of_lt hx) n) ≤
      epsilon :=
  Q'.le_trans' _ _ _ (reciprocal_le_calibrated x hx n)
    (ChebyshevMarginParameters.normalization_small
      (eta x hx) (eta_pos x hx) (eta_lt_one x hx) epsilon hEpsilon n hn)

#print axioms eta
#print axioms eta_pos
#print axioms eta_lt_one
#print axioms rate
#print axioms rate_pos
#print axioms rate_lt_one
#print axioms rate_deficit_sq_lower
#print axioms reciprocal_T_le
#print axioms degreeModulus
#print axioms normalization_small

end YMGap.Continuum.ChebyshevSqrtRate
