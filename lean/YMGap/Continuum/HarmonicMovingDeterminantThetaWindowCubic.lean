/-
Three-factor Bernoulli carrier for the cumulative theta-window proof.

The first-order carrier is too weak.  Splitting the odd power as
`2n+1 = n+n+1` retains the constructive cubic correction
`w^(2n+1) >= (1-n(1-w))^2 w` and gives a sharper upper bound on the positive
root slope without any analytic approximation.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCumulative

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCumulative
open YMGap.Continuum.MovingCutoff
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem cubic_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "cubic_ring" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Q'.neg_den, cubic_neg_num_cast,
               Int.natCast_mul,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

def thetaLinearBernoulliFactor (w : Q') (n : Nat) : Q' :=
  (1 : Q') + -(Q'.ofNat n * ((1 : Q') + -w))

def thetaThreeFactorLower (w : Q') (n : Nat) : Q' :=
  (thetaLinearBernoulliFactor w n * thetaLinearBernoulliFactor w n) * w

private theorem qpow_two_n_one_factor (w : Q') (n : Nat) :
    qpow w (2 * n + 1) ≈ (qpow w n * qpow w n) * w := by
  have hnn := HeatKernelRGStep.qpow_add w n n
  have hlast := HeatKernelRGStep.qpow_add w (n + n) 1
  have hdouble : n + n = 2 * n := by omega
  rw [hdouble] at hnn
  rw [hdouble] at hlast
  have hone : qpow w 1 ≈ w := by
    change (1 : Q') * w ≈ w
    exact Q'.one_mul_eqv w
  refine Q'.eqv_trans _ _ _ hlast ?_
  refine Q'.eqv_trans _
    (qpow w (2 * n) * w) _
    (Q'.mul_eqv_congr_left _ _ _ hone) ?_
  exact Q'.mul_eqv_congr_right _ _ _ hnn

/-- Cubic-strength constructive lower Bernoulli bound obtained from two
copies of the linear bound and the exact final factor `w`. -/
theorem qpow_odd_ge_threeFactor {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (n : Nat)
    (hlin0 : (0 : Q') ≤ thetaLinearBernoulliFactor w n) :
    thetaThreeFactorLower w n ≤ qpow w (2 * n + 1) := by
  have hbern : thetaLinearBernoulliFactor w n ≤ qpow w n := by
    unfold thetaLinearBernoulliFactor
    exact MovingCutoff.qpow_ge_bernoulli hw0 hw1 n
  have hsq :
      thetaLinearBernoulliFactor w n * thetaLinearBernoulliFactor w n ≤
        qpow w n * qpow w n :=
    Q'.mul_le_mul_of_nonneg hbern hbern (qpow_nonneg w hw0 n) hlin0
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ w hsq hw0
  unfold thetaThreeFactorLower
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (Q'.eqv_symm (qpow_two_n_one_factor w n)))

/-- Cubic Bernoulli upper carrier for the positive root-slope branch. -/
def thetaCubicRightCarrier (k n : Nat) : Q' :=
  Q'.ofNat n +
    -(Q'.ofNat (n + 1) * thetaThreeFactorLower (harmW k) n)

theorem thetaRootSlope_le_cubicCarrier {k n : Nat}
    (hlin0 : (0 : Q') ≤ thetaLinearBernoulliFactor (harmW k) n) :
    thetaRootSlope k n ≤ thetaCubicRightCarrier k n := by
  have hp := qpow_odd_ge_threeFactor
    (harmW_nonneg k) (harmW_le_one k) n hlin0
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (n + 1)) hp
    (HeatKernelRGStep.zero_le_ofNat _)
  have hn := Q'.neg_le_neg hm
  unfold thetaRootSlope thetaCubicRightCarrier
  exact Q'.add_le_add_left (Q'.ofNat n) _ _ hn

theorem thetaWindowCenter_le_harmonicDen {k : Nat} (hk : 38 ≤ k) :
    thetaWindowCenter k ≤ k + 2 := by
  let c := thetaWindowCenter k
  have hc9 : 9 ≤ c := thetaWindowCenter_ge_nine hk
  have hsq : c * c ≤ 2 * (k + 2) + 1 := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have h2c : 2 * c ≤ c * c := by
    have h := Nat.mul_le_mul_right c (show 2 ≤ c by omega)
    simpa [Nat.mul_comm] using h
  omega

theorem thetaLinearBernoulliFactor_nonnegative_on_window {k n : Nat}
    (hk : 38 ≤ k) (hn : n ≤ thetaWindowCenter k) :
    (0 : Q') ≤ thetaLinearBernoulliFactor (harmW k) n := by
  have hnm : n ≤ k + 2 := Nat.le_trans hn
    (thetaWindowCenter_le_harmonicDen hk)
  have hunit : Q'.ofNat n * harmU k ≤ (1 : Q') := by
    unfold harmU unit
    show (Q'.ofNat n * Q'.mkPos 1 (k + 2) (by omega)).num *
        ((1 : Q').den : Int) ≤
      (1 : Q').num *
        ((Q'.ofNat n * Q'.mkPos 1 (k + 2) (by omega)).den : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
      Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
      Int.one_mul]
    have h1n : (1 : Q').num = 1 := rfl
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    rw [h1n, h1d, Int.mul_one, Int.one_mul]
    exact_mod_cast hnm
  have hcomp : (1 : Q') + -harmW k ≈ harmU k := by
    unfold harmW ReciprocalBernoulliUpper.oneSub
    cubic_ring <;> omega
  have hmulComp :
      Q'.ofNat n * ((1 : Q') + -harmW k) ≈
        Q'.ofNat n * harmU k :=
    Q'.mul_eqv_congr_left _ _ _ hcomp
  have hle : Q'.ofNat n * ((1 : Q') + -harmW k) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hmulComp) hunit
  unfold thetaLinearBernoulliFactor
  exact Q'.sub_nonneg_of_le hle

theorem thetaRootSlope_le_cubicCarrier_on_window {k n : Nat}
    (hk : 38 ≤ k) (hn : n ≤ thetaWindowCenter k) :
    thetaRootSlope k n ≤ thetaCubicRightCarrier k n :=
  thetaRootSlope_le_cubicCarrier
    (thetaLinearBernoulliFactor_nonnegative_on_window hk hn)

/-- Exact threshold audit: the cubic cumulative lower carriers retain enough
reserve through the negative endpoint, unlike the first-order carrier. -/
theorem thetaCubicCarrier_prefix_k38 :
    (0 : Q') ≤
      finSum (fun j =>
        sevenDirichletProfile 38 *
            Q'.ofNat ((thetaWindowLeft 38 + j) * (thetaWindowLeft 38 + j)) +
          -(Q'.ofNat 4 *
            (thetaCubicRightCarrier 38 (thetaWindowLeft 38 + j) *
              thetaCubicRightCarrier 38 (thetaWindowLeft 38 + j)))) 6 := by
  unfold thetaCubicRightCarrier thetaThreeFactorLower
    thetaLinearBernoulliFactor sevenDirichletProfile thetaWindowLeft
    thetaWindowCenter thetaWindowLength harmW harmU
    ReciprocalBernoulliUpper.oneSub unit
    ChebOrthoMidpointEst.isqrt ChebOrthoMidpointEst.isqrtAux finSum qpow
  decide

#print axioms thetaLinearBernoulliFactor
#print axioms thetaThreeFactorLower
#print axioms qpow_odd_ge_threeFactor
#print axioms thetaCubicRightCarrier
#print axioms thetaRootSlope_le_cubicCarrier
#print axioms thetaWindowCenter_le_harmonicDen
#print axioms thetaLinearBernoulliFactor_nonnegative_on_window
#print axioms thetaRootSlope_le_cubicCarrier_on_window
#print axioms thetaCubicCarrier_prefix_k38

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
