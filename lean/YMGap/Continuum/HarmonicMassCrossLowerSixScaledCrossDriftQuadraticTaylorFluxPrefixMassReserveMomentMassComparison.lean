/-
Comparison of the next-scale Gaussian prefix with the old Hermite mass.

The square-root window is far inside the harmonic scale.  On that window the
exact weight drift is at most two, by a constructive reciprocal-Bernoulli
argument.  Summation then embeds the next zeroth moment into twice the old
complete Hermite weight sum.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentPayment

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassComparison

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentSummation
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem comparison_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "comparison_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               comparison_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private abbrev PE := RingNormaliser.PolyExpr

private def pTwoPSubL : PE :=
  .add (.add (.const 2) (.var 0))
    (.neg (.mul (.const 2) (.var 0)))

private def pTwoPSubR : PE :=
  .add (.const 2) (.neg (.var 0))

private theorem pTwoPSub_normal :
    RingNormaliser.normalize pTwoPSubL =
      RingNormaliser.normalize pTwoPSubR := by decide

private theorem twoP_sub_algebra (P : Q') :
    (Q'.ofNat 2 + P) + -(Q'.ofNat 2 * P) ≈
      Q'.ofNat 2 + -P := by
  simpa [pTwoPSubL, pTwoPSubR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTwoPSubL pTwoPSubR pTwoPSub_normal (fun _ => P))

private theorem squared_drift_base_eqv_one_add_excess (k : Nat) :
    driftRatio k * driftRatio k ≈
      (1 : Q') + lowerSixDriftExcess k := by
  let u := unit (driftDen k) (driftDen_pos k)
  have hr := HarmonicWeightedAbelReserve.driftRatio_eqv_one_add_unitDen k
  refine Q'.eqv_trans _ (((1 : Q') + u) * ((1 : Q') + u)) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hr)
      (Q'.mul_eqv_congr_left _ _ _ hr)
  · unfold lowerSixDriftExcess
    dsimp only [u]
    comparison_ring

private theorem six_mode_square_le_scale_square
    {k j : Nat} (hk : 8189 ≤ k) (hj : j < thetaWindowRight k) :
    6 * ((j + 1) * (j + 1)) ≤ (k + 2) * (k + 2) := by
  let n := j + 1
  let R := thetaWindowRight k
  let D := k + 2
  have hmax := eight_odd_thetaWindowRight_le_harmonicDen hk
  have hnR : n ≤ R := by
    dsimp only [n, R]
    omega
  have h16n : 16 * n ≤ D := by
    dsimp only [R, D] at hmax hnR ⊢
    omega
  have h6n : 6 * n ≤ D := by omega
  have hnD : n ≤ D := by omega
  have hmul := Nat.mul_le_mul h6n hnD
  simpa only [n, D, Nat.mul_assoc] using hmul

private theorem two_mode_driftExcess_le_one
    {k j : Nat} (hk : 8189 ≤ k) (hj : j < thetaWindowRight k) :
    Q'.ofNat 2 *
        (Q'.ofNat ((j + 1) * (j + 1)) * lowerSixDriftExcess k) ≤
      (1 : Q') := by
  let m := (j + 1) * (j + 1)
  let e := lowerSixDriftExcess k
  let D2 := (k + 2) * (k + 2)
  have hnat : 6 * m ≤ D2 := by
    dsimp only [m, D2]
    exact six_mode_square_le_scale_square hk hj
  have hcast : Q'.ofNat (6 * m) ≤ Q'.ofNat D2 :=
    CReal.ofNat_le_ofNat hnat
  have he0 : (0 : Q') ≤ e := by
    dsimp only [e]
    exact lowerSixDriftExcess_nonnegative k
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ e hcast he0
  have hscale := lowerSixDriftExcess_scaled_le_three
    (show 1 ≤ k by omega)
  change Q'.ofNat D2 * e ≤ Q'.ofNat 3 at hscale
  have hchain : Q'.ofNat (6 * m) * e ≤ Q'.ofNat 3 :=
    Q'.le_trans' _ _ _ hmul hscale
  have hcast6 : Q'.ofNat (6 * m) ≈ Q'.ofNat 6 * Q'.ofNat m :=
    HeatKernelRGStep.ofNat_mul_eqv 6 m
  have hleft :
      Q'.ofNat 3 * (Q'.ofNat 2 * (Q'.ofNat m * e)) ≈
        Q'.ofNat (6 * m) * e := by
    refine Q'.eqv_trans _ ((Q'.ofNat 6 * Q'.ofNat m) * e) _ ?_ ?_
    · comparison_ring
    · exact Q'.mul_eqv_congr_right _ _ e (Q'.eqv_symm hcast6)
  have hright : Q'.ofNat 3 ≈ Q'.ofNat 3 * (1 : Q') :=
    Q'.eqv_symm (Q'.mul_one_eqv (Q'.ofNat 3))
  have hcancel :
      Q'.ofNat 3 * (Q'.ofNat 2 * (Q'.ofNat m * e)) ≤
        Q'.ofNat 3 * (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv hright))
  have hsmall := Q'.le_of_mul_le_mul_left hcancel
    (by decide : (0 : Q') < Q'.ofNat 3)
  dsimp only [m, e] at hsmall ⊢
  exact hsmall

private theorem qpow_one_add_le_two
    {e : Q'} (he0 : (0 : Q') ≤ e) (m : Nat)
    (hsmall : Q'.ofNat 2 * (Q'.ofNat m * e) ≤ (1 : Q')) :
    qpow ((1 : Q') + e) m ≤ Q'.ofNat 2 := by
  let P := qpow ((1 : Q') + e) m
  let x := Q'.ofNat m * e
  have hP0 : (0 : Q') ≤ P := by
    dsimp only [P]
    exact qpow_nonneg _ (Q'.zero_le_add _ _ (by decide) he0) _
  have hgrowth := HarmonicWeightedAbelReserve.qpow_one_add_growth
    he0 (Q'.eqv_refl ((1 : Q') + e)) m
  change P ≤ (1 : Q') + x * P at hgrowth
  have hXP := Q'.mul_le_mul_of_nonneg_right _ _ P hsmall hP0
  have hXP' : (Q'.ofNat 2 * x) * P ≤ P :=
    Q'.le_trans' _ _ _ hXP (Q'.le_of_eqv (Q'.one_mul_eqv P))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hgrowth (by decide)
  have hbound : Q'.ofNat 2 * ((1 : Q') + x * P) ≤
      Q'.ofNat 2 + P := by
    have hadd := Q'.add_le_add_left (Q'.ofNat 2) _ _ hXP'
    have hL : Q'.ofNat 2 * ((1 : Q') + x * P) ≈
        Q'.ofNat 2 + (Q'.ofNat 2 * x) * P := by comparison_ring
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) hadd
  have htwoP : Q'.ofNat 2 * P ≤ Q'.ofNat 2 + P :=
    Q'.le_trans' _ _ _ hscaled hbound
  have hdiff := Q'.sub_nonneg_of_le htwoP
  have hrearrange :
      (Q'.ofNat 2 + P) + -(Q'.ofNat 2 * P) ≈
        Q'.ofNat 2 + -P := twoP_sub_algebra P
  have hnonneg : (0 : Q') ≤ Q'.ofNat 2 + -P :=
    Q'.le_trans' _ _ _ hdiff (Q'.le_of_eqv hrearrange)
  dsimp only [P] at hnonneg ⊢
  exact Q'.le_of_sub_nonneg hnonneg

/-- On the complete large-scale square-root prefix, one scale step enlarges
each squared heat-kernel weight by at most two. -/
theorem lowerSixModeWeight_next_le_two_old_large
    {k j : Nat} (hk : 8189 ≤ k) (hj : j < thetaWindowRight k) :
    lowerSixModeWeight (k + 1) (j + 1) ≤
      Q'.ofNat 2 * lowerSixModeWeight k (j + 1) := by
  let n := j + 1
  let m := n * n
  let e := lowerSixDriftExcess k
  let F := lowerSixWeightDriftFactor k n
  let W := lowerSixModeWeight k n
  have he0 : (0 : Q') ≤ e := by
    dsimp only [e]
    exact lowerSixDriftExcess_nonnegative k
  have hb := squared_drift_base_eqv_one_add_excess k
  have hFpow : F ≈ qpow ((1 : Q') + e) m := by
    dsimp only [F, lowerSixWeightDriftFactor, e, m, n]
    exact qpow_eqv_congr_base hb ((j + 1) * (j + 1))
  have hsmall := two_mode_driftExcess_le_one hk hj
  change Q'.ofNat 2 * (Q'.ofNat m * e) ≤ (1 : Q') at hsmall
  have hpow := qpow_one_add_le_two he0 m hsmall
  have hF : F ≤ Q'.ofNat 2 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hFpow) hpow
  have hW0 : (0 : Q') ≤ W := by
    dsimp only [W, n]
    exact lowerSixModeWeight_nonnegative k (j + 1)
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ W hF hW0
  have hstep := lowerSixModeWeight_step_eqv k n
  have hright : W * Q'.ofNat 2 ≈ Q'.ofNat 2 * W :=
    Q'.mul_comm_eqv W (Q'.ofNat 2)
  dsimp only [n, W, F] at hstep hmul hright ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hstep)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hright))

private theorem thetaWindowRight_le_growingAnchor_large
    {k : Nat} (hk : 8189 ≤ k) :
    thetaWindowRight k ≤ growingAnchor k := by
  let c := thetaWindowCenter k
  have hc : 9 ≤ c := thetaWindowCenter_ge_nine (show 38 ≤ k by omega)
  have hsq : c * c ≤ thetaWindowLength k := by
    dsimp only [c, thetaWindowCenter]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hright : thetaWindowRight k + 1 ≤ 2 * c + 1 := by
    unfold thetaWindowRight
    dsimp only [c]
    have hdiv := Nat.div_le_self (thetaWindowCenter k) 4
    omega
  have hroom : 2 * c + 1 ≤ c * c := by
    have hmul := Nat.mul_le_mul_right c (show 3 ≤ c by omega)
    have h3c : 3 * c ≤ c * c := by
      simpa [Nat.mul_comm] using hmul
    have hlinear : 2 * c + 1 ≤ 3 * c := by omega
    exact Nat.le_trans hlinear h3c
  rw [thetaWindowLength_eq_anchor] at hsq
  omega

/-- The large-scale next zeroth Gaussian moment is at most twice the old
complete Hermite weight sum. -/
theorem lowerSixNextGaussianMoment_zero_le_two_oldWeightSum_large
    {k : Nat} (hk : 8189 ≤ k) :
    lowerSixNextGaussianMoment k 0 (thetaWindowRight k) ≤
      Q'.ofNat 2 * lowerSixHermiteWeightSum k := by
  let R := thetaWindowRight k
  let f : Nat → Q' := fun j =>
    lowerSixQPower (j + 1) 0 * lowerSixModeWeight (k + 1) (j + 1)
  let g : Nat → Q' := fun j =>
    Q'.ofNat 2 * lowerSixModeWeight k (j + 1)
  have hterm : ∀ j, j < R → f j ≤ g j := by
    intro j hj
    have hweight := lowerSixModeWeight_next_le_two_old_large hk hj
    have hone : lowerSixQPower (j + 1) 0 *
        lowerSixModeWeight (k + 1) (j + 1) ≈
          lowerSixModeWeight (k + 1) (j + 1) := by
      unfold lowerSixQPower RingNormaliser.qpow
      exact Q'.one_mul_eqv _
    dsimp only [f, g]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hone) hweight
  have hsum : finSum f R ≤ finSum g R :=
    finSum_le_lt f g R hterm
  have hleft : lowerSixNextGaussianMoment k 0 R = finSum f R := rfl
  have hright : finSum g R ≈
      Q'.ofNat 2 * finSum
        (fun j => lowerSixModeWeight k (j + 1)) R := by
    dsimp only [g]
    exact Q'.eqv_symm (const_mul_finSum _ _ _)
  have hprefix : finSum (fun j => lowerSixModeWeight k (j + 1)) R ≤
      lowerSixHermiteWeightSum k := by
    unfold lowerSixHermiteWeightSum
    apply finSum_monotone_of_nonneg
    · intro j
      exact lowerSixModeWeight_nonnegative k (j + 1)
    · dsimp only [R]
      exact thetaWindowRight_le_growingAnchor_large hk
  have htwo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hprefix (by decide)
  rw [hleft]
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright) htwo)

#print axioms lowerSixModeWeight_next_le_two_old_large
#print axioms lowerSixNextGaussianMoment_zero_le_two_oldWeightSum_large

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassComparison
