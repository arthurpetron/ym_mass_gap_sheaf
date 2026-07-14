/-
Cubic envelope for the exact-minus-quadratic drift factor.

The first-order suffix-Abel fence shows that the third-and-higher binomial
growth cannot be discarded.  This file derives the corresponding exact
constructive upper bound: the quadratic Taylor remainder is bounded by the
third Pascal coefficient, the cube of the drift excess, and the exact power.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixAbelFence

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem cubic_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "cubic_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               cubic_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

def cubicCoeff : Nat → Nat
  | 0 => 0
  | m + 1 => cubicCoeff m + lowerSixQuadraticCoeff m

def taylor2 (u : Q') (m : Nat) : Q' :=
  ((1 : Q') + Q'.ofNat m * u) +
    Q'.ofNat (lowerSixQuadraticCoeff m) * (u * u)

private theorem taylor2_step (u : Q') (m : Nat) :
    taylor2 u m * ((1 : Q') + u) ≈
      taylor2 u (m + 1) +
        Q'.ofNat (lowerSixQuadraticCoeff m) * (u * (u * u)) := by
  have hm : Q'.ofNat (m + 1) ≈ Q'.ofNat m + (1 : Q') := by
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv m 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hc : Q'.ofNat (lowerSixQuadraticCoeff (m + 1)) ≈
      Q'.ofNat (lowerSixQuadraticCoeff m) + Q'.ofNat m := by
    rw [lowerSixQuadraticCoeff]
    exact Q'.ofNat_add_eqv _ _
  unfold taylor2
  refine Q'.eqv_trans _
    ((((1 : Q') + (Q'.ofNat m + 1) * u) +
      (Q'.ofNat (lowerSixQuadraticCoeff m) + Q'.ofNat m) * (u * u)) +
        Q'.ofNat (lowerSixQuadraticCoeff m) * (u * (u * u))) _ ?_ ?_
  · ring_qeqv
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left (1 : Q') _ _
          (Q'.mul_eqv_congr_right _ _ u (Q'.eqv_symm hm)))
        (Q'.mul_eqv_congr_right _ _ (u * u) (Q'.eqv_symm hc)))

private theorem remainder_step (u : Q') (m : Nat) :
    qpow ((1 : Q') + u) (m + 1) + -taylor2 u (m + 1) ≈
      (qpow ((1 : Q') + u) m + -taylor2 u m) * ((1 : Q') + u) +
        Q'.ofNat (lowerSixQuadraticCoeff m) * (u * (u * u)) := by
  have ht := taylor2_step u m
  let T := taylor2 u m
  let T1 := taylor2 u (m + 1)
  let B := Q'.ofNat (lowerSixQuadraticCoeff m) * (u * (u * u))
  have ht1 : T1 ≈ T * ((1 : Q') + u) + -B := by
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ ((T1 + B) + -B) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _ ht
    · refine Q'.eqv_trans _ (T1 + (B + -B)) _
        (Q'.add_assoc_eqv T1 B (-B)) ?_
      refine Q'.eqv_trans _ (T1 + 0) _
        (Q'.add_eqv_congr_left T1 _ _ (Q'.add_neg_self_eqv B)) ?_
      exact QPoly.q_add_zero_eqv T1
  change qpow ((1 : Q') + u) m * ((1 : Q') + u) + -T1 ≈
    (qpow ((1 : Q') + u) m + -T) * ((1 : Q') + u) + B
  refine Q'.eqv_trans _
      (qpow ((1 : Q') + u) m * ((1 : Q') + u) +
        -(T * ((1 : Q') + u) + -B)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ ht1)
  · dsimp only [T, T1, B]
    cubic_ring

private theorem one_le_qpow {q : Q'} (hq : (1 : Q') ≤ q) :
    ∀ n, (1 : Q') ≤ qpow q n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hq0 : (0 : Q') ≤ q := Q'.le_trans' _ _ _ (by decide) hq
      have hp0 : (0 : Q') ≤ qpow q n := qpow_nonneg q hq0 n
      have hs : qpow q n * (1 : Q') ≤ qpow q n * q :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hq hp0
      exact Q'.le_trans' _ _ _ (one_le_qpow hq n)
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) hs)

theorem qpow_taylor2_remainder_le_cubic_power {u : Q'}
    (hu : (0 : Q') ≤ u) : ∀ m,
    qpow ((1 : Q') + u) m + -taylor2 u m ≤
      Q'.ofNat (cubicCoeff m) * (u * (u * u)) *
        qpow ((1 : Q') + u) m
  | 0 => by
      have ht0 : taylor2 u 0 ≈ (1 : Q') := by
        unfold taylor2 lowerSixQuadraticCoeff
        have hz1 : Q'.ofNat 0 * u ≈ (0 : Q') :=
          Q'.eqv_trans _ (0 * u) _
            (Q'.mul_eqv_congr_right _ _ u Q'.ofNat_zero_eqv)
            (Q'.zero_mul_eqv u)
        have hz2 : Q'.ofNat 0 * (u * u) ≈ (0 : Q') :=
          Q'.eqv_trans _ (0 * (u * u)) _
            (Q'.mul_eqv_congr_right _ _ (u * u) Q'.ofNat_zero_eqv)
            (Q'.zero_mul_eqv (u * u))
        refine Q'.eqv_trans _ (((1 : Q') + 0) + 0) _
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr_left (1 : Q') _ _ hz1) hz2) ?_
        exact Q'.eqv_trans _ ((1 : Q') + 0) _
          (QPoly.q_add_zero_eqv _) (QPoly.q_add_zero_eqv _)
      have hl : (1 : Q') + -taylor2 u 0 ≈ 0 :=
        Q'.eqv_trans _ ((1 : Q') + -(1 : Q')) _
          (Q'.add_eqv_congr_left (1 : Q') _ _
            (Q'.neg_eqv_congr _ _ ht0))
          (Q'.add_neg_self_eqv _)
      have hr : Q'.ofNat (cubicCoeff 0) * (u * (u * u)) * (1 : Q') ≈
          (0 : Q') := by
        unfold cubicCoeff
        refine Q'.eqv_trans _ ((0 : Q') * (u * (u * u)) * 1) _
          (Q'.mul_eqv_congr_right _ _ 1
            (Q'.mul_eqv_congr_right _ _ (u * (u * u))
              Q'.ofNat_zero_eqv)) ?_
        exact Q'.eqv_trans _ ((0 : Q') * 1) _
          (Q'.mul_eqv_congr_right _ _ 1 (Q'.zero_mul_eqv _))
          (Q'.zero_mul_eqv _)
      apply Q'.le_of_eqv
      exact Q'.eqv_trans _ 0 _ hl (Q'.eqv_symm hr)
  | m + 1 => by
      let r := (1 : Q') + u
      let P := qpow r m
      let P1 := qpow r (m + 1)
      let R := P + -taylor2 u m
      let A := Q'.ofNat (cubicCoeff m) * (u * (u * u))
      let B := Q'.ofNat (lowerSixQuadraticCoeff m) * (u * (u * u))
      have hr0 : (0 : Q') ≤ r := Q'.zero_le_add _ _ (by decide) hu
      have hR := qpow_taylor2_remainder_le_cubic_power hu m
      have hmul : R * r ≤ (A * P) * r :=
        Q'.mul_le_mul_of_nonneg_right _ _ r hR hr0
      have hP1 : P * r ≈ P1 := by
        dsimp only [P, P1, r]
        exact Q'.eqv_refl _
      have hAP : (A * P) * r ≈ A * P1 := by
        refine Q'.eqv_trans _ (A * (P * r)) _ (Q'.mul_assoc_eqv _ _ _) ?_
        exact Q'.mul_eqv_congr_left _ _ _ hP1
      have hRmul : R * r ≤ A * P1 :=
        Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hAP)
      have hr1 : (1 : Q') ≤ r := Q'.add_le_self_of_nonneg _ _ hu
      have hP1one : (1 : Q') ≤ P1 := by
        dsimp only [P1, r]
        exact one_le_qpow hr1 (m + 1)
      have hu3 : (0 : Q') ≤ u * (u * u) :=
        Q'.mul_nonneg _ _ hu (Q'.mul_nonneg _ _ hu hu)
      have hB0 : (0 : Q') ≤ B :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) hu3
      have hBP := Q'.mul_le_mul_of_nonneg_left _ _ B hP1one hB0
      have hBone : B ≈ B * (1 : Q') := Q'.eqv_symm (Q'.mul_one_eqv B)
      have hBmul : B ≤ B * P1 :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv hBone) hBP
      have hadd := Q'.add_le_add hRmul hBmul
      have hstep := remainder_step u m
      have hcoeff : Q'.ofNat (cubicCoeff (m + 1)) ≈
          Q'.ofNat (cubicCoeff m) +
            Q'.ofNat (lowerSixQuadraticCoeff m) := by
        rw [cubicCoeff]
        exact Q'.ofNat_add_eqv _ _
      have hright : A * P1 + B * P1 ≈
          Q'.ofNat (cubicCoeff (m + 1)) * (u * (u * u)) * P1 := by
        dsimp only [A, B]
        refine Q'.eqv_trans _
          ((Q'.ofNat (cubicCoeff m) +
            Q'.ofNat (lowerSixQuadraticCoeff m)) *
              (u * (u * u)) * P1) _ ?_ ?_
        · ring_qeqv
        · exact Q'.mul_eqv_congr_right _ _ P1
            (Q'.mul_eqv_congr_right _ _ (u * (u * u))
              (Q'.eqv_symm hcoeff))
      dsimp only [P, P1, R, A, B, r] at hstep hadd ⊢
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hstep) hadd)
        (Q'.le_of_eqv hright)

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
    cubic_ring

theorem lowerSixQuadraticTaylorFactorRemainder_le_cubic_power
    (k n : Nat) :
    lowerSixWeightDriftFactor k n +
        -lowerSixQuadraticTaylorFactor k n ≤
      Q'.ofNat (cubicCoeff (n * n)) *
          (lowerSixDriftExcess k *
            (lowerSixDriftExcess k * lowerSixDriftExcess k)) *
        lowerSixWeightDriftFactor k n := by
  let e := lowerSixDriftExcess k
  let m := n * n
  let C := Q'.ofNat (cubicCoeff m) * (e * (e * e))
  have hb := squared_drift_base_eqv_one_add_excess k
  have hp : lowerSixWeightDriftFactor k n ≈
      qpow ((1 : Q') + e) m := by
    unfold lowerSixWeightDriftFactor
    dsimp only [e, m]
    exact qpow_eqv_congr_base hb (n * n)
  have hpoly : lowerSixQuadraticTaylorFactor k n ≈ taylor2 e m := by
    unfold lowerSixQuadraticTaylorFactor lowerSixWeightDriftFloor
      lowerSixWeightDriftQuadratic taylor2
    exact Q'.eqv_refl _
  have h := qpow_taylor2_remainder_le_cubic_power
    (lowerSixDriftExcess_nonnegative k) m
  have hleft :
      lowerSixWeightDriftFactor k n +
          -lowerSixQuadraticTaylorFactor k n ≈
        qpow ((1 : Q') + e) m + -taylor2 e m :=
    Q'.add_eqv_congr' hp (Q'.neg_eqv_congr _ _ hpoly)
  have hright : C * qpow ((1 : Q') + e) m ≈
      Q'.ofNat (cubicCoeff (n * n)) *
          (lowerSixDriftExcess k *
            (lowerSixDriftExcess k * lowerSixDriftExcess k)) *
        lowerSixWeightDriftFactor k n := by
    dsimp only [C, e, m]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hp)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

#print axioms qpow_taylor2_remainder_le_cubic_power
#print axioms lowerSixQuadraticTaylorFactorRemainder_le_cubic_power

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
