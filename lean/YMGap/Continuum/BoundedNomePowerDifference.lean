/-
# Damped power sensitivity on a bounded nome interval

The ordinary power-difference estimate loses the geometric factor.  This
version retains it by assuming both bases lie below an explicit bound `W`.
-/

import YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability

namespace YMGap.Continuum.BoundedNomePowerDifference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RingNormaliser
  (PolyExpr normalize poly_identity_of_normal_eq)
open YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             try ac_rfl))

private def powerDifferenceStepL : PolyExpr :=
  let px := PolyExpr.var 0
  let py := PolyExpr.var 1
  let x := PolyExpr.var 2
  let y := PolyExpr.var 3
  .add (.mul px x) (.neg (.mul py y))

private def powerDifferenceStepR : PolyExpr :=
  let px := PolyExpr.var 0
  let py := PolyExpr.var 1
  let x := PolyExpr.var 2
  let y := PolyExpr.var 3
  .add (.mul px (.add x (.neg y))) (.mul y (.add px (.neg py)))

private theorem powerDifferenceStep_normal :
    normalize powerDifferenceStepL = normalize powerDifferenceStepR := by
  decide

private theorem power_difference_step (px py x y : Q') :
    px * x + -(py * y) ≈
      px * (x + -y) + y * (px + -py) := by
    simpa [powerDifferenceStepL, powerDifferenceStepR,
      YMGap.Continuum.RingNormaliser.eval] using
    (poly_identity_of_normal_eq powerDifferenceStepL powerDifferenceStepR
      powerDifferenceStep_normal
      (fun | 0 => px | 1 => py | 2 => x | _ => y))

/-- The bounded-base power difference retains one full `W` damping factor. -/
theorem weighted_qpow_difference {u v W : Q'}
    (hu0 : (0 : Q') ≤ u) (hv0 : (0 : Q') ≤ v)
    (huW : u ≤ W) (hvW : v ≤ W) (hW : (0 : Q') < W) (n : Nat) :
    W * Q'.abs (qpow u n + -(qpow v n)) ≤
      (Q'.ofNat n * qpow W n) * Q'.abs (u + -v) := by
  have hW0 : (0 : Q') ≤ W := Q'.le_of_lt hW
  induction n with
  | zero =>
      have hleft : W * Q'.abs (qpow u 0 + -(qpow v 0)) ≈ (0 : Q') := by
        simp only [YMGap.Continuum.RGTransport.qpow]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (YMGap.Continuum.TsumDeriv.Q'.abs_eqv_congr
              (Q'.add_neg_self_eqv (1 : Q'))))
          (Q'.mul_zero_eqv W)
      have hright :
          ((Q'.ofNat 0) * qpow W 0) * Q'.abs (u + -v) ≈ (0 : Q') := by
        simp only [YMGap.Continuum.RGTransport.qpow]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (by decide))
          (Q'.zero_mul_eqv _)
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright))
  | succ n ih =>
      let difference := u + -v
      let previous := qpow u n + -(qpow v n)
      have hdecompose :
          qpow u (n + 1) + -(qpow v (n + 1)) ≈
            qpow u n * difference + v * previous := by
        dsimp [difference, previous]
        change
          (qpow u n * u + -(qpow v n * v)) ≈
            qpow u n * (u + -v) + v * (qpow u n + -qpow v n)
        exact power_difference_step (qpow u n) (qpow v n) u v
      have htriangle :
          W * Q'.abs (qpow u (n + 1) + -(qpow v (n + 1))) ≤
            W * (Q'.abs (qpow u n * difference) +
              Q'.abs (v * previous)) := by
        refine Q'.mul_le_mul_of_nonneg_left _ _ W ?_ hW0
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (YMGap.Continuum.TsumDeriv.Q'.abs_eqv_congr hdecompose))
          (YMGap.Continuum.TsumDeriv.abs_add_le _ _)
      have huPow : qpow u n ≤ qpow W n := qpow_mono hu0 huW n
      have huPow0 : (0 : Q') ≤ qpow u n := qpow_nonneg u hu0 n
      have hfirst :
          W * Q'.abs (qpow u n * difference) ≤
            qpow W (n + 1) * Q'.abs difference := by
        have habs := YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
          (qpow u n) difference
        have hqpowAbs : Q'.abs (qpow u n) ≤ qpow W n := by
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv
              (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg huPow0)) huPow
        have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _ hqpowAbs
          (Q'.abs_nonneg difference)
        have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ W hmul hW0
        have hrewrite :
            W * (qpow W n * Q'.abs difference) ≈
              qpow W (n + 1) * Q'.abs difference := by
          simp only [YMGap.Continuum.RGTransport.qpow]
          ring_qeqv
        exact Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ W habs hW0)
          (Q'.le_trans' _ _ _ hscaled
            (Q'.le_of_eqv hrewrite))
      have hsecond :
          W * Q'.abs (v * previous) ≤
            (Q'.ofNat n * qpow W (n + 1)) * Q'.abs difference := by
        have habs := YMGap.Continuum.TsumDeriv.Q'.abs_mul_le v previous
        have hvabs : Q'.abs v ≤ W := by
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv
              (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hv0)) hvW
        have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _ hvabs
          (Q'.abs_nonneg previous)
        have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hmul hW0
        have hi := ih
        have hscaledIh := Q'.mul_le_mul_of_nonneg_left _ _ W hi hW0
        have hrewrite :
            W * ((Q'.ofNat n * qpow W n) * Q'.abs difference) ≈
              (Q'.ofNat n * qpow W (n + 1)) * Q'.abs difference := by
          simp only [YMGap.Continuum.RGTransport.qpow]
          ring_qeqv
        exact Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ W habs hW0)
          (Q'.le_trans' _ _ _ hscaled
            (Q'.le_trans' _ _ _ hscaledIh
              (Q'.le_of_eqv hrewrite)))
      have hsum := Q'.add_le_add hfirst hsecond
      have hsplit :
          W * (Q'.abs (qpow u n * difference) + Q'.abs (v * previous)) ≤
            W * Q'.abs (qpow u n * difference) +
              W * Q'.abs (v * previous) :=
        Q'.le_of_eqv (Q'.mul_add_eqv W _ _)
      have hsum' := Q'.le_trans' _ _ _ hsplit hsum
      have hsum_eqv :
          qpow W (n + 1) * Q'.abs difference +
              (Q'.ofNat n * qpow W (n + 1)) * Q'.abs difference ≈
            ((Q'.ofNat n + 1) * qpow W (n + 1)) *
              Q'.abs difference := by
        ring_qeqv
      have hnat : Q'.ofNat (n + 1) ≈ Q'.ofNat n + 1 := by
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
          (Q'.add_eqv_congr_left _ _ _
            (by decide : Q'.ofNat 1 ≈ (1 : Q')))
      have htarget :
          ((Q'.ofNat n + 1) * qpow W (n + 1)) *
              Q'.abs difference ≈
            (Q'.ofNat (n + 1) * qpow W (n + 1)) *
              Q'.abs difference := by
        exact Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hnat))
      exact Q'.le_trans' _ _ _ htriangle
        (Q'.le_trans' _ _ _ hsum'
          (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hsum_eqv htarget)))

#print axioms YMGap.Continuum.BoundedNomePowerDifference.weighted_qpow_difference

end YMGap.Continuum.BoundedNomePowerDifference
