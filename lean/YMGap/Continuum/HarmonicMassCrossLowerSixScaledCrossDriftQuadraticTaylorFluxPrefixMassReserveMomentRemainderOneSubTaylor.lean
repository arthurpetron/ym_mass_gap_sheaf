/-
Constructive alternating Taylor enclosure for powers of `1-u`.

The quadratic truncation is an upper bound and the cubic truncation is a
lower bound on `0 <= u <= 1`.  Hence the exact quadratic overshoot is between
zero and the third Pascal coefficient times `u^3`.  This is the local engine
needed to bound the old- and next-scale root slopes in the signed Hermite
remainder.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderHeadFloor

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem one_sub_taylor_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "one_sub_taylor_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               one_sub_taylor_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Int.natCast_add, Int.natCast_one,
               Int.natCast_zero,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

private abbrev PE := RingNormaliser.PolyExpr

private def pTaylor2StepL : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let u : PE := .var 2
  .mul
    (.add (.add (.const 1) (.neg (.mul M u)))
      (.mul C (.mul u u)))
    (.add (.const 1) (.neg u))

private def pTaylor2StepR : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let u : PE := .var 2
  .add
    (.add (.add (.const 1)
      (.neg (.mul (.add M (.const 1)) u)))
      (.mul (.add C M) (.mul u u)))
    (.neg (.mul C (.mul u (.mul u u))))

private theorem pTaylor2Step_normal :
    RingNormaliser.normalize pTaylor2StepL =
      RingNormaliser.normalize pTaylor2StepR := by decide

private def pTaylor3StepL : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let B : PE := .var 2
  let u : PE := .var 3
  .mul
    (.add
      (.add (.add (.const 1) (.neg (.mul M u)))
        (.mul C (.mul u u)))
      (.neg (.mul B (.mul u (.mul u u)))))
    (.add (.const 1) (.neg u))

private def pTaylor3StepR : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let B : PE := .var 2
  let u : PE := .var 3
  .add
    (.add
      (.add (.add (.const 1)
        (.neg (.mul (.add M (.const 1)) u)))
        (.mul (.add C M) (.mul u u)))
      (.neg (.mul (.add B C) (.mul u (.mul u u)))))
    (.mul B (.mul u (.mul u (.mul u u))))

private theorem pTaylor3Step_normal :
    RingNormaliser.normalize pTaylor3StepL =
      RingNormaliser.normalize pTaylor3StepR := by decide

private def pTaylorCancelL : PE :=
  .add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))

private def pTaylorCancelR : PE := .var 1

private theorem pTaylorCancel_normal :
    RingNormaliser.normalize pTaylorCancelL =
      RingNormaliser.normalize pTaylorCancelR := by decide

private theorem taylor2_step_algebra (M C u : Q') :
    (((1 : Q') + -(M * u)) + C * (u * u)) * ((1 : Q') + -u) ≈
      (((1 : Q') + -((M + 1) * u)) + (C + M) * (u * u)) +
        -(C * (u * (u * u))) := by
  let rho : Nat → Q' := fun | 0 => M | 1 => C | _ => u
  simpa [pTaylor2StepL, pTaylor2StepR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTaylor2StepL pTaylor2StepR pTaylor2Step_normal rho)

private theorem taylor3_step_algebra (M C B u : Q') :
    ((((1 : Q') + -(M * u)) + C * (u * u)) +
        -(B * (u * (u * u)))) * ((1 : Q') + -u) ≈
      ((((1 : Q') + -((M + 1) * u)) + (C + M) * (u * u)) +
        -((B + C) * (u * (u * u)))) +
          B * (u * (u * (u * u))) := by
  let rho : Nat → Q' := fun | 0 => M | 1 => C | 2 => B | _ => u
  simpa [pTaylor3StepL, pTaylor3StepR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTaylor3StepL pTaylor3StepR pTaylor3Step_normal rho)

private theorem taylor_cancel_algebra (T E : Q') :
    T + -(T + -E) ≈ E := by
  let rho : Nat → Q' := fun | 0 => T | _ => E
  simpa [pTaylorCancelL, pTaylorCancelR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTaylorCancelL pTaylorCancelR pTaylorCancel_normal rho)

/-- Quadratic alternating truncation of `(1-u)^m`. -/
def oneSubTaylor2 (u : Q') (m : Nat) : Q' :=
  ((1 : Q') + -(Q'.ofNat m * u)) +
    Q'.ofNat (lowerSixQuadraticCoeff m) * (u * u)

/-- Cubic alternating truncation of `(1-u)^m`. -/
def oneSubTaylor3 (u : Q') (m : Nat) : Q' :=
  oneSubTaylor2 u m +
    -(Q'.ofNat (cubicCoeff m) * (u * (u * u)))

private theorem oneSubTaylor2_step (u : Q') (m : Nat) :
    oneSubTaylor2 u m * ((1 : Q') + -u) ≈
      oneSubTaylor2 u (m + 1) +
        -(Q'.ofNat (lowerSixQuadraticCoeff m) * (u * (u * u))) := by
  let M := Q'.ofNat m
  let C := Q'.ofNat (lowerSixQuadraticCoeff m)
  let S := ((1 : Q') + -((M + 1) * u)) + (C + M) * (u * u)
  let E := C * (u * (u * u))
  have hm : Q'.ofNat (m + 1) ≈ M + (1 : Q') := by
    dsimp only [M]
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv m 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hc : Q'.ofNat (lowerSixQuadraticCoeff (m + 1)) ≈ C + M := by
    rw [lowerSixQuadraticCoeff]
    dsimp only [C, M]
    exact Q'.ofNat_add_eqv _ _
  have hsucc : oneSubTaylor2 u (m + 1) ≈ S := by
    unfold oneSubTaylor2
    dsimp only [S]
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left (1 : Q') _ _
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_right _ _ u hm)))
      (Q'.mul_eqv_congr_right _ _ (u * u) hc)
  change (((1 : Q') + -(M * u)) + C * (u * u)) *
      ((1 : Q') + -u) ≈ oneSubTaylor2 u (m + 1) + -E
  refine Q'.eqv_trans _ (S + -E) _
    (by
      dsimp only [S, E]
      exact taylor2_step_algebra M C u) ?_
  exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsucc)

private theorem oneSubTaylor3_step (u : Q') (m : Nat) :
    oneSubTaylor3 u m * ((1 : Q') + -u) ≈
      oneSubTaylor3 u (m + 1) +
        Q'.ofNat (cubicCoeff m) *
          (u * (u * (u * u))) := by
  let M := Q'.ofNat m
  let C := Q'.ofNat (lowerSixQuadraticCoeff m)
  let B := Q'.ofNat (cubicCoeff m)
  let S := (((1 : Q') + -((M + 1) * u)) + (C + M) * (u * u)) +
    -((B + C) * (u * (u * u)))
  let E := B * (u * (u * (u * u)))
  have hm : Q'.ofNat (m + 1) ≈ M + (1 : Q') := by
    dsimp only [M]
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv m 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hc : Q'.ofNat (lowerSixQuadraticCoeff (m + 1)) ≈ C + M := by
    rw [lowerSixQuadraticCoeff]
    dsimp only [C, M]
    exact Q'.ofNat_add_eqv _ _
  have hb : Q'.ofNat (cubicCoeff (m + 1)) ≈ B + C := by
    rw [cubicCoeff]
    dsimp only [B, C]
    exact Q'.ofNat_add_eqv _ _
  have hsucc : oneSubTaylor3 u (m + 1) ≈ S := by
    unfold oneSubTaylor3 oneSubTaylor2
    dsimp only [S]
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left (1 : Q') _ _
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_right _ _ u hm)))
        (Q'.mul_eqv_congr_right _ _ (u * u) hc))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ (u * (u * u)) hb))
  change ((((1 : Q') + -(M * u)) + C * (u * u)) +
      -(B * (u * (u * u)))) * ((1 : Q') + -u) ≈
        oneSubTaylor3 u (m + 1) + E
  refine Q'.eqv_trans _ (S + E) _
    (by
      dsimp only [S, E]
      exact taylor3_step_algebra M C B u) ?_
  exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsucc)

private theorem oneSubTaylor2_zero (u : Q') :
    oneSubTaylor2 u 0 ≈ (1 : Q') := by
  unfold oneSubTaylor2 lowerSixQuadraticCoeff
  one_sub_taylor_ring

private theorem oneSubTaylor3_zero (u : Q') :
    oneSubTaylor3 u 0 ≈ (1 : Q') := by
  unfold oneSubTaylor3 oneSubTaylor2 cubicCoeff lowerSixQuadraticCoeff
  one_sub_taylor_ring

private theorem cube_nonnegative {u : Q'} (hu : (0 : Q') ≤ u) :
    (0 : Q') ≤ u * (u * u) :=
  Q'.mul_nonneg _ _ hu (Q'.mul_nonneg _ _ hu hu)

private theorem fourth_nonnegative {u : Q'} (hu : (0 : Q') ≤ u) :
    (0 : Q') ≤ u * (u * (u * u)) :=
  Q'.mul_nonneg _ _ hu
    (Q'.mul_nonneg _ _ hu (Q'.mul_nonneg _ _ hu hu))

/-- Even alternating truncation: `(1-u)^m <= T2`. -/
theorem qpow_oneSub_le_taylor2
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    ∀ m, qpow ((1 : Q') + -u) m ≤ oneSubTaylor2 u m
  | 0 => Q'.le_of_eqv (Q'.eqv_symm (oneSubTaylor2_zero u))
  | m + 1 => by
      let r := (1 : Q') + -u
      let E := Q'.ofNat (lowerSixQuadraticCoeff m) * (u * (u * u))
      have hr0 : (0 : Q') ≤ r := by
        dsimp only [r]
        exact Q'.sub_nonneg_of_le hu1
      have hmul := Q'.mul_le_mul_of_nonneg_right _ _ r
        (qpow_oneSub_le_taylor2 hu0 hu1 m) hr0
      have hstep := oneSubTaylor2_step u m
      have hE0 : (0 : Q') ≤ E :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
          (cube_nonnegative hu0)
      have hnegE : -E ≤ (0 : Q') := Q'.nonpos_neg_of_nonneg hE0
      have hdrop := Q'.add_le_add_left (oneSubTaylor2 u (m + 1))
        (-E) (0 : Q') hnegE
      have hzero : oneSubTaylor2 u (m + 1) + (0 : Q') ≈
          oneSubTaylor2 u (m + 1) := QPoly.q_add_zero_eqv _
      dsimp only [r, E] at hmul hstep hdrop hzero ⊢
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hstep)
          (Q'.le_trans' _ _ _ hdrop (Q'.le_of_eqv hzero)))

/-- Odd alternating truncation: `T3 <= (1-u)^m`. -/
theorem taylor3_le_qpow_oneSub
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    ∀ m, oneSubTaylor3 u m ≤ qpow ((1 : Q') + -u) m
  | 0 => Q'.le_of_eqv (oneSubTaylor3_zero u)
  | m + 1 => by
      let r := (1 : Q') + -u
      let E := Q'.ofNat (cubicCoeff m) * (u * (u * (u * u)))
      have hr0 : (0 : Q') ≤ r := by
        dsimp only [r]
        exact Q'.sub_nonneg_of_le hu1
      have hmul := Q'.mul_le_mul_of_nonneg_right _ _ r
        (taylor3_le_qpow_oneSub hu0 hu1 m) hr0
      have hstep := oneSubTaylor3_step u m
      have hE0 : (0 : Q') ≤ E :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
          (fourth_nonnegative hu0)
      have hadd := Q'.add_le_self_of_nonneg
        (oneSubTaylor3 u (m + 1)) E hE0
      dsimp only [r, E] at hmul hstep hadd ⊢
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hstep)) hmul)

/-- The quadratic overshoot is nonnegative. -/
theorem qpow_oneSub_taylor2_error_nonnegative
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (m : Nat) :
    (0 : Q') ≤ oneSubTaylor2 u m + -qpow ((1 : Q') + -u) m := by
  exact Q'.sub_nonneg_of_le (qpow_oneSub_le_taylor2 hu0 hu1 m)

/-- Sharp constructive cubic envelope for the quadratic overshoot. -/
theorem qpow_oneSub_taylor2_error_le_cubic
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (m : Nat) :
    oneSubTaylor2 u m + -qpow ((1 : Q') + -u) m ≤
      Q'.ofNat (cubicCoeff m) * (u * (u * u)) := by
  let P := qpow ((1 : Q') + -u) m
  let T2 := oneSubTaylor2 u m
  let E := Q'.ofNat (cubicCoeff m) * (u * (u * u))
  have hlower := taylor3_le_qpow_oneSub hu0 hu1 m
  have hneg := Q'.neg_le_neg hlower
  have hadd := Q'.add_le_add_left T2 (-P) (-(oneSubTaylor3 u m)) hneg
  have hright : T2 + -(oneSubTaylor3 u m) ≈ E := by
    unfold oneSubTaylor3
    dsimp only [T2, E]
    exact taylor_cancel_algebra _ _
  dsimp only [P, T2, E] at hadd hright ⊢
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright)

#print axioms qpow_oneSub_le_taylor2
#print axioms taylor3_le_qpow_oneSub
#print axioms qpow_oneSub_taylor2_error_nonnegative
#print axioms qpow_oneSub_taylor2_error_le_cubic

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
