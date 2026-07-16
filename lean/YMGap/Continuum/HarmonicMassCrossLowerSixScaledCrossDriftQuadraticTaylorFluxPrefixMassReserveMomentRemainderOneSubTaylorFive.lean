/-
Fourth/fifth alternating enclosure for powers of `1-u`.

The cubic error is adequate for coarse slope localization but too large for
the `D^4`-cleared finite-Hermite remainder.  Two further Pascal orders give
an exact quintic error envelope while retaining the same constructive
induction on `0 <= u <= 1`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem one_sub_five_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "one_sub_five_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               one_sub_five_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Int.natCast_add, Int.natCast_one,
               Int.natCast_zero,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Subtraction-free fourth Pascal coefficient. -/
def quarticCoeff : Nat → Nat
  | 0 => 0
  | m + 1 => quarticCoeff m + cubicCoeff m

/-- Subtraction-free fifth Pascal coefficient. -/
def quinticCoeff : Nat → Nat
  | 0 => 0
  | m + 1 => quinticCoeff m + quarticCoeff m

/-- Fourth alternating truncation of `(1-u)^m`. -/
def oneSubTaylor4 (u : Q') (m : Nat) : Q' :=
  oneSubTaylor3 u m +
    Q'.ofNat (quarticCoeff m) * (u * (u * (u * u)))

/-- Fifth alternating truncation of `(1-u)^m`. -/
def oneSubTaylor5 (u : Q') (m : Nat) : Q' :=
  oneSubTaylor4 u m +
    -(Q'.ofNat (quinticCoeff m) * (u * (u * (u * (u * u)))))

private abbrev PE := RingNormaliser.PolyExpr

private def pTaylor4StepL : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let B : PE := .var 2
  let A : PE := .var 3
  let u : PE := .var 4
  .mul
    (.add
      (.add
        (.add
          (.add (.const 1) (.neg (.mul M u)))
          (.mul C (.mul u u)))
        (.neg (.mul B (.mul u (.mul u u)))))
      (.mul A (.mul u (.mul u (.mul u u)))))
    (.add (.const 1) (.neg u))

private def pTaylor4StepR : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let B : PE := .var 2
  let A : PE := .var 3
  let u : PE := .var 4
  .add
    (.add
      (.add
        (.add
          (.add (.const 1) (.neg (.mul (.add M (.const 1)) u)))
          (.mul (.add C M) (.mul u u)))
        (.neg (.mul (.add B C) (.mul u (.mul u u)))))
      (.mul (.add A B) (.mul u (.mul u (.mul u u)))))
    (.neg (.mul A (.mul u (.mul u (.mul u (.mul u u))))))

private theorem pTaylor4Step_normal :
    RingNormaliser.normalize pTaylor4StepL =
      RingNormaliser.normalize pTaylor4StepR := by decide

private def pTaylor5StepL : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let B : PE := .var 2
  let A : PE := .var 3
  let E : PE := .var 4
  let u : PE := .var 5
  .mul
    (.add
      (.add
        (.add
          (.add
            (.add (.const 1) (.neg (.mul M u)))
            (.mul C (.mul u u)))
          (.neg (.mul B (.mul u (.mul u u)))))
        (.mul A (.mul u (.mul u (.mul u u)))))
      (.neg (.mul E (.mul u (.mul u (.mul u (.mul u u)))))))
    (.add (.const 1) (.neg u))

private def pTaylor5StepR : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let B : PE := .var 2
  let A : PE := .var 3
  let E : PE := .var 4
  let u : PE := .var 5
  .add
    (.add
      (.add
        (.add
          (.add
            (.add (.const 1) (.neg (.mul (.add M (.const 1)) u)))
            (.mul (.add C M) (.mul u u)))
          (.neg (.mul (.add B C) (.mul u (.mul u u)))))
        (.mul (.add A B) (.mul u (.mul u (.mul u u)))))
      (.neg (.mul (.add E A)
        (.mul u (.mul u (.mul u (.mul u u)))))))
    (.mul E (.mul u (.mul u (.mul u (.mul u (.mul u u))))))

private theorem pTaylor5Step_normal :
    RingNormaliser.normalize pTaylor5StepL =
      RingNormaliser.normalize pTaylor5StepR := by decide

private def pTaylorCancelL : PE :=
  .add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))

private def pTaylorCancelR : PE := .var 1

private theorem pTaylorCancel_normal :
    RingNormaliser.normalize pTaylorCancelL =
      RingNormaliser.normalize pTaylorCancelR := by decide

private theorem taylor4_step_algebra (M C B A u : Q') :
    (((((1 : Q') + -(M * u)) + C * (u * u)) +
        -(B * (u * (u * u)))) +
        A * (u * (u * (u * u)))) * ((1 : Q') + -u) ≈
      (((((1 : Q') + -((M + 1) * u)) +
          (C + M) * (u * u)) +
          -((B + C) * (u * (u * u)))) +
          (A + B) * (u * (u * (u * u)))) +
          -(A * (u * (u * (u * (u * u))))) := by
  let rho : Nat → Q' := fun
    | 0 => M | 1 => C | 2 => B | 3 => A | _ => u
  simpa [pTaylor4StepL, pTaylor4StepR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTaylor4StepL pTaylor4StepR pTaylor4Step_normal rho)

private theorem taylor5_step_algebra (M C B A E u : Q') :
    ((((((1 : Q') + -(M * u)) + C * (u * u)) +
        -(B * (u * (u * u)))) +
        A * (u * (u * (u * u)))) +
        -(E * (u * (u * (u * (u * u)))))) * ((1 : Q') + -u) ≈
      ((((((1 : Q') + -((M + 1) * u)) +
          (C + M) * (u * u)) +
          -((B + C) * (u * (u * u)))) +
          (A + B) * (u * (u * (u * u)))) +
          -((E + A) * (u * (u * (u * (u * u)))))) +
          E * (u * (u * (u * (u * (u * u))))) := by
  let rho : Nat → Q' := fun
    | 0 => M | 1 => C | 2 => B | 3 => A | 4 => E | _ => u
  simpa [pTaylor5StepL, pTaylor5StepR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTaylor5StepL pTaylor5StepR pTaylor5Step_normal rho)

private theorem taylor_cancel_algebra (T E : Q') :
    T + -(T + -E) ≈ E := by
  let rho : Nat → Q' := fun | 0 => T | _ => E
  simpa [pTaylorCancelL, pTaylorCancelR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTaylorCancelL pTaylorCancelR pTaylorCancel_normal rho)

private theorem oneSubTaylor4_step (u : Q') (m : Nat) :
    oneSubTaylor4 u m * ((1 : Q') + -u) ≈
      oneSubTaylor4 u (m + 1) +
        -(Q'.ofNat (quarticCoeff m) *
          (u * (u * (u * (u * u))))) := by
  let M := Q'.ofNat m
  let C := Q'.ofNat (lowerSixQuadraticCoeff m)
  let B := Q'.ofNat (cubicCoeff m)
  let A := Q'.ofNat (quarticCoeff m)
  let S := (((((1 : Q') + -((M + 1) * u)) +
      (C + M) * (u * u)) +
      -((B + C) * (u * (u * u)))) +
      (A + B) * (u * (u * (u * u))))
  let E := A * (u * (u * (u * (u * u))))
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
  have ha : Q'.ofNat (quarticCoeff (m + 1)) ≈ A + B := by
    rw [quarticCoeff]
    dsimp only [A, B]
    exact Q'.ofNat_add_eqv _ _
  have hsucc : oneSubTaylor4 u (m + 1) ≈ S := by
    unfold oneSubTaylor4 oneSubTaylor3 oneSubTaylor2
    dsimp only [S]
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left (1 : Q') _ _
            (Q'.neg_eqv_congr _ _
              (Q'.mul_eqv_congr_right _ _ u hm)))
          (Q'.mul_eqv_congr_right _ _ (u * u) hc))
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_right _ _ (u * (u * u)) hb)))
      (Q'.mul_eqv_congr_right _ _ (u * (u * (u * u))) ha)
  change (((((1 : Q') + -(M * u)) + C * (u * u)) +
      -(B * (u * (u * u)))) + A * (u * (u * (u * u)))) *
        ((1 : Q') + -u) ≈ oneSubTaylor4 u (m + 1) + -E
  refine Q'.eqv_trans _ (S + -E) _
    (by
      dsimp only [S, E]
      exact taylor4_step_algebra M C B A u) ?_
  exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsucc)

private theorem oneSubTaylor5_step (u : Q') (m : Nat) :
    oneSubTaylor5 u m * ((1 : Q') + -u) ≈
      oneSubTaylor5 u (m + 1) +
        Q'.ofNat (quinticCoeff m) *
          (u * (u * (u * (u * (u * u))))) := by
  let M := Q'.ofNat m
  let C := Q'.ofNat (lowerSixQuadraticCoeff m)
  let B := Q'.ofNat (cubicCoeff m)
  let A := Q'.ofNat (quarticCoeff m)
  let E := Q'.ofNat (quinticCoeff m)
  let S := ((((((1 : Q') + -((M + 1) * u)) +
      (C + M) * (u * u)) +
      -((B + C) * (u * (u * u)))) +
      (A + B) * (u * (u * (u * u)))) +
      -((E + A) * (u * (u * (u * (u * u))))))
  let F := E * (u * (u * (u * (u * (u * u)))))
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
  have ha : Q'.ofNat (quarticCoeff (m + 1)) ≈ A + B := by
    rw [quarticCoeff]
    dsimp only [A, B]
    exact Q'.ofNat_add_eqv _ _
  have he : Q'.ofNat (quinticCoeff (m + 1)) ≈ E + A := by
    rw [quinticCoeff]
    dsimp only [E, A]
    exact Q'.ofNat_add_eqv _ _
  have hsucc : oneSubTaylor5 u (m + 1) ≈ S := by
    unfold oneSubTaylor5 oneSubTaylor4 oneSubTaylor3 oneSubTaylor2
    dsimp only [S]
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr_left (1 : Q') _ _
              (Q'.neg_eqv_congr _ _
                (Q'.mul_eqv_congr_right _ _ u hm)))
            (Q'.mul_eqv_congr_right _ _ (u * u) hc))
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_right _ _ (u * (u * u)) hb)))
        (Q'.mul_eqv_congr_right _ _ (u * (u * (u * u))) ha))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _
          (u * (u * (u * (u * u)))) he))
  change ((((((1 : Q') + -(M * u)) + C * (u * u)) +
      -(B * (u * (u * u)))) + A * (u * (u * (u * u)))) +
      -(E * (u * (u * (u * (u * u)))))) *
        ((1 : Q') + -u) ≈ oneSubTaylor5 u (m + 1) + F
  refine Q'.eqv_trans _ (S + F) _
    (by
      dsimp only [S, F]
      exact taylor5_step_algebra M C B A E u) ?_
  exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsucc)

private theorem oneSubTaylor4_zero (u : Q') :
    oneSubTaylor4 u 0 ≈ (1 : Q') := by
  unfold oneSubTaylor4 oneSubTaylor3 oneSubTaylor2 quarticCoeff cubicCoeff
    lowerSixQuadraticCoeff
  one_sub_five_ring

private theorem oneSubTaylor5_zero (u : Q') :
    oneSubTaylor5 u 0 ≈ (1 : Q') := by
  unfold oneSubTaylor5 oneSubTaylor4 oneSubTaylor3 oneSubTaylor2
    quinticCoeff quarticCoeff cubicCoeff lowerSixQuadraticCoeff
  one_sub_five_ring

private theorem fifth_nonnegative {u : Q'} (hu : (0 : Q') ≤ u) :
    (0 : Q') ≤ u * (u * (u * (u * u))) :=
  Q'.mul_nonneg _ _ hu
    (Q'.mul_nonneg _ _ hu
      (Q'.mul_nonneg _ _ hu (Q'.mul_nonneg _ _ hu hu)))

private theorem sixth_nonnegative {u : Q'} (hu : (0 : Q') ≤ u) :
    (0 : Q') ≤ u * (u * (u * (u * (u * u)))) :=
  Q'.mul_nonneg _ _ hu
    (Q'.mul_nonneg _ _ hu
      (Q'.mul_nonneg _ _ hu
        (Q'.mul_nonneg _ _ hu (Q'.mul_nonneg _ _ hu hu))))

/-- Even alternating truncation: `(1-u)^m <= T4`. -/
theorem qpow_oneSub_le_taylor4
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    ∀ m, qpow ((1 : Q') + -u) m ≤ oneSubTaylor4 u m
  | 0 => Q'.le_of_eqv (Q'.eqv_symm (oneSubTaylor4_zero u))
  | m + 1 => by
      let r := (1 : Q') + -u
      let E := Q'.ofNat (quarticCoeff m) *
        (u * (u * (u * (u * u))))
      have hr0 : (0 : Q') ≤ r := by
        dsimp only [r]
        exact Q'.sub_nonneg_of_le hu1
      have hmul := Q'.mul_le_mul_of_nonneg_right _ _ r
        (qpow_oneSub_le_taylor4 hu0 hu1 m) hr0
      have hstep := oneSubTaylor4_step u m
      have hE0 : (0 : Q') ≤ E :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
          (fifth_nonnegative hu0)
      have hnegE : -E ≤ (0 : Q') := Q'.nonpos_neg_of_nonneg hE0
      have hdrop := Q'.add_le_add_left (oneSubTaylor4 u (m + 1))
        (-E) (0 : Q') hnegE
      have hzero : oneSubTaylor4 u (m + 1) + (0 : Q') ≈
          oneSubTaylor4 u (m + 1) := QPoly.q_add_zero_eqv _
      dsimp only [r, E] at hmul hstep hdrop hzero ⊢
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hstep)
          (Q'.le_trans' _ _ _ hdrop (Q'.le_of_eqv hzero)))

/-- Odd alternating truncation: `T5 <= (1-u)^m`. -/
theorem taylor5_le_qpow_oneSub
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    ∀ m, oneSubTaylor5 u m ≤ qpow ((1 : Q') + -u) m
  | 0 => Q'.le_of_eqv (oneSubTaylor5_zero u)
  | m + 1 => by
      let r := (1 : Q') + -u
      let E := Q'.ofNat (quinticCoeff m) *
        (u * (u * (u * (u * (u * u)))))
      have hr0 : (0 : Q') ≤ r := by
        dsimp only [r]
        exact Q'.sub_nonneg_of_le hu1
      have hmul := Q'.mul_le_mul_of_nonneg_right _ _ r
        (taylor5_le_qpow_oneSub hu0 hu1 m) hr0
      have hstep := oneSubTaylor5_step u m
      have hE0 : (0 : Q') ≤ E :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
          (sixth_nonnegative hu0)
      have hadd := Q'.add_le_self_of_nonneg
        (oneSubTaylor5 u (m + 1)) E hE0
      dsimp only [r, E] at hmul hstep hadd ⊢
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hstep)) hmul)

/-- The fourth-order overshoot is nonnegative. -/
theorem qpow_oneSub_taylor4_error_nonnegative
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (m : Nat) :
    (0 : Q') ≤ oneSubTaylor4 u m +
      -qpow ((1 : Q') + -u) m := by
  exact Q'.sub_nonneg_of_le (qpow_oneSub_le_taylor4 hu0 hu1 m)

/-- Sharp constructive quintic envelope for the fourth-order overshoot. -/
theorem qpow_oneSub_taylor4_error_le_quintic
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (m : Nat) :
    oneSubTaylor4 u m + -qpow ((1 : Q') + -u) m ≤
      Q'.ofNat (quinticCoeff m) * (u * (u * (u * (u * u)))) := by
  let P := qpow ((1 : Q') + -u) m
  let T4 := oneSubTaylor4 u m
  let E := Q'.ofNat (quinticCoeff m) * (u * (u * (u * (u * u))))
  have hlower := taylor5_le_qpow_oneSub hu0 hu1 m
  have hneg := Q'.neg_le_neg hlower
  have hadd := Q'.add_le_add_left T4 (-P) (-(oneSubTaylor5 u m)) hneg
  have hright : T4 + -(oneSubTaylor5 u m) ≈ E := by
    unfold oneSubTaylor5
    dsimp only [T4, E]
    exact taylor_cancel_algebra _ _
  dsimp only [P, T4, E] at hadd hright ⊢
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright)

#print axioms qpow_oneSub_le_taylor4
#print axioms taylor5_le_qpow_oneSub
#print axioms qpow_oneSub_taylor4_error_nonnegative
#print axioms qpow_oneSub_taylor4_error_le_quintic

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive
