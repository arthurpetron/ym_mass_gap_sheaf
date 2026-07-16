/-
Sixth/seventh alternating enclosure for powers of `1-u`.

The fifth-order slope width is too coarse after the coupled `D^5` carrier
clearing.  Two further Pascal orders give the seventh-order width needed for
an independent old/next slope-square enclosure on the square-root prefix.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorSeven

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem one_sub_seven_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "one_sub_seven_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               one_sub_seven_neg_num_cast, Q'.ofNat_num_cast,
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

/-- Subtraction-free sixth Pascal coefficient. -/
def sexticCoeff : Nat → Nat
  | 0 => 0
  | m + 1 => sexticCoeff m + quinticCoeff m

/-- Subtraction-free seventh Pascal coefficient. -/
def septicCoeff : Nat → Nat
  | 0 => 0
  | m + 1 => septicCoeff m + sexticCoeff m

/-- Sixth alternating truncation of `(1-u)^m`. -/
def oneSubTaylor6 (u : Q') (m : Nat) : Q' :=
  oneSubTaylor5 u m +
    Q'.ofNat (sexticCoeff m) *
      (u * (u * (u * (u * (u * u)))))

/-- Seventh alternating truncation of `(1-u)^m`. -/
def oneSubTaylor7 (u : Q') (m : Nat) : Q' :=
  oneSubTaylor6 u m +
    -(Q'.ofNat (septicCoeff m) *
      (u * (u * (u * (u * (u * (u * u)))))))

private abbrev PE := RingNormaliser.PolyExpr

private def pTaylor6StepL : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let B : PE := .var 2
  let A : PE := .var 3
  let E : PE := .var 4
  let F : PE := .var 5
  let u : PE := .var 6
  .mul
    (.add
      (.add
        (.add
          (.add
            (.add
              (.add (.const 1) (.neg (.mul M u)))
              (.mul C (.mul u u)))
            (.neg (.mul B (.mul u (.mul u u)))))
          (.mul A (.mul u (.mul u (.mul u u)))))
        (.neg (.mul E (.mul u (.mul u (.mul u (.mul u u)))))))
      (.mul F (.mul u (.mul u (.mul u (.mul u (.mul u u)))))))
    (.add (.const 1) (.neg u))

private def pTaylor6StepR : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let B : PE := .var 2
  let A : PE := .var 3
  let E : PE := .var 4
  let F : PE := .var 5
  let u : PE := .var 6
  .add
    (.add
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
      (.mul (.add F E)
        (.mul u (.mul u (.mul u (.mul u (.mul u u)))))))
    (.neg (.mul F
      (.mul u (.mul u (.mul u (.mul u (.mul u (.mul u u))))))))

private theorem pTaylor6Step_normal :
    RingNormaliser.normalize pTaylor6StepL =
      RingNormaliser.normalize pTaylor6StepR := by decide

private def pTaylor7StepL : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let B : PE := .var 2
  let A : PE := .var 3
  let E : PE := .var 4
  let F : PE := .var 5
  let G : PE := .var 6
  let u : PE := .var 7
  .mul
    (.add
      (.add
        (.add
          (.add
            (.add
              (.add
                (.add (.const 1) (.neg (.mul M u)))
                (.mul C (.mul u u)))
              (.neg (.mul B (.mul u (.mul u u)))))
            (.mul A (.mul u (.mul u (.mul u u)))))
          (.neg (.mul E (.mul u (.mul u (.mul u (.mul u u)))))))
        (.mul F (.mul u (.mul u (.mul u (.mul u (.mul u u)))))))
      (.neg (.mul G
        (.mul u (.mul u (.mul u (.mul u (.mul u (.mul u u)))))))))
    (.add (.const 1) (.neg u))

private def pTaylor7StepR : PE :=
  let M : PE := .var 0
  let C : PE := .var 1
  let B : PE := .var 2
  let A : PE := .var 3
  let E : PE := .var 4
  let F : PE := .var 5
  let G : PE := .var 6
  let u : PE := .var 7
  .add
    (.add
      (.add
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
        (.mul (.add F E)
          (.mul u (.mul u (.mul u (.mul u (.mul u u)))))))
      (.neg (.mul (.add G F)
        (.mul u (.mul u (.mul u (.mul u (.mul u (.mul u u)))))))))
    (.mul G
      (.mul u (.mul u (.mul u (.mul u (.mul u (.mul u (.mul u u))))))))

private theorem pTaylor7Step_normal :
    RingNormaliser.normalize pTaylor7StepL =
      RingNormaliser.normalize pTaylor7StepR := by decide

private def pTaylorCancelL : PE :=
  .add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))

private def pTaylorCancelR : PE := .var 1

private theorem pTaylorCancel_normal :
    RingNormaliser.normalize pTaylorCancelL =
      RingNormaliser.normalize pTaylorCancelR := by decide

private theorem taylor6_step_algebra
    (M C B A E F u : Q') :
    (((((((1 : Q') + -(M * u)) + C * (u * u)) +
        -(B * (u * (u * u)))) + A * (u * (u * (u * u)))) +
        -(E * (u * (u * (u * (u * u)))))) +
        F * (u * (u * (u * (u * (u * u)))))) * ((1 : Q') + -u) ≈
      (((((((1 : Q') + -((M + 1) * u)) +
        (C + M) * (u * u)) +
        -((B + C) * (u * (u * u)))) +
        (A + B) * (u * (u * (u * u)))) +
        -((E + A) * (u * (u * (u * (u * u)))))) +
        (F + E) * (u * (u * (u * (u * (u * u)))))) +
        -(F * (u * (u * (u * (u * (u * (u * u))))))) := by
  let rho : Nat → Q' := fun
    | 0 => M | 1 => C | 2 => B | 3 => A | 4 => E | 5 => F | _ => u
  simpa [pTaylor6StepL, pTaylor6StepR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTaylor6StepL pTaylor6StepR pTaylor6Step_normal rho)

private theorem taylor7_step_algebra
    (M C B A E F G u : Q') :
    ((((((((1 : Q') + -(M * u)) + C * (u * u)) +
        -(B * (u * (u * u)))) + A * (u * (u * (u * u)))) +
        -(E * (u * (u * (u * (u * u)))))) +
        F * (u * (u * (u * (u * (u * u)))))) +
        -(G * (u * (u * (u * (u * (u * (u * u)))))))) *
        ((1 : Q') + -u) ≈
      ((((((((1 : Q') + -((M + 1) * u)) +
        (C + M) * (u * u)) +
        -((B + C) * (u * (u * u)))) +
        (A + B) * (u * (u * (u * u)))) +
        -((E + A) * (u * (u * (u * (u * u)))))) +
        (F + E) * (u * (u * (u * (u * (u * u)))))) +
        -((G + F) * (u * (u * (u * (u * (u * (u * u)))))))) +
        G * (u * (u * (u * (u * (u * (u * (u * u))))))) := by
  let rho : Nat → Q' := fun
    | 0 => M | 1 => C | 2 => B | 3 => A | 4 => E | 5 => F | 6 => G | _ => u
  simpa [pTaylor7StepL, pTaylor7StepR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTaylor7StepL pTaylor7StepR pTaylor7Step_normal rho)

private theorem taylor_cancel_algebra (T E : Q') :
    T + -(T + -E) ≈ E := by
  let rho : Nat → Q' := fun | 0 => T | _ => E
  simpa [pTaylorCancelL, pTaylorCancelR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pTaylorCancelL pTaylorCancelR pTaylorCancel_normal rho)

private theorem oneSubTaylor6_step (u : Q') (m : Nat) :
    oneSubTaylor6 u m * ((1 : Q') + -u) ≈
      oneSubTaylor6 u (m + 1) +
        -(Q'.ofNat (sexticCoeff m) *
          (u * (u * (u * (u * (u * (u * u))))))) := by
  let M := Q'.ofNat m
  let C := Q'.ofNat (lowerSixQuadraticCoeff m)
  let B := Q'.ofNat (cubicCoeff m)
  let A := Q'.ofNat (quarticCoeff m)
  let E := Q'.ofNat (quinticCoeff m)
  let F := Q'.ofNat (sexticCoeff m)
  let S := (((((((1 : Q') + -((M + 1) * u)) +
      (C + M) * (u * u)) +
      -((B + C) * (u * (u * u)))) +
      (A + B) * (u * (u * (u * u)))) +
      -((E + A) * (u * (u * (u * (u * u)))))) +
      (F + E) * (u * (u * (u * (u * (u * u))))))
  let G := F * (u * (u * (u * (u * (u * (u * u))))))
  have hm : Q'.ofNat (m + 1) ≈ M + (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv m 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hc : Q'.ofNat (lowerSixQuadraticCoeff (m + 1)) ≈ C + M := by
    rw [lowerSixQuadraticCoeff]
    exact Q'.ofNat_add_eqv _ _
  have hb : Q'.ofNat (cubicCoeff (m + 1)) ≈ B + C := by
    rw [cubicCoeff]
    exact Q'.ofNat_add_eqv _ _
  have ha : Q'.ofNat (quarticCoeff (m + 1)) ≈ A + B := by
    rw [quarticCoeff]
    exact Q'.ofNat_add_eqv _ _
  have he : Q'.ofNat (quinticCoeff (m + 1)) ≈ E + A := by
    rw [quinticCoeff]
    exact Q'.ofNat_add_eqv _ _
  have hf : Q'.ofNat (sexticCoeff (m + 1)) ≈ F + E := by
    rw [sexticCoeff]
    exact Q'.ofNat_add_eqv _ _
  have hsucc : oneSubTaylor6 u (m + 1) ≈ S := by
    unfold oneSubTaylor6 oneSubTaylor5 oneSubTaylor4 oneSubTaylor3
      oneSubTaylor2
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
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
            (u * (u * (u * (u * u)))) he)))
      (Q'.mul_eqv_congr_right _ _
        (u * (u * (u * (u * (u * u))))) hf)
  change (((((((1 : Q') + -(M * u)) + C * (u * u)) +
      -(B * (u * (u * u)))) + A * (u * (u * (u * u)))) +
      -(E * (u * (u * (u * (u * u)))))) +
      F * (u * (u * (u * (u * (u * u)))))) * ((1 : Q') + -u) ≈
        oneSubTaylor6 u (m + 1) + -G
  refine Q'.eqv_trans _ (S + -G) _ ?_ ?_
  · exact taylor6_step_algebra M C B A E F u
  · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsucc)

private theorem oneSubTaylor7_step (u : Q') (m : Nat) :
    oneSubTaylor7 u m * ((1 : Q') + -u) ≈
      oneSubTaylor7 u (m + 1) +
        Q'.ofNat (septicCoeff m) *
          (u * (u * (u * (u * (u * (u * (u * u))))))) := by
  let M := Q'.ofNat m
  let C := Q'.ofNat (lowerSixQuadraticCoeff m)
  let B := Q'.ofNat (cubicCoeff m)
  let A := Q'.ofNat (quarticCoeff m)
  let E := Q'.ofNat (quinticCoeff m)
  let F := Q'.ofNat (sexticCoeff m)
  let G := Q'.ofNat (septicCoeff m)
  let S := ((((((((1 : Q') + -((M + 1) * u)) +
      (C + M) * (u * u)) +
      -((B + C) * (u * (u * u)))) +
      (A + B) * (u * (u * (u * u)))) +
      -((E + A) * (u * (u * (u * (u * u)))))) +
      (F + E) * (u * (u * (u * (u * (u * u)))))) +
      -((G + F) * (u * (u * (u * (u * (u * (u * u))))))))
  let H := G * (u * (u * (u * (u * (u * (u * (u * u)))))))
  have hm : Q'.ofNat (m + 1) ≈ M + (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv m 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hc : Q'.ofNat (lowerSixQuadraticCoeff (m + 1)) ≈ C + M := by
    rw [lowerSixQuadraticCoeff]
    exact Q'.ofNat_add_eqv _ _
  have hb : Q'.ofNat (cubicCoeff (m + 1)) ≈ B + C := by
    rw [cubicCoeff]
    exact Q'.ofNat_add_eqv _ _
  have ha : Q'.ofNat (quarticCoeff (m + 1)) ≈ A + B := by
    rw [quarticCoeff]
    exact Q'.ofNat_add_eqv _ _
  have he : Q'.ofNat (quinticCoeff (m + 1)) ≈ E + A := by
    rw [quinticCoeff]
    exact Q'.ofNat_add_eqv _ _
  have hf : Q'.ofNat (sexticCoeff (m + 1)) ≈ F + E := by
    rw [sexticCoeff]
    exact Q'.ofNat_add_eqv _ _
  have hg : Q'.ofNat (septicCoeff (m + 1)) ≈ G + F := by
    rw [septicCoeff]
    exact Q'.ofNat_add_eqv _ _
  have hsucc : oneSubTaylor7 u (m + 1) ≈ S := by
    unfold oneSubTaylor7 oneSubTaylor6 oneSubTaylor5 oneSubTaylor4
      oneSubTaylor3 oneSubTaylor2
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
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
              (u * (u * (u * (u * u)))) he)))
        (Q'.mul_eqv_congr_right _ _
          (u * (u * (u * (u * (u * u))))) hf))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _
          (u * (u * (u * (u * (u * (u * u)))))) hg))
  change ((((((((1 : Q') + -(M * u)) + C * (u * u)) +
      -(B * (u * (u * u)))) + A * (u * (u * (u * u)))) +
      -(E * (u * (u * (u * (u * u)))))) +
      F * (u * (u * (u * (u * (u * u)))))) +
      -(G * (u * (u * (u * (u * (u * (u * u)))))))) *
        ((1 : Q') + -u) ≈ oneSubTaylor7 u (m + 1) + H
  refine Q'.eqv_trans _ (S + H) _ ?_ ?_
  · exact taylor7_step_algebra M C B A E F G u
  · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsucc)

/-- Public exact recurrence for the seventh alternating Taylor truncation.
This is a stable consumer wrapper around the kernel-checked local algebra
used by `taylor7_le_qpow_oneSub`. -/
theorem oneSubTaylor7_step_eqv (u : Q') (m : Nat) :
    oneSubTaylor7 u m * ((1 : Q') + -u) ≈
      oneSubTaylor7 u (m + 1) +
        Q'.ofNat (septicCoeff m) *
          (u * (u * (u * (u * (u * (u * (u * u))))))) :=
  oneSubTaylor7_step u m

private theorem oneSubTaylor6_zero (u : Q') :
    oneSubTaylor6 u 0 ≈ (1 : Q') := by
  unfold oneSubTaylor6 oneSubTaylor5 oneSubTaylor4 oneSubTaylor3
    oneSubTaylor2 sexticCoeff quinticCoeff quarticCoeff cubicCoeff
    lowerSixQuadraticCoeff
  one_sub_seven_ring

private theorem oneSubTaylor7_zero (u : Q') :
    oneSubTaylor7 u 0 ≈ (1 : Q') := by
  unfold oneSubTaylor7 oneSubTaylor6 oneSubTaylor5 oneSubTaylor4
    oneSubTaylor3 oneSubTaylor2 septicCoeff sexticCoeff quinticCoeff
    quarticCoeff cubicCoeff lowerSixQuadraticCoeff
  one_sub_seven_ring

private theorem seventh_nonnegative {u : Q'} (hu : (0 : Q') ≤ u) :
    (0 : Q') ≤ u * (u * (u * (u * (u * (u * u))))) :=
  Q'.mul_nonneg _ _ hu
    (Q'.mul_nonneg _ _ hu
      (Q'.mul_nonneg _ _ hu
        (Q'.mul_nonneg _ _ hu
          (Q'.mul_nonneg _ _ hu (Q'.mul_nonneg _ _ hu hu)))))

private theorem eighth_nonnegative {u : Q'} (hu : (0 : Q') ≤ u) :
    (0 : Q') ≤ u * (u * (u * (u * (u * (u * (u * u)))))) :=
  Q'.mul_nonneg _ _ hu
    (Q'.mul_nonneg _ _ hu
      (Q'.mul_nonneg _ _ hu
        (Q'.mul_nonneg _ _ hu
          (Q'.mul_nonneg _ _ hu
            (Q'.mul_nonneg _ _ hu (Q'.mul_nonneg _ _ hu hu))))))

/-- Even alternating truncation: `(1-u)^m <= T6`. -/
theorem qpow_oneSub_le_taylor6
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    ∀ m, qpow ((1 : Q') + -u) m ≤ oneSubTaylor6 u m
  | 0 => Q'.le_of_eqv (Q'.eqv_symm (oneSubTaylor6_zero u))
  | m + 1 => by
      let r := (1 : Q') + -u
      let E := Q'.ofNat (sexticCoeff m) *
        (u * (u * (u * (u * (u * (u * u))))))
      have hr0 : (0 : Q') ≤ r := Q'.sub_nonneg_of_le hu1
      have hmul := Q'.mul_le_mul_of_nonneg_right _ _ r
        (qpow_oneSub_le_taylor6 hu0 hu1 m) hr0
      have hstep := oneSubTaylor6_step u m
      have hE0 : (0 : Q') ≤ E :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
          (seventh_nonnegative hu0)
      have hnegE : -E ≤ (0 : Q') := Q'.nonpos_neg_of_nonneg hE0
      have hdrop := Q'.add_le_add_left (oneSubTaylor6 u (m + 1))
        (-E) (0 : Q') hnegE
      have hzero : oneSubTaylor6 u (m + 1) + (0 : Q') ≈
          oneSubTaylor6 u (m + 1) := QPoly.q_add_zero_eqv _
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hstep)
          (Q'.le_trans' _ _ _ hdrop (Q'.le_of_eqv hzero)))

/-- Odd alternating truncation: `T7 <= (1-u)^m`. -/
theorem taylor7_le_qpow_oneSub
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    ∀ m, oneSubTaylor7 u m ≤ qpow ((1 : Q') + -u) m
  | 0 => Q'.le_of_eqv (oneSubTaylor7_zero u)
  | m + 1 => by
      let r := (1 : Q') + -u
      let E := Q'.ofNat (septicCoeff m) *
        (u * (u * (u * (u * (u * (u * (u * u)))))))
      have hr0 : (0 : Q') ≤ r := Q'.sub_nonneg_of_le hu1
      have hmul := Q'.mul_le_mul_of_nonneg_right _ _ r
        (taylor7_le_qpow_oneSub hu0 hu1 m) hr0
      have hstep := oneSubTaylor7_step u m
      have hE0 : (0 : Q') ≤ E :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
          (eighth_nonnegative hu0)
      have hadd := Q'.add_le_self_of_nonneg
        (oneSubTaylor7 u (m + 1)) E hE0
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hstep)) hmul)

/-- The sixth-order overshoot is nonnegative. -/
theorem qpow_oneSub_taylor6_error_nonnegative
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (m : Nat) :
    (0 : Q') ≤ oneSubTaylor6 u m +
      -qpow ((1 : Q') + -u) m :=
  Q'.sub_nonneg_of_le (qpow_oneSub_le_taylor6 hu0 hu1 m)

/-- Sharp constructive seventh-order envelope for the sixth-order
overshoot. -/
theorem qpow_oneSub_taylor6_error_le_septic
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (m : Nat) :
    oneSubTaylor6 u m + -qpow ((1 : Q') + -u) m ≤
      Q'.ofNat (septicCoeff m) *
        (u * (u * (u * (u * (u * (u * u)))))) := by
  let P := qpow ((1 : Q') + -u) m
  let T6 := oneSubTaylor6 u m
  let E := Q'.ofNat (septicCoeff m) *
    (u * (u * (u * (u * (u * (u * u))))))
  have hlower := taylor7_le_qpow_oneSub hu0 hu1 m
  have hneg := Q'.neg_le_neg hlower
  have hadd := Q'.add_le_add_left T6 (-P) (-(oneSubTaylor7 u m)) hneg
  have hright : T6 + -(oneSubTaylor7 u m) ≈ E := by
    unfold oneSubTaylor7
    exact taylor_cancel_algebra _ _
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright)

#print axioms qpow_oneSub_le_taylor6
#print axioms taylor7_le_qpow_oneSub
#print axioms qpow_oneSub_taylor6_error_nonnegative
#print axioms qpow_oneSub_taylor6_error_le_septic
#print axioms oneSubTaylor7_step_eqv

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorSeven
