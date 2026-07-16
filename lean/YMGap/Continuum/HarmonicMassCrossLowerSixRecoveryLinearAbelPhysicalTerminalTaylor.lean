/-
# Fourth-order Taylor sum for the physical terminal carrier prefix

This successor attaches the positive cell-slack block to the analytic
carrier.  The Taylor floor keeps the first Bernoulli term in the favorable
sixth power and the even fourth-order Taylor upper enclosure in the adverse
eighth power.  Its complete prefix has an exact degree-four closed form.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalTerminalPrefix

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalTerminalTaylor

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalPrefixCrossing
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalSplice
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalTerminalPrefix
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPostBootstrap
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelRisingSplice
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem terminal_taylor_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "terminal_taylor_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               terminal_taylor_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul, Int.natCast_add,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def pv (n : Nat) : PE := .var n
private def pa (x y : PE) : PE := .add x y
private def pm (x y : PE) : PE := .mul x y
private def pn (x : PE) : PE := .neg x
private def pp (x : PE) (n : Nat) : PE := .pow x n

private theorem eval_eqv_congr (e : PE) {rho sigma : Nat → Q'}
    (h : ∀ i, rho i ≈ sigma i) :
    RingNormaliser.eval rho e ≈ RingNormaliser.eval sigma e := by
  induction e with
  | const z => exact Q'.eqv_refl _
  | var i => exact h i
  | add a b iha ihb => exact Q'.add_eqv_congr' iha ihb
  | mul a b iha ihb =>
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ iha)
        (Q'.mul_eqv_congr_left _ _ _ ihb)
  | neg a ih => exact Q'.neg_eqv_congr _ _ ih
  | pow a n ih => exact RingNormaliser.qpow_eqv_congr ih n

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

/-! ## Pascal coefficients in falling-factorial form -/

private theorem lowerSixQuadraticCoeff_falling : ∀ m : Nat,
    2 * lowerSixQuadraticCoeff m = m * (m - 1)
  | 0 => rfl
  | m + 1 => by
      rw [lowerSixQuadraticCoeff, Nat.mul_add,
        lowerSixQuadraticCoeff_falling m]
      cases m with
      | zero => rfl
      | succ t =>
          simp only [Nat.add_sub_cancel]
          simp only [Nat.add_mul, Nat.mul_add]
          omega

private theorem cubicCoeff_falling : ∀ m : Nat,
    6 * cubicCoeff m = m * (m - 1) * (m - 2)
  | 0 => rfl
  | m + 1 => by
      rw [cubicCoeff, Nat.mul_add, cubicCoeff_falling m]
      have hq := lowerSixQuadraticCoeff_falling m
      have h6q : 6 * lowerSixQuadraticCoeff m =
          3 * (m * (m - 1)) := by
        calc
          6 * lowerSixQuadraticCoeff m =
              3 * (2 * lowerSixQuadraticCoeff m) := by ac_rfl
          _ = 3 * (m * (m - 1)) := by rw [hq]
      rw [h6q]
      rcases m with _ | _ | t
      · rfl
      · rfl
      · have h20 : t + 1 + 1 - 2 = t := by omega
        have h31 : t + 1 + 1 + 1 - 2 = t + 1 := by omega
        have h11 : t + 1 + 1 - 1 = t + 1 := by omega
        have h21 : t + 1 + 1 + 1 - 1 = t + 1 + 1 := by omega
        rw [h20, h31, h11, h21]
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega

private theorem quarticCoeff_falling : ∀ m : Nat,
    24 * quarticCoeff m = m * (m - 1) * (m - 2) * (m - 3)
  | 0 => rfl
  | m + 1 => by
      rw [quarticCoeff, Nat.mul_add, quarticCoeff_falling m]
      have hc := cubicCoeff_falling m
      have h24c : 24 * cubicCoeff m =
          4 * (m * (m - 1) * (m - 2)) := by
        calc
          24 * cubicCoeff m = 4 * (6 * cubicCoeff m) := by ac_rfl
          _ = 4 * (m * (m - 1) * (m - 2)) := by rw [hc]
      rw [h24c]
      rcases m with _ | _ | _ | t
      · rfl
      · rfl
      · rfl
      · have h31 : t + 1 + 1 + 1 - 3 = t := by omega
        have h42 : t + 1 + 1 + 1 + 1 - 3 = t + 1 := by omega
        have h21 : t + 1 + 1 + 1 - 2 = t + 1 := by omega
        have h32 : t + 1 + 1 + 1 + 1 - 2 = t + 1 + 1 := by omega
        have h11 : t + 1 + 1 + 1 - 1 = t + 1 + 1 := by omega
        have h21' : t + 1 + 1 + 1 + 1 - 1 =
            t + 1 + 1 + 1 := by omega
        rw [h31, h42, h21, h32, h11, h21']
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega

private theorem ofNat_sub_eqv_local (a b : Nat) (h : b ≤ a) :
    Q'.ofNat a + -(Q'.ofNat b) ≈ Q'.ofNat (a - b) := by
  change (Int.ofNat a * 1 + (-Int.ofNat b) * 1) * 1 =
    Int.ofNat (a - b) * 1
  simp only [Int.mul_one]
  simpa [Int.sub_eq_add_neg] using (Int.ofNat_sub h).symm

private theorem quadraticCoeff_scaled_cast {m : Nat} (hm : 1 ≤ m) :
    Q'.ofNat 24 * Q'.ofNat (lowerSixQuadraticCoeff m) ≈
      Q'.ofNat 12 *
        (Q'.ofNat m * (Q'.ofNat m + -(1 : Q'))) := by
  have hq := lowerSixQuadraticCoeff_falling m
  have hnat : 24 * lowerSixQuadraticCoeff m =
      12 * (m * (m - 1)) := by
    calc
      24 * lowerSixQuadraticCoeff m =
          12 * (2 * lowerSixQuadraticCoeff m) := by ac_rfl
      _ = 12 * (m * (m - 1)) := by rw [hq]
  have hsub : Q'.ofNat (m - 1) ≈
      Q'.ofNat m + -(1 : Q') := by
    refine Q'.eqv_trans _ (Q'.ofNat m + -Q'.ofNat 1) _ ?_ ?_
    · exact Q'.eqv_symm (ofNat_sub_eqv_local m 1 hm)
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (by decide))
  refine Q'.eqv_trans _ (Q'.ofNat (24 * lowerSixQuadraticCoeff m)) _
    (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv _ _)) ?_
  rw [hnat]
  refine Q'.eqv_trans _
    (Q'.ofNat 12 * Q'.ofNat (m * (m - 1))) _
    (HeatKernelRGStep.ofNat_mul_eqv _ _) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  exact Q'.eqv_trans _ _ _
    (HeatKernelRGStep.ofNat_mul_eqv _ _)
    (Q'.mul_eqv_congr_left _ _ _ hsub)

private theorem cubicCoeff_scaled_cast {m : Nat} (hm : 2 ≤ m) :
    Q'.ofNat 24 * Q'.ofNat (cubicCoeff m) ≈
      Q'.ofNat 4 *
        ((Q'.ofNat m * (Q'.ofNat m + -(1 : Q'))) *
          (Q'.ofNat m + -(Q'.ofNat 2))) := by
  have hc := cubicCoeff_falling m
  have hnat : 24 * cubicCoeff m =
      4 * (m * (m - 1) * (m - 2)) := by
    calc
      24 * cubicCoeff m = 4 * (6 * cubicCoeff m) := by ac_rfl
      _ = 4 * (m * (m - 1) * (m - 2)) := by rw [hc]
  have hsub1 : Q'.ofNat (m - 1) ≈
      Q'.ofNat m + -(1 : Q') := by
    refine Q'.eqv_trans _ (Q'.ofNat m + -Q'.ofNat 1) _ ?_ ?_
    · exact Q'.eqv_symm (ofNat_sub_eqv_local m 1 (by omega))
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (by decide))
  have hsub2 : Q'.ofNat (m - 2) ≈
      Q'.ofNat m + -(Q'.ofNat 2) :=
    Q'.eqv_symm (ofNat_sub_eqv_local m 2 hm)
  refine Q'.eqv_trans _ (Q'.ofNat (24 * cubicCoeff m)) _
    (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv _ _)) ?_
  rw [hnat]
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * Q'.ofNat (m * (m - 1) * (m - 2))) _
    (HeatKernelRGStep.ofNat_mul_eqv _ _) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (m * (m - 1)) * Q'.ofNat (m - 2)) _
    (HeatKernelRGStep.ofNat_mul_eqv _ _) ?_
  let A := Q'.ofNat m * (Q'.ofNat m + -(1 : Q'))
  have hA : Q'.ofNat (m * (m - 1)) ≈ A :=
    Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv _ _)
      (Q'.mul_eqv_congr_left _ _ _ hsub1)
  refine Q'.eqv_trans _ (A * Q'.ofNat (m - 2)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hA
  · exact Q'.mul_eqv_congr_left _ _ _ hsub2

private theorem quarticCoeff_scaled_cast {m : Nat} (hm : 3 ≤ m) :
    Q'.ofNat 24 * Q'.ofNat (quarticCoeff m) ≈
      (((Q'.ofNat m * (Q'.ofNat m + -(1 : Q'))) *
          (Q'.ofNat m + -(Q'.ofNat 2))) *
        (Q'.ofNat m + -(Q'.ofNat 3))) := by
  have hc := quarticCoeff_falling m
  have hsub1 : Q'.ofNat (m - 1) ≈
      Q'.ofNat m + -(1 : Q') := by
    refine Q'.eqv_trans _ (Q'.ofNat m + -Q'.ofNat 1) _ ?_ ?_
    · exact Q'.eqv_symm (ofNat_sub_eqv_local m 1 (by omega))
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (by decide))
  have hsub2 : Q'.ofNat (m - 2) ≈
      Q'.ofNat m + -(Q'.ofNat 2) :=
    Q'.eqv_symm (ofNat_sub_eqv_local m 2 (by omega))
  have hsub3 : Q'.ofNat (m - 3) ≈
      Q'.ofNat m + -(Q'.ofNat 3) :=
    Q'.eqv_symm (ofNat_sub_eqv_local m 3 hm)
  refine Q'.eqv_trans _ (Q'.ofNat (24 * quarticCoeff m)) _
    (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv _ _)) ?_
  rw [hc]
  refine Q'.eqv_trans _
    (Q'.ofNat (m * (m - 1) * (m - 2)) * Q'.ofNat (m - 3)) _
    (HeatKernelRGStep.ofNat_mul_eqv _ _) ?_
  let A := (Q'.ofNat m * (Q'.ofNat m + -(1 : Q'))) *
    (Q'.ofNat m + -(Q'.ofNat 2))
  have hA : Q'.ofNat (m * (m - 1) * (m - 2)) ≈ A := by
    refine Q'.eqv_trans _
      (Q'.ofNat (m * (m - 1)) * Q'.ofNat (m - 2)) _
      (HeatKernelRGStep.ofNat_mul_eqv _ _) ?_
    let B := Q'.ofNat m * (Q'.ofNat m + -(1 : Q'))
    have hB : Q'.ofNat (m * (m - 1)) ≈ B :=
      Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv _ _)
        (Q'.mul_eqv_congr_left _ _ _ hsub1)
    refine Q'.eqv_trans _ (B * Q'.ofNat (m - 2)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hB
    · exact Q'.mul_eqv_congr_left _ _ _ hsub2
  refine Q'.eqv_trans _ (A * Q'.ofNat (m - 3)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hA
  · exact Q'.mul_eqv_congr_left _ _ _ hsub3

/-! ## Exact scaled mode and prefix polynomials -/

private def pTerminalTaylor4ScaledAt (b u : PE) : PE :=
  let b1 := pa b (pc (-1))
  let b2 := pa b (pc (-2))
  let b3 := pa b (pc (-3))
  pa (pa (pa (pa
    (pc 24)
    (pm (pm (pc (-24)) b) u))
    (pm (pm (pm (pc 12) b) b1) (pp u 2)))
    (pm (pm (pm (pm (pc (-4)) b) b1) b2) (pp u 3)))
    (pm (pm (pm (pm b b1) b2) b3) (pp u 4))

private def pTerminalTaylor4RecursiveScaled : PE :=
  let M := pv 0
  let Q := pv 1
  let B := pv 2
  let A := pv 3
  let u := pv 4
  let u2 := pm u u
  let u3 := pm u u2
  let u4 := pm u u3
  pm (pc 24)
    (pa (pa
      (pa (pa (pc 1) (pn (pm M u))) (pm Q u2))
      (pn (pm B u3)))
      (pm A u4))

private def pTerminalTaylor4CoefficientScaledAt
    (M C2 C3 C4 u : PE) : PE :=
  pa (pa (pa (pa
    (pc 24)
    (pn (pm (pm (pc 24) M) u)))
    (pm C2 (pp u 2)))
    (pn (pm C3 (pp u 3))))
    (pm C4 (pp u 4))

private def pTerminalTaylor4CoefficientScaled : PE :=
  pTerminalTaylor4CoefficientScaledAt
    (pv 0) (pm (pc 24) (pv 1)) (pm (pc 24) (pv 2))
      (pm (pc 24) (pv 3)) (pv 4)

private def pTerminalTaylor4CoefficientVariables : PE :=
  pTerminalTaylor4CoefficientScaledAt
    (pv 0) (pv 1) (pv 2) (pv 3) (pv 4)

private theorem pTerminalTaylor4_coefficient_normal :
    RingNormaliser.normalize pTerminalTaylor4RecursiveScaled =
      RingNormaliser.normalize pTerminalTaylor4CoefficientScaled := by
  decide

private def pTerminalTaylor4FallingScaled : PE :=
  let M := pv 0
  let u := pv 1
  let M1 := pa M (pc (-1))
  let M2 := pa M (pc (-2))
  let M3 := pa M (pc (-3))
  pTerminalTaylor4CoefficientScaledAt M
    (pm (pm (pc 12) M) M1)
    (pm (pm (pm (pc 4) M) M1) M2)
    (pm (pm (pm M M1) M2) M3) u

private def pTerminalTaylor4FallingInput : PE :=
  let M := pv 0
  let u := pv 1
  let M1 := pa M (pc (-1))
  let M2 := pa M (pc (-2))
  let M3 := pa M (pc (-3))
  pTerminalTaylor4CoefficientScaledAt M
    (pm (pc 12) (pm M M1))
    (pm (pc 4) ((pm (pm M M1) M2)))
    (pm (pm (pm M M1) M2) M3) u

private theorem pTerminalTaylor4_falling_input_normal :
    RingNormaliser.normalize pTerminalTaylor4FallingInput =
      RingNormaliser.normalize pTerminalTaylor4FallingScaled := by
  decide

private theorem pTerminalTaylor4_falling_normal :
    RingNormaliser.normalize pTerminalTaylor4FallingScaled =
      RingNormaliser.normalize
        (pTerminalTaylor4ScaledAt (pv 0) (pv 1)) := by
  decide

private theorem terminalTaylor4_scaled_eqv
    {u : Q'} {m : Nat} (hm : 3 ≤ m) :
    Q'.ofNat 24 * oneSubTaylor4 u m ≈
      RingNormaliser.eval
        (fun | 0 => Q'.ofNat m | _ => u)
        (pTerminalTaylor4ScaledAt (pv 0) (pv 1)) := by
  let M := Q'.ofNat m
  let Q := Q'.ofNat (lowerSixQuadraticCoeff m)
  let B := Q'.ofNat (cubicCoeff m)
  let A := Q'.ofNat (quarticCoeff m)
  have hraw : Q'.ofNat 24 * oneSubTaylor4 u m ≈
      RingNormaliser.eval
        (fun | 0 => M | 1 => Q | 2 => B | 3 => A | _ => u)
        pTerminalTaylor4RecursiveScaled := by
    unfold oneSubTaylor4 oneSubTaylor3 oneSubTaylor2
    simp only [pTerminalTaylor4RecursiveScaled, pc, pv, pa, pm, pn,
      RingNormaliser.eval]
    exact Q'.eqv_refl _
  have hcoeff :
      RingNormaliser.eval
          (fun | 0 => M | 1 => Q | 2 => B | 3 => A | _ => u)
          pTerminalTaylor4RecursiveScaled ≈
        RingNormaliser.eval
          (fun | 0 => M | 1 => Q | 2 => B | 3 => A | _ => u)
          pTerminalTaylor4CoefficientScaled :=
    RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalTaylor4_coefficient_normal _
  let C2 := Q'.ofNat 12 * (M * (M + -(1 : Q')))
  let C3 := Q'.ofNat 4 * ((M * (M + -(1 : Q'))) *
    (M + -(Q'.ofNat 2)))
  let C4 := ((M * (M + -(1 : Q'))) *
    (M + -(Q'.ofNat 2))) * (M + -(Q'.ofNat 3))
  have hC2 : Q'.ofNat 24 * Q ≈ C2 := by
    dsimp only [Q, C2, M]
    exact quadraticCoeff_scaled_cast (by omega)
  have hC3 : Q'.ofNat 24 * B ≈ C3 := by
    dsimp only [B, C3, M]
    exact cubicCoeff_scaled_cast (by omega)
  have hC4 : Q'.ofNat 24 * A ≈ C4 := by
    dsimp only [A, C4, M]
    exact quarticCoeff_scaled_cast hm
  have hreplace :
      RingNormaliser.eval
          (fun | 0 => M | 1 => Q | 2 => B | 3 => A | _ => u)
          pTerminalTaylor4CoefficientScaled ≈
        RingNormaliser.eval
          (fun | 0 => M | 1 => C2 | 2 => C3 | 3 => C4 | _ => u)
          (pTerminalTaylor4CoefficientScaledAt
            (pv 0) (pv 1) (pv 2) (pv 3) (pv 4)) := by
    change RingNormaliser.eval
        (fun | 0 => M | 1 => Q'.ofNat 24 * Q |
          2 => Q'.ofNat 24 * B | 3 => Q'.ofNat 24 * A | _ => u)
        pTerminalTaylor4CoefficientVariables ≈
      RingNormaliser.eval
        (fun | 0 => M | 1 => C2 | 2 => C3 | 3 => C4 | _ => u)
        pTerminalTaylor4CoefficientVariables
    apply eval_eqv_congr pTerminalTaylor4CoefficientVariables
    intro i
    rcases i with _ | _ | _ | _ | i
    · exact Q'.eqv_refl _
    · exact hC2
    · exact hC3
    · exact hC4
    · exact Q'.eqv_refl _
  have hfall :
      RingNormaliser.eval
          (fun | 0 => M | 1 => C2 | 2 => C3 | 3 => C4 | _ => u)
          (pTerminalTaylor4CoefficientScaledAt
            (pv 0) (pv 1) (pv 2) (pv 3) (pv 4)) ≈
        RingNormaliser.eval (fun | 0 => M | _ => u)
          pTerminalTaylor4FallingScaled := by
    change RingNormaliser.eval (fun | 0 => M | _ => u)
        pTerminalTaylor4FallingInput ≈
      RingNormaliser.eval (fun | 0 => M | _ => u)
        pTerminalTaylor4FallingScaled
    exact RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalTaylor4_falling_input_normal _
  have htarget :
      RingNormaliser.eval (fun | 0 => M | _ => u)
          pTerminalTaylor4FallingScaled ≈
        RingNormaliser.eval (fun | 0 => M | _ => u)
          (pTerminalTaylor4ScaledAt (pv 0) (pv 1)) :=
    RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalTaylor4_falling_normal _
  dsimp only [M] at htarget ⊢
  exact Q'.eqv_trans _ _ _ hraw
    (Q'.eqv_trans _ _ _ hcoeff
      (Q'.eqv_trans _ _ _ hreplace
        (Q'.eqv_trans _ _ _ hfall htarget)))

private def pTerminalTaylorModeScaledAt (x u : PE) : PE :=
  let n := pa x (pc 1)
  let n1 := pa x (pc 2)
  let a := pm (pc 6) x
  let b := pa (pm (pc 8) x) (pc 3)
  let positive := pm (pm (pm (pp n 2)
    (pa (pc 8) (pm (pc (-13)) u))) (pc 24))
      (pa (pc 1) (pn (pm a u)))
  let adverse := pm (pm (pm (pc 8) n) n1)
    (pTerminalTaylor4ScaledAt b u)
  pm (pc 210) (pa positive (pn adverse))

private def pTerminalTaylorModeCoordinateAt
    (n n1 a T u : PE) : PE :=
  let positive := pm (pm (pm (pm n n)
    (pa (pc 8) (pm (pc (-13)) u))) (pc 24))
      (pa (pc 1) (pn (pm a u)))
  let adverse := pm (pm (pm (pc 8) n) n1) T
  pm (pc 210) (pa positive (pn adverse))

private def pTerminalTaylorModeRawAt
    (n n1 a T u : PE) : PE :=
  let positive := pm (pm (pm n n)
    (pa (pc 8) (pn (pm (pc 13) u))))
      (pa (pc 1) (pn (pm a u)))
  let adverse := pm (pm (pc 8) (pm n n1)) T
  pm (pc 5040) (pa positive (pn adverse))

private def pTerminalTaylorModeRaw : PE :=
  pTerminalTaylorModeRawAt
    (pv 0) (pv 1) (pv 2) (pv 3) (pv 4)

private def pTerminalTaylorModeCoordinateTwentyFour : PE :=
  pTerminalTaylorModeCoordinateAt
    (pv 0) (pv 1) (pv 2) (pm (pc 24) (pv 3)) (pv 4)

private theorem pTerminalTaylorMode_raw_normal :
    RingNormaliser.normalize pTerminalTaylorModeRaw =
      RingNormaliser.normalize
        pTerminalTaylorModeCoordinateTwentyFour := by
  decide

private def pTerminalTaylorModeCoordinate : PE :=
  pTerminalTaylorModeCoordinateAt
    (pv 0) (pv 1) (pv 2) (pv 3) (pv 4)

private def pTerminalTaylorModeExpandedAt
    (n n1 a b u : PE) : PE :=
  pTerminalTaylorModeCoordinateAt n n1 a
    (pTerminalTaylor4ScaledAt b u) u

private def pTerminalTaylorModeExpanded : PE :=
  pTerminalTaylorModeExpandedAt
    (pv 0) (pv 1) (pv 2) (pv 3) (pv 4)

private def pTerminalTaylorModeSubstituted : PE :=
  let x := pv 0
  let u := pv 1
  pTerminalTaylorModeExpandedAt
    (pa x (pc 1)) (pa x (pc 2)) (pm (pc 6) x)
      (pa (pm (pc 8) x) (pc 3)) u

private theorem pTerminalTaylorMode_substituted_normal :
    RingNormaliser.normalize pTerminalTaylorModeSubstituted =
      RingNormaliser.normalize
        (pTerminalTaylorModeScaledAt (pv 0) (pv 1)) := by
  decide

private def pTerminalTaylorPrefixScaledAt (N u : PE) : PE :=
  let N1 := pa N (pc 1)
  let N2 := pa N (pc 2)
  let common := pm N N1
  let p1 := pa (pa
    (pm (pc 24) (pp N 2))
    (pm (pc 142) N)) (pc (-61))
  let p2 := pa (pa (pa
    (pm (pc 512) (pp N 3))
    (pm (pc 333) (pp N 2)))
    (pm (pc (-863)) N)) (pc 258)
  let p3 := pa (pa (pa
    (pm (pc 128) (pp N 3))
    (pm (pc (-192)) (pp N 2)))
    (pm (pc 49) N)) (pc 18)
  let p4 := pa (pa (pa
    (pm (pc 5120) (pp N 3))
    (pm (pc (-5760)) (pp N 2)))
    (pm (pc (-944)) N)) (pc 1293)
  pa (pa (pa (pa
    (pm (pm (pc (-20160)) common) (pc 1))
    (pm (pm (pm (pc 840) common) p1) u))
    (pm (pm (pm (pc (-504)) common) p2) (pp u 2)))
    (pm (pm (pm (pm (pc 4480) common) N2) p3) (pp u 3)))
    (pm (pm (pm (pm (pm (pm (pc (-192)) N)
      (pa N (pc (-1)))) N1) N2) p4) (pp u 4))

private def pTerminalTaylorModeScaled : PE :=
  pTerminalTaylorModeScaledAt (pv 0) (pv 1)

private def pTerminalTaylorPrefixScaled : PE :=
  pTerminalTaylorPrefixScaledAt (pv 0) (pv 1)

private def pTerminalTaylorPrefixStepL : PE :=
  pTerminalTaylorPrefixScaledAt (pa (pv 0) (pc 1)) (pv 1)

private def pTerminalTaylorPrefixStepR : PE :=
  pa pTerminalTaylorPrefixScaled pTerminalTaylorModeScaled

private theorem pTerminalTaylorPrefix_step_normal :
    RingNormaliser.normalize pTerminalTaylorPrefixStepL =
      RingNormaliser.normalize pTerminalTaylorPrefixStepR := by
  decide

private def pTerminalTaylorPrefixBase : PE :=
  pTerminalTaylorPrefixScaledAt (pc 0) (pv 0)

private theorem pTerminalTaylorPrefix_base_normal :
    RingNormaliser.normalize pTerminalTaylorPrefixBase =
      RingNormaliser.normalize (pc 0) := by
  decide

/-- The analytic per-mode floor before multiplying by `5040`. -/
def lowerSixRecoveryTerminalTaylorMode (u : Q') (j : Nat) : Q' :=
  let n := Q'.ofNat (j + 1)
  let n1 := Q'.ofNat (j + 2)
  let a := Q'.ofNat (6 * j)
  ((n * n) * (Q'.ofNat 8 + -(Q'.ofNat 13 * u))) *
      ((1 : Q') + -(a * u)) +
    -(Q'.ofNat 8 * (n * n1) * oneSubTaylor4 u (8 * j + 3))

/-- The exact degree-four closed form for the `5040`-scaled Taylor prefix. -/
def lowerSixRecoveryTerminalTaylorPrefixPolynomial (N : Nat) (u : Q') : Q' :=
  RingNormaliser.eval
    (fun | 0 => Q'.ofNat N | _ => u) pTerminalTaylorPrefixScaled

private theorem terminalTaylorMode_scaled_eqv_poly (u : Q') (j : Nat) :
    Q'.ofNat 5040 * lowerSixRecoveryTerminalTaylorMode u j ≈
      RingNormaliser.eval
        (fun | 0 => Q'.ofNat j | _ => u) pTerminalTaylorModeScaled := by
  let n := Q'.ofNat (j + 1)
  let n1 := Q'.ofNat (j + 2)
  let a := Q'.ofNat (6 * j)
  let b := Q'.ofNat (8 * j + 3)
  let T := oneSubTaylor4 u (8 * j + 3)
  let S := RingNormaliser.eval
    (fun | 0 => b | _ => u)
    (pTerminalTaylor4ScaledAt (pv 0) (pv 1))
  have hraw :
      Q'.ofNat 5040 * lowerSixRecoveryTerminalTaylorMode u j ≈
        RingNormaliser.eval
          (fun | 0 => n | 1 => n1 | 2 => a |
            3 => Q'.ofNat 24 * T | _ => u)
          pTerminalTaylorModeCoordinate := by
    have hpoly := RingNormaliser.poly_identity_of_normal_eq
      pTerminalTaylorModeRaw pTerminalTaylorModeCoordinateTwentyFour
      pTerminalTaylorMode_raw_normal
      (fun | 0 => n | 1 => n1 | 2 => a | 3 => T | _ => u)
    simpa [lowerSixRecoveryTerminalTaylorMode,
      pTerminalTaylorModeRaw, pTerminalTaylorModeRawAt,
      pTerminalTaylorModeCoordinateTwentyFour,
      pTerminalTaylorModeCoordinate,
      pTerminalTaylorModeCoordinateAt, pc, pv, pa, pm, pn,
      RingNormaliser.eval, n, n1, a, T] using hpoly
  have hT : Q'.ofNat 24 * T ≈ S := by
    dsimp only [T, S, b]
    exact terminalTaylor4_scaled_eqv (by omega)
  have hreplace :
      RingNormaliser.eval
          (fun | 0 => n | 1 => n1 | 2 => a |
            3 => Q'.ofNat 24 * T | _ => u)
          pTerminalTaylorModeCoordinate ≈
        RingNormaliser.eval
          (fun | 0 => n | 1 => n1 | 2 => a | 3 => S | _ => u)
          pTerminalTaylorModeCoordinate := by
    apply eval_eqv_congr pTerminalTaylorModeCoordinate
    intro i
    rcases i with _ | _ | _ | _ | i
    · exact Q'.eqv_refl _
    · exact Q'.eqv_refl _
    · exact Q'.eqv_refl _
    · exact hT
    · exact Q'.eqv_refl _
  have hexpand :
      RingNormaliser.eval
          (fun | 0 => n | 1 => n1 | 2 => a | 3 => S | _ => u)
          pTerminalTaylorModeCoordinate ≈
        RingNormaliser.eval
          (fun | 0 => n | 1 => n1 | 2 => a | 3 => b | _ => u)
          pTerminalTaylorModeExpanded := by
    dsimp only [S]
    exact Q'.eqv_refl _
  let J := Q'.ofNat j
  have hn : n ≈ J + (1 : Q') := by
    dsimp only [n, J]
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv j 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hn1 : n1 ≈ J + Q'.ofNat 2 := by
    dsimp only [n1, J]
    exact Q'.ofNat_add_eqv j 2
  have ha : a ≈ Q'.ofNat 6 * J := by
    dsimp only [a, J]
    exact HeatKernelRGStep.ofNat_mul_eqv 6 j
  have hb : b ≈ Q'.ofNat 8 * J + Q'.ofNat 3 := by
    dsimp only [b, J]
    exact Q'.eqv_trans _
      (Q'.ofNat (8 * j) + Q'.ofNat 3) _
      (Q'.ofNat_add_eqv (8 * j) 3)
      (Q'.add_eqv_congr_right _ _ _
        (HeatKernelRGStep.ofNat_mul_eqv 8 j))
  have hcoords :
      RingNormaliser.eval
          (fun | 0 => n | 1 => n1 | 2 => a | 3 => b | _ => u)
          pTerminalTaylorModeExpanded ≈
        RingNormaliser.eval
          (fun | 0 => J + (1 : Q') | 1 => J + Q'.ofNat 2 |
            2 => Q'.ofNat 6 * J |
            3 => Q'.ofNat 8 * J + Q'.ofNat 3 | _ => u)
          pTerminalTaylorModeExpanded := by
    apply eval_eqv_congr pTerminalTaylorModeExpanded
    intro i
    rcases i with _ | _ | _ | _ | i
    · exact hn
    · exact hn1
    · exact ha
    · exact hb
    · exact Q'.eqv_refl _
  have hsubstitute :
      RingNormaliser.eval
          (fun | 0 => J + (1 : Q') | 1 => J + Q'.ofNat 2 |
            2 => Q'.ofNat 6 * J |
            3 => Q'.ofNat 8 * J + Q'.ofNat 3 | _ => u)
          pTerminalTaylorModeExpanded ≈
        RingNormaliser.eval (fun | 0 => J | _ => u)
          pTerminalTaylorModeSubstituted := by
    exact Q'.eqv_refl _
  have hnormal :
      RingNormaliser.eval (fun | 0 => J | _ => u)
          pTerminalTaylorModeSubstituted ≈
        RingNormaliser.eval (fun | 0 => J | _ => u)
          pTerminalTaylorModeScaled :=
    RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalTaylorMode_substituted_normal _
  dsimp only [J] at hnormal ⊢
  exact Q'.eqv_trans _ _ _ hraw
    (Q'.eqv_trans _ _ _ hreplace
      (Q'.eqv_trans _ _ _ hexpand
        (Q'.eqv_trans _ _ _ hcoords
          (Q'.eqv_trans _ _ _ hsubstitute hnormal))))

private theorem terminalTaylorPrefix_step_algebra (N u : Q') :
    RingNormaliser.eval (fun | 0 => N + (1 : Q') | _ => u)
        pTerminalTaylorPrefixScaled ≈
      RingNormaliser.eval (fun | 0 => N | _ => u)
          pTerminalTaylorPrefixScaled +
        RingNormaliser.eval (fun | 0 => N | _ => u)
          pTerminalTaylorModeScaled := by
  simpa [pTerminalTaylorPrefixStepL, pTerminalTaylorPrefixStepR,
    pTerminalTaylorPrefixScaled, pTerminalTaylorModeScaled,
    pTerminalTaylorPrefixScaledAt, pTerminalTaylorModeScaledAt,
    pTerminalTaylor4ScaledAt, pc, pv, pa, pm, pn, pp,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalTaylorPrefix_step_normal (fun | 0 => N | _ => u))

/-- Exact summation of the Taylor floor.  All denominators are cleared by
the fixed positive integer `5040`; the right side is the closed degree-four
prefix polynomial. -/
theorem lowerSixRecoveryTerminalTaylorFinSum_scaled_eqv_prefix
    (u : Q') : ∀ N : Nat,
    Q'.ofNat 5040 *
        finSum (fun j => lowerSixRecoveryTerminalTaylorMode u j) N ≈
      lowerSixRecoveryTerminalTaylorPrefixPolynomial N u
  | 0 => by
      have hb : RingNormaliser.eval (fun _ => u)
          pTerminalTaylorPrefixBase ≈ (0 : Q') :=
        RingNormaliser.poly_identity_of_normal_eq _ _
          pTerminalTaylorPrefix_base_normal _
      unfold lowerSixRecoveryTerminalTaylorPrefixPolynomial finSum
      refine Q'.eqv_trans _ (0 : Q') _ (Q'.mul_zero_eqv _) ?_
      exact Q'.eqv_symm (by
        simpa [pTerminalTaylorPrefixBase,
          pTerminalTaylorPrefixScaled, pc, pv,
          RingNormaliser.eval] using hb)
  | N + 1 => by
      rw [finSum_succ]
      have ih := lowerSixRecoveryTerminalTaylorFinSum_scaled_eqv_prefix u N
      have hm := terminalTaylorMode_scaled_eqv_poly u N
      have hsum :
          Q'.ofNat 5040 *
              (finSum (fun j => lowerSixRecoveryTerminalTaylorMode u j) N +
                lowerSixRecoveryTerminalTaylorMode u N) ≈
            lowerSixRecoveryTerminalTaylorPrefixPolynomial N u +
              RingNormaliser.eval
                (fun | 0 => Q'.ofNat N | _ => u)
                pTerminalTaylorModeScaled := by
        refine Q'.eqv_trans _
          (Q'.ofNat 5040 *
              finSum (fun j => lowerSixRecoveryTerminalTaylorMode u j) N +
            Q'.ofNat 5040 * lowerSixRecoveryTerminalTaylorMode u N) _
          (Q'.mul_add_eqv _ _ _) ?_
        exact Q'.add_eqv_congr' ih hm
      have hcast : Q'.ofNat (N + 1) ≈
          Q'.ofNat N + (1 : Q') := by
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv N 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      have hleft :
          lowerSixRecoveryTerminalTaylorPrefixPolynomial (N + 1) u ≈
            RingNormaliser.eval
              (fun | 0 => Q'.ofNat N + (1 : Q') | _ => u)
              pTerminalTaylorPrefixScaled := by
        unfold lowerSixRecoveryTerminalTaylorPrefixPolynomial
        apply eval_eqv_congr pTerminalTaylorPrefixScaled
        intro i
        rcases i with _ | i
        · exact hcast
        · exact Q'.eqv_refl _
      have hstep := terminalTaylorPrefix_step_algebra (Q'.ofNat N) u
      have htarget :
          lowerSixRecoveryTerminalTaylorPrefixPolynomial (N + 1) u ≈
            lowerSixRecoveryTerminalTaylorPrefixPolynomial N u +
              RingNormaliser.eval
                (fun | 0 => Q'.ofNat N | _ => u)
                pTerminalTaylorModeScaled := by
        exact Q'.eqv_trans _ _ _ hleft (by
          unfold lowerSixRecoveryTerminalTaylorPrefixPolynomial
          exact hstep)
      exact Q'.eqv_trans _ _ _ hsum (Q'.eqv_symm htarget)

/-! ## Harmonic and within-cell clearing -/

private def pTerminalTaylorP1At (N : PE) : PE :=
  pa (pa (pm (pc 24) (pp N 2)) (pm (pc 142) N)) (pc (-61))

private def pTerminalTaylorP2At (N : PE) : PE :=
  pa (pa (pa (pm (pc 512) (pp N 3))
    (pm (pc 333) (pp N 2))) (pm (pc (-863)) N)) (pc 258)

private def pTerminalTaylorP3At (N : PE) : PE :=
  pa (pa (pa (pm (pc 128) (pp N 3))
    (pm (pc (-192)) (pp N 2))) (pm (pc 49) N)) (pc 18)

private def pTerminalTaylorP4At (N : PE) : PE :=
  pa (pa (pa (pm (pc 5120) (pp N 3))
    (pm (pc (-5760)) (pp N 2))) (pm (pc (-944)) N)) (pc 1293)

private def pTerminalTaylorPrefixClearedAt (N D T : PE) : PE :=
  let N1 := pa N (pc 1)
  let N2 := pa N (pc 2)
  let common := pm N N1
  pa (pa (pa (pa
    (pm (pm (pc (-20160)) common) (pp D 4))
    (pm (pm (pm (pm (pc 840) common)
      (pTerminalTaylorP1At N)) (pp D 3)) T))
    (pm (pm (pm (pm (pc (-504)) common)
      (pTerminalTaylorP2At N)) (pp D 2)) (pp T 2)))
    (pm (pm (pm (pm (pm (pc 4480) common) N2)
      (pTerminalTaylorP3At N)) D) (pp T 3)))
    (pm (pm (pm (pm (pm (pm (pc (-192)) N)
      (pa N (pc (-1)))) N1) N2) (pTerminalTaylorP4At N))
      (pp T 4))

private def pTerminalTaylorPrefixCleared : PE :=
  pTerminalTaylorPrefixClearedAt (pv 0) (pv 1) (pv 2)

private def pTerminalTaylorPrefixClearL : PE :=
  let N := pv 0
  let u := pv 1
  let D := pv 2
  pm (pp D 4) (pTerminalTaylorPrefixScaledAt N u)

private def pTerminalTaylorPrefixClearR : PE :=
  let N := pv 0
  let u := pv 1
  let D := pv 2
  pTerminalTaylorPrefixClearedAt N D (pm u D)

private theorem pTerminalTaylorPrefix_clear_normal :
    RingNormaliser.normalize pTerminalTaylorPrefixClearL =
      RingNormaliser.normalize pTerminalTaylorPrefixClearR := by
  decide

private def pTerminalTaylorDoubledAt (c Y : PE) : PE :=
  let N := pa c (pc 1)
  let N1 := pa N (pc 1)
  let N2 := pa N (pc 2)
  let common := pm N N1
  pa (pa (pa (pa
    (pm (pm (pc (-20160)) common) (pp Y 4))
    (pm (pm (pm (pc 1680) common)
      (pTerminalTaylorP1At N)) (pp Y 3)))
    (pm (pm (pm (pc (-2016)) common)
      (pTerminalTaylorP2At N)) (pp Y 2)))
    (pm (pm (pm (pm (pc 35840) common) N2)
      (pTerminalTaylorP3At N)) Y))
    (pm (pm (pm (pm (pm (pc (-3072)) N)
      (pa N (pc (-1)))) N1) N2) (pTerminalTaylorP4At N))

private def pTerminalTaylorDoubled : PE :=
  pTerminalTaylorDoubledAt (pv 0) (pv 1)

private def pTerminalTaylorDoubleL : PE :=
  let c := pv 0
  let D := pv 1
  pm (pc 16)
    (pTerminalTaylorPrefixClearedAt (pa c (pc 1)) D (pc 1))

private def pTerminalTaylorDoubleR : PE :=
  pTerminalTaylorDoubledAt (pv 0) (pm (pc 2) (pv 1))

private theorem pTerminalTaylor_double_normal :
    RingNormaliser.normalize pTerminalTaylorDoubleL =
      RingNormaliser.normalize pTerminalTaylorDoubleR := by
  decide

private def pTerminalCellQ0At (c : PE) : PE :=
  pm c
    (pa (pa (pa (pa (pa (pa (pa
      (pm (pc 1260) (pp c 7))
      (pn (pm (pc 44562) (pp c 6))))
      (pm (pc 62251) (pp c 5)))
      (pm (pc 138486) (pp c 4)))
      (pn (pm (pc 3422560) (pp c 3))))
      (pn (pm (pc 5749632) (pp c 2))))
      (pn (pm (pc 1592064) c)))
      (pc 167616))

private def pTerminalCellA2At (c : PE) : PE :=
  pa (pa (pa
    (pm (pc 4662) (pp c 3))
    (pm (pc 202419) (pp c 2)))
    (pm (pc 168714) c))
    (pc 30240)

private def pTerminalCellBlock : PE :=
  let c := pv 0
  let X := pv 1
  let q0 := pTerminalCellQ0At c
  let q1 := pa (pa (pa (pa (pa (pa
    (pm (pc 2520) (pp c 6))
    (pn (pm (pc 69174) (pp c 5))))
    (pn (pm (pc 151193) (pp c 4))))
    (pm (pc 952812) (pp c 3)))
    (pm (pc 1339520) (pp c 2)))
    (pm (pc 336000) c))
    (pc 20160)
  let q3 := pa (pa
    (pn (pm (pc 2520) (pp c 2)))
    (pm (pc 19950) c))
    (pc 11025)
  pa (pa (pa (pa q0 (pm q1 X))
    (pn (pm (pTerminalCellA2At c) (pp X 2))))
    (pm q3 (pp X 3)))
    (pn (pm (pc 1260) (pp X 4)))

private def pTerminalTaylorCellL : PE :=
  let c := pv 0
  let X := pv 1
  pTerminalTaylorDoubledAt c (pa (pp c 2) X)

private def pTerminalTaylorCellR : PE :=
  let c := pv 0
  pm (pm (pm (pc 16) (pa c (pc 1))) (pa c (pc 2)))
    pTerminalCellBlock

private theorem pTerminalTaylor_cell_normal :
    RingNormaliser.normalize pTerminalTaylorCellL =
      RingNormaliser.normalize pTerminalTaylorCellR := by
  decide

private def lowerSixRecoveryTerminalPrefixBlockLocal (c X : Q') : Q' :=
  RingNormaliser.eval (fun | 0 => c | _ => X) pTerminalCellBlock

private theorem terminalPrefixBlockLocal_eqv_public (c X : Q') :
    lowerSixRecoveryTerminalPrefixBlockLocal c X ≈
      lowerSixRecoveryTerminalPrefixBlock c X := by
  unfold lowerSixRecoveryTerminalPrefixBlockLocal
    lowerSixRecoveryTerminalPrefixBlock
  exact Q'.eqv_refl _

private theorem ringQpow_pos {a : Q'} (ha : (0 : Q') < a) :
    ∀ m, (0 : Q') < RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_pos (ringQpow_pos ha m) ha

/-- The closed Taylor prefix is nonnegative at the physical terminal length
`N=c+1` throughout every post-bootstrap within-center cell. -/
theorem lowerSixRecoveryTerminalTaylorPrefixPolynomial_nonnegative
    {k c : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c) :
    (0 : Q') ≤
      lowerSixRecoveryTerminalTaylorPrefixPolynomial
        (c + 1) (harmU (k + 1)) := by
  let Dn := k + 3
  let D := Q'.ofNat Dn
  let C := Q'.ofNat c
  let Xn := 2 * Dn - c * c
  let X := Q'.ofNat Xn
  let U := harmU (k + 1)
  let P := lowerSixRecoveryTerminalTaylorPrefixPolynomial (c + 1) U
  let Pc := RingNormaliser.eval
    (fun | 0 => C + (1 : Q') | _ => U) pTerminalTaylorPrefixScaled
  have hc36 : 36 ≤ c :=
    lowerSixWithinCenterCell_center_ge_thirtySix hk hcell
  have hcsq : c * c ≤ 2 * Dn := by
    dsimp only [Dn]
    have h := hcell.2.2.1
    omega
  have hXsum : c * c + Xn = 2 * Dn := by
    dsimp only [Xn]
    exact Nat.add_sub_of_le hcsq
  have hsuccsq : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  have hXle : Xn ≤ 2 * c := by
    have hupper := hcell.2.2.2
    rw [hsuccsq] at hupper
    dsimp only [Xn, Dn]
    omega
  have hX0 : (0 : Q') ≤ X := by
    dsimp only [X]
    exact ExpNeg.ofNat_nonneg' _
  have hX2c : X ≤ Q'.ofNat 2 * C := by
    have hcast : Q'.ofNat Xn ≤ Q'.ofNat (2 * c) :=
      CReal.ofNat_le_ofNat hXle
    have hmul : Q'.ofNat (2 * c) ≈ Q'.ofNat 2 * Q'.ofNat c :=
      HeatKernelRGStep.ofNat_mul_eqv 2 c
    dsimp only [X, C]
    exact Q'.le_trans' _ _ _ hcast (Q'.le_of_eqv hmul)
  have hblockPublic : (0 : Q') ≤
      lowerSixRecoveryTerminalPrefixBlock C X :=
    lowerSixRecoveryTerminalPrefixBlock_nonnegative hc36 hX0 hX2c
  have hblock : (0 : Q') ≤
      lowerSixRecoveryTerminalPrefixBlockLocal C X :=
    Q'.le_trans' _ _ _ hblockPublic
      (Q'.ge_of_eqv (terminalPrefixBlockLocal_eqv_public C X))
  have hC0 : (0 : Q') ≤ C := by
    dsimp only [C]
    exact ExpNeg.ofNat_nonneg' _
  have hC10 : (0 : Q') ≤ C + (1 : Q') :=
    Q'.zero_le_add _ _ hC0 (by decide)
  have hC20 : (0 : Q') ≤ C + Q'.ofNat 2 :=
    Q'.zero_le_add _ _ hC0 (by decide)
  have hRhs0 : (0 : Q') ≤
      Q'.ofNat 16 * (C + (1 : Q')) * (C + Q'.ofNat 2) *
        lowerSixRecoveryTerminalPrefixBlockLocal C X := by
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) hC10) hC20) hblock
  have hcellEq :
      RingNormaliser.eval
          (fun | 0 => C | _ => X) pTerminalTaylorCellL ≈
        RingNormaliser.eval
          (fun | 0 => C | _ => X) pTerminalTaylorCellR :=
    RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalTaylor_cell_normal _
  have hcellLeft0 : (0 : Q') ≤
      RingNormaliser.eval
        (fun | 0 => C | _ => X) pTerminalTaylorCellL := by
    have hright : RingNormaliser.eval
          (fun | 0 => C | _ => X) pTerminalTaylorCellR ≈
        Q'.ofNat 16 * (C + (1 : Q')) * (C + Q'.ofNat 2) *
          lowerSixRecoveryTerminalPrefixBlockLocal C X := by
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ hRhs0
      (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ hcellEq hright))
  have hCpow : Q'.ofNat (c * c) ≈
      RingNormaliser.qpow C 2 := by
    refine Q'.eqv_trans _ (C * C) _ ?_ ?_
    · dsimp only [C]
      exact HeatKernelRGStep.ofNat_mul_eqv c c
    · unfold RingNormaliser.qpow
      exact Q'.mul_eqv_congr_right _ _ C
        (Q'.eqv_symm (Q'.one_mul_eqv C))
  have hY : Q'.ofNat (2 * Dn) ≈
      RingNormaliser.qpow C 2 + X := by
    rw [← hXsum]
    refine Q'.eqv_trans _
      (Q'.ofNat (c * c) + Q'.ofNat Xn) _
      (Q'.ofNat_add_eqv (c * c) Xn) ?_
    dsimp only [X]
    exact Q'.add_eqv_congr_right _ _ _ hCpow
  have htwoD : Q'.ofNat 2 * D ≈ Q'.ofNat (2 * Dn) := by
    dsimp only [D]
    exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 2 Dn)
  have hYfull : Q'.ofNat 2 * D ≈
      RingNormaliser.qpow C 2 + X :=
    Q'.eqv_trans _ _ _ htwoD hY
  have hYreplace :
      RingNormaliser.eval
          (fun | 0 => C | _ => Q'.ofNat 2 * D)
          pTerminalTaylorDoubled ≈
        RingNormaliser.eval
          (fun | 0 => C | _ => RingNormaliser.qpow C 2 + X)
          pTerminalTaylorDoubled := by
    apply eval_eqv_congr pTerminalTaylorDoubled
    intro i
    rcases i with _ | i
    · exact Q'.eqv_refl _
    · exact hYfull
  have hcellView :
      RingNormaliser.eval
          (fun | 0 => C | _ => RingNormaliser.qpow C 2 + X)
          pTerminalTaylorDoubled ≈
        RingNormaliser.eval
          (fun | 0 => C | _ => X) pTerminalTaylorCellL := by
    exact Q'.eqv_refl _
  have hDoubled0 : (0 : Q') ≤
      RingNormaliser.eval
        (fun | 0 => C | _ => Q'.ofNat 2 * D)
        pTerminalTaylorDoubled := by
    exact Q'.le_trans' _ _ _ hcellLeft0
      (Q'.ge_of_eqv
        (Q'.eqv_trans _ _ _ hYreplace hcellView))
  have hdoubleEq :
      RingNormaliser.eval (fun | 0 => C | _ => D)
          pTerminalTaylorDoubleL ≈
        RingNormaliser.eval (fun | 0 => C | _ => D)
          pTerminalTaylorDoubleR :=
    RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalTaylor_double_normal _
  have hdoubleViewL :
      RingNormaliser.eval (fun | 0 => C | _ => D)
          pTerminalTaylorDoubleL ≈
        Q'.ofNat 16 * RingNormaliser.eval
          (fun | 0 => C + (1 : Q') | 1 => D | _ => (1 : Q'))
          pTerminalTaylorPrefixCleared := by
    exact Q'.eqv_refl _
  have hdoubleViewR :
      RingNormaliser.eval (fun | 0 => C | _ => D)
          pTerminalTaylorDoubleR ≈
        RingNormaliser.eval
          (fun | 0 => C | _ => Q'.ofNat 2 * D)
          pTerminalTaylorDoubled := by
    exact Q'.eqv_refl _
  have hClearedScaled0 : (0 : Q') ≤
      Q'.ofNat 16 * RingNormaliser.eval
        (fun | 0 => C + (1 : Q') | 1 => D | _ => (1 : Q'))
        pTerminalTaylorPrefixCleared := by
    have hscaledEq := Q'.eqv_trans _ _ _
      (Q'.eqv_symm hdoubleViewL)
      (Q'.eqv_trans _ _ _ hdoubleEq hdoubleViewR)
    exact Q'.le_trans' _ _ _ hDoubled0 (Q'.ge_of_eqv hscaledEq)
  have hUD : U * D ≈ (1 : Q') := by
    dsimp only [U, D, Dn]
    simpa only [Nat.add_assoc] using
      (HarmonicThetaLinearCarrier.harmonicUnit_mul_den (k + 1))
  have hclearEqRaw :
      RingNormaliser.eval
          (fun | 0 => C + (1 : Q') | 1 => U | _ => D)
          pTerminalTaylorPrefixClearL ≈
        RingNormaliser.eval
          (fun | 0 => C + (1 : Q') | 1 => U | _ => D)
          pTerminalTaylorPrefixClearR :=
    RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalTaylorPrefix_clear_normal _
  have hclearViewL :
      RingNormaliser.eval
          (fun | 0 => C + (1 : Q') | 1 => U | _ => D)
          pTerminalTaylorPrefixClearL ≈
        RingNormaliser.qpow D 4 * Pc := by
    exact Q'.eqv_refl _
  have hclearViewR :
      RingNormaliser.eval
          (fun | 0 => C + (1 : Q') | 1 => U | _ => D)
          pTerminalTaylorPrefixClearR ≈
        RingNormaliser.eval
          (fun | 0 => C + (1 : Q') | 1 => D | _ => U * D)
          pTerminalTaylorPrefixCleared := by
    exact Q'.eqv_refl _
  have hTreplace :
      RingNormaliser.eval
          (fun | 0 => C + (1 : Q') | 1 => D | _ => U * D)
          pTerminalTaylorPrefixCleared ≈
        RingNormaliser.eval
          (fun | 0 => C + (1 : Q') | 1 => D | _ => (1 : Q'))
          pTerminalTaylorPrefixCleared := by
    apply eval_eqv_congr pTerminalTaylorPrefixCleared
    intro i
    rcases i with _ | _ | i
    · exact Q'.eqv_refl _
    · exact Q'.eqv_refl _
    · exact hUD
  have hclearEq : RingNormaliser.qpow D 4 * Pc ≈
      RingNormaliser.eval
        (fun | 0 => C + (1 : Q') | 1 => D | _ => (1 : Q'))
        pTerminalTaylorPrefixCleared :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hclearViewL)
      (Q'.eqv_trans _ _ _ hclearEqRaw
        (Q'.eqv_trans _ _ _ hclearViewR hTreplace))
  have hScaledPrefix0 : (0 : Q') ≤
      Q'.ofNat 16 * (RingNormaliser.qpow D 4 * Pc) := by
    have hscaledEq := Q'.mul_eqv_congr_left (Q'.ofNat 16) _ _ hclearEq
    exact Q'.le_trans' _ _ _ hClearedScaled0
      (Q'.ge_of_eqv hscaledEq)
  have hDpos : (0 : Q') < D := by
    dsimp only [D, Dn]
    simpa only [Nat.add_assoc] using Q'.ofNat_succ_pos (k + 2)
  let F := Q'.ofNat 16 * RingNormaliser.qpow D 4
  have hFpos : (0 : Q') < F :=
    Q'.mul_pos (by decide) (ringQpow_pos hDpos 4)
  have hfactor :
      Q'.ofNat 16 * (RingNormaliser.qpow D 4 * Pc) ≈ Pc * F := by
    dsimp only [F]
    terminal_taylor_ring
  have hmul : (0 : Q') * F ≤ Pc * F := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.zero_mul_eqv F))
      (Q'.le_trans' _ _ _ hScaledPrefix0 (Q'.le_of_eqv hfactor))
  have hPc0 : (0 : Q') ≤ Pc :=
    BakryEmery.le_of_mul_le_mul_right_pos hFpos hmul
  have hN : Q'.ofNat (c + 1) ≈ C + (1 : Q') := by
    dsimp only [C]
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv c 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hPcoord : P ≈ Pc := by
    dsimp only [P, Pc]
    unfold lowerSixRecoveryTerminalTaylorPrefixPolynomial
    apply eval_eqv_congr pTerminalTaylorPrefixScaled
    intro i
    rcases i with _ | i
    · exact hN
    · exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ hPc0 (Q'.ge_of_eqv hPcoord)

private theorem one_sub_le_of_one_sub_le {q a : Q'}
    (h : (1 : Q') + -q ≤ a) :
    (1 : Q') + -a ≤ q := by
  have hn := Q'.neg_le_neg h
  have hadd := Q'.add_le_add_left (1 : Q') _ _ hn
  have hright : (1 : Q') + -((1 : Q') + -q) ≈ q := by
    let rho : Nat → Q' := fun _ => q
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) rho
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright)

private theorem recoveryLinearProfileFloor_nonnegative
    {K : Nat} (h13 : 13 ≤ 8 * (K + 2)) :
    (0 : Q') ≤ Q'.ofNat 8 + -(Q'.ofNat 13 * harmU K) := by
  let D := Q'.ofNat (K + 2)
  have hDpos : (0 : Q') < D := by
    dsimp only [D]
    simpa only [Nat.add_assoc] using Q'.ofNat_succ_pos (K + 1)
  have hcast : Q'.ofNat 13 ≤ Q'.ofNat (8 * (K + 2)) :=
    CReal.ofNat_le_ofNat h13
  have hright : Q'.ofNat (8 * (K + 2)) ≈ Q'.ofNat 8 * D := by
    dsimp only [D]
    exact HeatKernelRGStep.ofNat_mul_eqv 8 (K + 2)
  have hUD : harmU K * D ≈ (1 : Q') := by
    dsimp only [D]
    exact HarmonicThetaLinearCarrier.harmonicUnit_mul_den K
  have hleft : (Q'.ofNat 13 * harmU K) * D ≈ Q'.ofNat 13 := by
    refine Q'.eqv_trans _ (Q'.ofNat 13 * (harmU K * D)) _ ?_ ?_
    · exact Q'.mul_assoc_eqv _ _ _
    · exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hUD) (Q'.mul_one_eqv _)
  have hscaled : (Q'.ofNat 13 * harmU K) * D ≤
      Q'.ofNat 8 * D :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hcast (Q'.le_of_eqv hright))
  have h13u : Q'.ofNat 13 * harmU K ≤ Q'.ofNat 8 :=
    BakryEmery.le_of_mul_le_mul_right_pos hDpos hscaled
  exact Q'.sub_nonneg_of_le h13u

private theorem lowerSixRecoveryLinearCarrier_terminal_form (K j : Nat) :
    lowerSixRecoveryLinearCarrier K j ≈
      ((Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) *
          lowerSixRecoveryCubicProfile (harmW K)) *
          qpow (harmW K) (6 * j) +
        -(Q'.ofNat 8 *
          (Q'.ofNat (j + 1) * Q'.ofNat (j + 2)) *
          qpow (harmW K) (8 * j + 3)) := by
  let n := Q'.ofNat (j + 1)
  let n1 := Q'.ofNat (j + 2)
  let w := harmW K
  let q6 := qpow w (6 * j)
  let qo := qpow w (2 * (j + 1) + 1)
  let q8 := qpow w (8 * j + 3)
  have hs := lowerSixRecoveryModeSlope_eqv_cubicSlope K (j + 1)
  have hstart : lowerSixRecoveryLinearCarrier K j ≈
      n * q6 * lowerSixRecoveryCubicSlope w (j + 1) := by
    unfold lowerSixRecoveryLinearCarrier
    dsimp only [n, q6, w]
    exact Q'.mul_eqv_congr_left _ _ _ hs
  have hslopeForm : lowerSixRecoveryCubicSlope w (j + 1) ≈
      n * lowerSixRecoveryCubicProfile w +
        -(Q'.ofNat 8 * (n1 * qo)) := by
    unfold lowerSixRecoveryCubicSlope
    dsimp only [n, n1, qo]
    rw [show j + 1 + 1 = j + 2 by omega]
    exact Q'.eqv_refl _
  have hslopeReplace :
      n * q6 * lowerSixRecoveryCubicSlope w (j + 1) ≈
        n * q6 *
          (n * lowerSixRecoveryCubicProfile w +
            -(Q'.ofNat 8 * (n1 * qo))) :=
    Q'.mul_eqv_congr_left _ _ _ hslopeForm
  have halgebra :
      n * q6 *
          (n * lowerSixRecoveryCubicProfile w +
            -(Q'.ofNat 8 * (n1 * qo))) ≈
        ((n * n) * lowerSixRecoveryCubicProfile w) * q6 +
          -(Q'.ofNat 8 * (n * n1) * (q6 * qo)) := by
    terminal_taylor_ring
  have hexp : 6 * j + (2 * (j + 1) + 1) = 8 * j + 3 := by omega
  have hpower : q6 * qo ≈ q8 := by
    dsimp only [q6, qo, q8]
    rw [← hexp]
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_add _ _ _)
  have hreplace :
      ((n * n) * lowerSixRecoveryCubicProfile w) * q6 +
          -(Q'.ofNat 8 * (n * n1) * (q6 * qo)) ≈
        ((n * n) * lowerSixRecoveryCubicProfile w) * q6 +
          -(Q'.ofNat 8 * (n * n1) * q8) := by
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hpower))
  dsimp only [n, n1, w, q6, qo, q8] at hstart hslopeReplace halgebra hreplace ⊢
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ hslopeReplace
      (Q'.eqv_trans _ _ _ halgebra hreplace))

/-- The fourth-order Taylor mode is a pointwise lower bound for the exact
linear recovery carrier. -/
theorem lowerSixRecoveryTerminalTaylorMode_le_carrier
    {K : Nat} (h13 : 13 ≤ 8 * (K + 2)) (j : Nat) :
    lowerSixRecoveryTerminalTaylorMode (harmU K) j ≤
      lowerSixRecoveryLinearCarrier K j := by
  let u := harmU K
  let w := harmW K
  let n := Q'.ofNat (j + 1)
  let n1 := Q'.ofNat (j + 2)
  let a := Q'.ofNat (6 * j)
  let m := 8 * j + 3
  let F := Q'.ofNat 8 + -(Q'.ofNat 13 * u)
  let L := (1 : Q') + -(a * u)
  let P := lowerSixRecoveryCubicProfile w
  let q6 := qpow w (6 * j)
  let q8 := qpow w m
  let T := oneSubTaylor4 u m
  let B := Q'.ofNat 8 * (n * n1)
  have hu0 : (0 : Q') ≤ u := by
    dsimp only [u]
    exact harmU_nonneg K
  have hu1 : u ≤ (1 : Q') := by
    dsimp only [u]
    exact harmU_le_one K
  have hw0 : (0 : Q') ≤ w := by
    dsimp only [w]
    exact harmW_nonneg K
  have hw1 : w ≤ (1 : Q') := by
    dsimp only [w]
    exact harmW_le_one K
  have hF0 : (0 : Q') ≤ F := by
    dsimp only [F, u]
    exact recoveryLinearProfileFloor_nonnegative h13
  have hprofile : F ≤ P := by
    have hp := lowerSixRecoveryCubicProfile_oneSub_ge_linear hu0 hu1
    dsimp only [F, P, w, u]
    change Q'.ofNat 8 + -(Q'.ofNat 13 * harmU K) ≤
      lowerSixRecoveryCubicProfile
        (ReciprocalBernoulliUpper.oneSub (harmU K))
    exact hp
  have hwu : (1 : Q') + -w ≈ u := by
    dsimp only [w, u]
    unfold harmW ReciprocalBernoulliUpper.oneSub
    let rho : Nat → Q' := fun _ => harmU K
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) rho
  have hbernRaw := HeatKernelRGStep.oneSub_qpow_le hw0 hw1 (6 * j)
  have hbern : (1 : Q') + -q6 ≤ a * u := by
    have hrhs : Q'.ofNat (6 * j) * ((1 : Q') + -w) ≈ a * u := by
      dsimp only [a]
      exact Q'.mul_eqv_congr_left _ _ _ hwu
    exact Q'.le_trans' _ _ _ hbernRaw (Q'.le_of_eqv hrhs)
  have hq6 : L ≤ q6 := by
    dsimp only [L]
    exact one_sub_le_of_one_sub_le hbern
  have hq60 : (0 : Q') ≤ q6 := qpow_nonneg _ hw0 _
  have hFL : F * L ≤ P * q6 := by
    have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ F hq6 hF0
    have hsecond := Q'.mul_le_mul_of_nonneg_right _ _ q6 hprofile hq60
    exact Q'.le_trans' _ _ _ hfirst hsecond
  have hn20 : (0 : Q') ≤ n * n :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) (ExpNeg.ofNat_nonneg' _)
  have hposRaw := Q'.mul_le_mul_of_nonneg_left _ _ (n * n) hFL hn20
  have hpos : ((n * n) * F) * L ≤ ((n * n) * P) * q6 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_assoc_eqv (n * n) F L))
      (Q'.le_trans' _ _ _ hposRaw
        (Q'.ge_of_eqv (Q'.mul_assoc_eqv (n * n) P q6)))
  have htaylor : q8 ≤ T := by
    dsimp only [q8, T, m, w, u]
    change qpow ((1 : Q') + -harmU K) (8 * j + 3) ≤
      oneSubTaylor4 (harmU K) (8 * j + 3)
    exact qpow_oneSub_le_taylor4 hu0 hu1 _
  have hB0 : (0 : Q') ≤ B := by
    dsimp only [B, n, n1]
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _)
        (ExpNeg.ofNat_nonneg' _))
  have hadverseRaw := Q'.mul_le_mul_of_nonneg_left _ _ B htaylor hB0
  have hadverse : -(B * T) ≤ -(B * q8) :=
    Q'.neg_le_neg hadverseRaw
  have hsum : ((n * n) * F) * L + -(B * T) ≤
      ((n * n) * P) * q6 + -(B * q8) := by
    have h1 := Q'.add_le_add_right _ _ (-(B * T)) hpos
    have h2 := Q'.add_le_add_left (((n * n) * P) * q6) _ _ hadverse
    exact Q'.le_trans' _ _ _ h1 h2
  have hfloor : lowerSixRecoveryTerminalTaylorMode u j ≈
      ((n * n) * F) * L + -(B * T) := by
    unfold lowerSixRecoveryTerminalTaylorMode
    dsimp only [u, n, n1, a, m, F, L, B, T]
    exact Q'.eqv_refl _
  have hcarrier := lowerSixRecoveryLinearCarrier_terminal_form K j
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfloor)
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hcarrier))

/-- The exact Taylor prefix pays the physical terminal carrier numerator.
The proof first removes the positive integer Taylor scaling, then sums the
pointwise carrier comparison, and finally invokes the already checked exact
denominator clearing for the carrier prefix. -/
theorem lowerSixRecoveryPhysicalTerminalPrefixNumerator_nonnegative
    {k c : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c) :
    (0 : Q') ≤
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (c + 1) := by
  let S := finSum
    (fun j => lowerSixRecoveryTerminalTaylorMode (harmU (k + 1)) j)
    (c + 1)
  let F := Q'.ofNat 5040
  have hpoly :=
    lowerSixRecoveryTerminalTaylorPrefixPolynomial_nonnegative hk hcell
  have hsumEq :=
    lowerSixRecoveryTerminalTaylorFinSum_scaled_eqv_prefix
      (harmU (k + 1)) (c + 1)
  have hscaled : (0 : Q') ≤ F * S := by
    dsimp only [F, S]
    exact Q'.le_trans' _ _ _ hpoly (Q'.ge_of_eqv hsumEq)
  have hFpos : (0 : Q') < F := by
    dsimp only [F]
    decide
  have hmul : (0 : Q') * F ≤ S * F := by
    exact Q'.le_trans' _ (0 : Q') _
      (Q'.le_of_eqv (Q'.zero_mul_eqv F))
      (Q'.le_trans' _ (F * S) _ hscaled
        (Q'.le_of_eqv (Q'.mul_comm_eqv F S)))
  have hS0 : (0 : Q') ≤ S :=
    BakryEmery.le_of_mul_le_mul_right_pos hFpos hmul
  have hterms : ∀ j,
      lowerSixRecoveryTerminalTaylorMode (harmU (k + 1)) j ≤
        lowerSixRecoveryLinearCarrier (k + 1) j := by
    intro j
    exact lowerSixRecoveryTerminalTaylorMode_le_carrier
      (K := k + 1) (by omega) j
  have hsumCarrier :=
    YMGap.Constructive.ExpNeg.finSum_le_finSum_of_termwise
      (fun j => lowerSixRecoveryTerminalTaylorMode (harmU (k + 1)) j)
      (fun j => lowerSixRecoveryLinearCarrier (k + 1) j)
      hterms (c + 1)
  have hprefix : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k c := by
    unfold lowerSixRecoveryNextCarrierPrefix
    exact Q'.le_trans' _ _ _ hS0 hsumCarrier
  exact lowerSixRecoveryLinearCarrierPrefixNumerator_nonnegative hprefix

/-- The Taylor certificate closes the only analytic input of the bounded
constructive prefix-crossing search. -/
theorem lowerSixRecoveryPhysicalPrefixCrossing_postBootstrap
    {k c : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c) :
    let s := lowerSixRecoveryPhysicalPrefixCrossing k c
    lowerSixRecoveryPhysicalPeakIndex c ≤ s ∧
      s ≤ 2 * c - 1 ∧
      (s = lowerSixRecoveryPhysicalPeakIndex c ∨
        lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) s ≤
          (0 : Q')) ∧
      (0 : Q') ≤
        lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (s + 1) := by
  exact lowerSixRecoveryPhysicalPrefixCrossing_postBootstrap_spec hcell
    (lowerSixRecoveryPhysicalTerminalPrefixNumerator_nonnegative hk hcell)

#print axioms lowerSixRecoveryTerminalTaylorMode
#print axioms lowerSixRecoveryTerminalTaylorPrefixPolynomial
#print axioms lowerSixRecoveryTerminalTaylorFinSum_scaled_eqv_prefix
#print axioms lowerSixRecoveryTerminalTaylorPrefixPolynomial_nonnegative
#print axioms lowerSixRecoveryTerminalTaylorMode_le_carrier
#print axioms lowerSixRecoveryPhysicalTerminalPrefixNumerator_nonnegative
#print axioms lowerSixRecoveryPhysicalPrefixCrossing_postBootstrap

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalTerminalTaylor
