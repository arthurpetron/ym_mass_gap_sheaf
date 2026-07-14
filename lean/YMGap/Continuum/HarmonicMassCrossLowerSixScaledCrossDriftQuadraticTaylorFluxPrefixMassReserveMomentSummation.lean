/-
Finite summation-by-parts closure for the next-scale Gaussian moments.

The local Gaussian decrement lowers an even moment by two powers.  This file
supplies the exact odd-power increment inequalities and the boundary-retaining
finite Abel telescope used to iterate that lowering at orders 2, 4, 6, and 8.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentSummation

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem summation_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "summation_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               summation_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

def lowerSixQPower (n p : Nat) : Q' :=
  RingNormaliser.qpow (Q'.ofNat n) p

theorem lowerSixQPower_nonnegative (n p : Nat) :
    (0 : Q') ≤ lowerSixQPower n p := by
  unfold lowerSixQPower
  induction p with
  | zero =>
      unfold RingNormaliser.qpow
      decide
  | succ p ih =>
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ ih (HeatKernelRGStep.zero_le_ofNat n)

private theorem ringQpow_nonnegative (x : Q') (hx : (0 : Q') ≤ x) :
    ∀ p : Nat, (0 : Q') ≤ RingNormaliser.qpow x p
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | p + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative x hx p) hx

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def pv : PE := .var 0
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def ppow (a : PE) (n : Nat) : PE := .pow a n

private def pSucc : PE := padd pv (pc 1)

private def pDiff (q : Nat) : PE :=
  padd (ppow pSucc q) (pneg (ppow pv q))

private def pBound (q : Nat) : PE :=
  pmul (pc q) (ppow pSucc (q - 1))

private def pResidual1 : PE := pc 0
private def pResidual3 : PE := padd (pmul (pc 3) pv) (pc 2)
private def pResidual5 : PE :=
  padd (padd (padd
    (pmul (pc 10) (ppow pv 3))
    (pmul (pc 20) (ppow pv 2)))
    (pmul (pc 15) pv)) (pc 4)
private def pResidual7 : PE :=
  padd (padd (padd (padd (padd
    (pmul (pc 21) (ppow pv 5))
    (pmul (pc 70) (ppow pv 4)))
    (pmul (pc 105) (ppow pv 3)))
    (pmul (pc 84) (ppow pv 2)))
    (pmul (pc 35) pv)) (pc 6)

private def pAbelStepL : PE :=
  let S : PE := .var 0
  let B : PE := .var 2
  let W : PE := .var 3
  let V : PE := .var 4
  padd (padd S (pmul B (padd W (pneg V)))) (pmul B V)

private def pAbelStepR : PE :=
  let S : PE := .var 0
  let A : PE := .var 1
  let B : PE := .var 2
  let W : PE := .var 3
  padd (padd S (pmul A W)) (pmul (padd B (pneg A)) W)

private theorem pAbelStep_normal :
    RingNormaliser.normalize pAbelStepL =
      RingNormaliser.normalize pAbelStepR := by decide

private theorem abel_step_algebra (S A B W V : Q') :
    (S + B * (W + -V)) + B * V ≈
      (S + A * W) + (B + -A) * W := by
  let rho : Nat → Q' := fun i =>
    match i with
    | 0 => S
    | 1 => A
    | 2 => B
    | 3 => W
    | _ => V
  simpa [pAbelStepL, pAbelStepR, padd, pmul, pneg,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pAbelStepL pAbelStepR pAbelStep_normal rho)

private theorem pStep1_normal :
    RingNormaliser.normalize (padd (pDiff 1) pResidual1) =
      RingNormaliser.normalize (pBound 1) := by decide
private theorem pStep3_normal :
    RingNormaliser.normalize (padd (pDiff 3) pResidual3) =
      RingNormaliser.normalize (pBound 3) := by decide
private theorem pStep5_normal :
    RingNormaliser.normalize (padd (pDiff 5) pResidual5) =
      RingNormaliser.normalize (pBound 5) := by decide
private theorem pStep7_normal :
    RingNormaliser.normalize (padd (pDiff 7) pResidual7) =
      RingNormaliser.normalize (pBound 7) := by decide

private theorem residual1_nonnegative (x : Q') (_hx : (0 : Q') ≤ x) :
    (0 : Q') ≤ RingNormaliser.eval (fun _ => x) pResidual1 := by
  unfold pResidual1 pc RingNormaliser.eval
  decide

private theorem residual3_nonnegative (x : Q') (hx : (0 : Q') ≤ x) :
    (0 : Q') ≤ RingNormaliser.eval (fun _ => x) pResidual3 := by
  unfold pResidual3 padd pmul pc pv RingNormaliser.eval
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 3) hx)
    (HeatKernelRGStep.zero_le_ofNat 2)

private theorem residual5_nonnegative (x : Q') (hx : (0 : Q') ≤ x) :
    (0 : Q') ≤ RingNormaliser.eval (fun _ => x) pResidual5 := by
  unfold pResidual5 padd pmul pc pv ppow RingNormaliser.eval
  have hx2 : (0 : Q') ≤ RingNormaliser.qpow x 2 :=
    ringQpow_nonnegative x hx 2
  have hx3 : (0 : Q') ≤ RingNormaliser.qpow x 3 :=
    ringQpow_nonnegative x hx 3
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 10) hx3)
        (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 20) hx2))
      (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 15) hx))
    (HeatKernelRGStep.zero_le_ofNat 4)

private theorem residual7_nonnegative (x : Q') (hx : (0 : Q') ≤ x) :
    (0 : Q') ≤ RingNormaliser.eval (fun _ => x) pResidual7 := by
  unfold pResidual7 padd pmul pc pv ppow RingNormaliser.eval
  have hx2 : (0 : Q') ≤ RingNormaliser.qpow x 2 :=
    ringQpow_nonnegative x hx 2
  have hx3 : (0 : Q') ≤ RingNormaliser.qpow x 3 :=
    ringQpow_nonnegative x hx 3
  have hx4 : (0 : Q') ≤ RingNormaliser.qpow x 4 :=
    ringQpow_nonnegative x hx 4
  have hx5 : (0 : Q') ≤ RingNormaliser.qpow x 5 :=
    ringQpow_nonnegative x hx 5
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 21) hx5)
            (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 70) hx4))
          (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 105) hx3))
        (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 84) hx2))
      (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 35) hx))
    (HeatKernelRGStep.zero_le_ofNat 6)

private theorem power_increment_le_core
    (R L B : Q') (hR : (0 : Q') ≤ R)
    (halg : L + R ≈ B) : L ≤ B := by
  have hadd : L ≤ L + R := Q'.add_le_self_of_nonneg _ _ hR
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv halg)

private theorem lowerSixSuccessorBase_eqv (n : Nat) :
    Q'.ofNat (n + 1) ≈ Q'.ofNat n + Q'.ofInt 1 := by
  refine Q'.eqv_trans _ (Q'.ofNat n + Q'.ofNat 1) _
    (Q'.ofNat_add_eqv n 1) ?_
  exact Q'.add_eqv_congr_left _ _ _ (by decide)

private theorem lowerSixSuccessorPower_eqv (n p : Nat) :
    RingNormaliser.qpow (Q'.ofNat (n + 1)) p ≈
      RingNormaliser.qpow (Q'.ofNat n + Q'.ofInt 1) p :=
  RingNormaliser.qpow_eqv_congr (lowerSixSuccessorBase_eqv n) p

private theorem lowerSixResidualIdentity
    (n q : Nat) (R : Q')
    (hraw :
      (RingNormaliser.qpow (Q'.ofNat n + Q'.ofInt 1) q +
          -RingNormaliser.qpow (Q'.ofNat n) q) + R ≈
        Q'.ofInt (Int.ofNat q) *
          RingNormaliser.qpow (Q'.ofNat n + Q'.ofInt 1) (q - 1)) :
    (lowerSixQPower (n + 1) q + -lowerSixQPower n q) + R ≈
      Q'.ofNat q * lowerSixQPower (n + 1) (q - 1) := by
  have hpq := lowerSixSuccessorPower_eqv n q
  have hpqm := lowerSixSuccessorPower_eqv n (q - 1)
  have hleft :
      (lowerSixQPower (n + 1) q + -lowerSixQPower n q) + R ≈
        (RingNormaliser.qpow (Q'.ofNat n + Q'.ofInt 1) q +
          -RingNormaliser.qpow (Q'.ofNat n) q) + R := by
    unfold lowerSixQPower
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hpq (Q'.eqv_refl _)) (Q'.eqv_refl R)
  have hcoeff : Q'.ofNat q ≈ Q'.ofInt (Int.ofNat q) :=
    Q'.eqv_refl _
  have hright :
      Q'.ofNat q * lowerSixQPower (n + 1) (q - 1) ≈
        Q'.ofInt (Int.ofNat q) *
          RingNormaliser.qpow (Q'.ofNat n + Q'.ofInt 1) (q - 1) := by
    unfold lowerSixQPower
    refine Q'.eqv_trans _
      (Q'.ofInt (Int.ofNat q) *
        RingNormaliser.qpow (Q'.ofNat (n + 1)) (q - 1)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hcoeff
    · exact Q'.mul_eqv_congr_left _ _ _ hpqm
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hraw (Q'.eqv_symm hright))

theorem lowerSixQPower_increment_le_one (n : Nat) :
    lowerSixQPower (n + 1) 1 + -lowerSixQPower n 1 ≤
      Q'.ofNat 1 * lowerSixQPower (n + 1) 0 := by
  let x := Q'.ofNat n
  apply power_increment_le_core
    (RingNormaliser.eval (fun _ => x) pResidual1)
  · exact residual1_nonnegative x (HeatKernelRGStep.zero_le_ofNat n)
  · unfold lowerSixQPower
    apply lowerSixResidualIdentity n 1
    simpa [pDiff, pBound, pResidual1, pSucc, pc, pv, padd, pmul, pneg,
      ppow, RingNormaliser.eval, x] using
      (RingNormaliser.poly_identity_of_normal_eq
        (padd (pDiff 1) pResidual1) (pBound 1) pStep1_normal
        (fun _ => x))

theorem lowerSixQPower_increment_le_three (n : Nat) :
    lowerSixQPower (n + 1) 3 + -lowerSixQPower n 3 ≤
      Q'.ofNat 3 * lowerSixQPower (n + 1) 2 := by
  let x := Q'.ofNat n
  apply power_increment_le_core
    (RingNormaliser.eval (fun _ => x) pResidual3)
  · exact residual3_nonnegative x (HeatKernelRGStep.zero_le_ofNat n)
  · unfold lowerSixQPower
    apply lowerSixResidualIdentity n 3
    simpa [pDiff, pBound, pResidual3, pSucc, pc, pv, padd, pmul, pneg,
      ppow, RingNormaliser.eval, x] using
      (RingNormaliser.poly_identity_of_normal_eq
        (padd (pDiff 3) pResidual3) (pBound 3) pStep3_normal
        (fun _ => x))

theorem lowerSixQPower_increment_le_five (n : Nat) :
    lowerSixQPower (n + 1) 5 + -lowerSixQPower n 5 ≤
      Q'.ofNat 5 * lowerSixQPower (n + 1) 4 := by
  let x := Q'.ofNat n
  apply power_increment_le_core
    (RingNormaliser.eval (fun _ => x) pResidual5)
  · exact residual5_nonnegative x (HeatKernelRGStep.zero_le_ofNat n)
  · unfold lowerSixQPower
    apply lowerSixResidualIdentity n 5
    simpa [pDiff, pBound, pResidual5, pSucc, pc, pv, padd, pmul, pneg,
      ppow, RingNormaliser.eval, x] using
      (RingNormaliser.poly_identity_of_normal_eq
        (padd (pDiff 5) pResidual5) (pBound 5) pStep5_normal
        (fun _ => x))

theorem lowerSixQPower_increment_le_seven (n : Nat) :
    lowerSixQPower (n + 1) 7 + -lowerSixQPower n 7 ≤
      Q'.ofNat 7 * lowerSixQPower (n + 1) 6 := by
  let x := Q'.ofNat n
  apply power_increment_le_core
    (RingNormaliser.eval (fun _ => x) pResidual7)
  · exact residual7_nonnegative x (HeatKernelRGStep.zero_le_ofNat n)
  · unfold lowerSixQPower
    apply lowerSixResidualIdentity n 7
    simpa [pDiff, pBound, pResidual7, pSucc, pc, pv, padd, pmul, pneg,
      ppow, RingNormaliser.eval, x] using
      (RingNormaliser.poly_identity_of_normal_eq
        (padd (pDiff 7) pResidual7) (pBound 7) pStep7_normal
        (fun _ => x))

/-! ## Boundary-retaining finite Abel telescope -/

/-- The truncated next-scale Gaussian moment `Σ_{n=1}^N n^p W_n`. -/
def lowerSixNextGaussianMoment (k p N : Nat) : Q' :=
  finSum
    (fun j => lowerSixQPower (j + 1) p *
      lowerSixModeWeight (k + 1) (j + 1)) N

/-- The finite weighted decrement `Σ_{n=1}^N n^q (W_n-W_{n+1})`. -/
def lowerSixNextGaussianDifferenceMoment (k q N : Nat) : Q' :=
  finSum
    (fun j => lowerSixQPower (j + 1) q *
      (lowerSixModeWeight (k + 1) (j + 1) +
        -lowerSixModeWeight (k + 1) (j + 2))) N

theorem lowerSixNextGaussianMoment_nonnegative (k p N : Nat) :
    (0 : Q') ≤ lowerSixNextGaussianMoment k p N := by
  unfold lowerSixNextGaussianMoment
  induction N with
  | zero => exact Q'.le_refl' 0
  | succ N ih =>
      exact Q'.zero_le_add _ _ ih
        (Q'.mul_nonneg _ _
          (lowerSixQPower_nonnegative (N + 1) p)
          (lowerSixModeWeight_nonnegative (k + 1) (N + 1)))

private theorem lowerSixNextGaussianDifferenceMoment_augmented_le
    (q : Nat) (hzero : lowerSixQPower 0 q ≈ (0 : Q'))
    (hinc : ∀ n : Nat,
      lowerSixQPower (n + 1) q + -lowerSixQPower n q ≤
        Q'.ofNat q * lowerSixQPower (n + 1) (q - 1))
    (k : Nat) : ∀ N : Nat,
    lowerSixNextGaussianDifferenceMoment k q N +
        lowerSixQPower N q * lowerSixModeWeight (k + 1) (N + 1) ≤
      Q'.ofNat q * lowerSixNextGaussianMoment k (q - 1) N
  | 0 => by
      have hboundary :
          lowerSixQPower 0 q * lowerSixModeWeight (k + 1) 1 ≈
            (0 : Q') :=
        Q'.eqv_trans _ (0 * lowerSixModeWeight (k + 1) 1) _
          (Q'.mul_eqv_congr_right _ _ _ hzero) (Q'.zero_mul_eqv _)
      have hleft :
          lowerSixNextGaussianDifferenceMoment k q 0 +
              lowerSixQPower 0 q * lowerSixModeWeight (k + 1) 1 ≈
            (0 : Q') := by
        unfold lowerSixNextGaussianDifferenceMoment finSum
        exact Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) hboundary
      have hright :
          Q'.ofNat q * lowerSixNextGaussianMoment k (q - 1) 0 ≈
            (0 : Q') := by
        unfold lowerSixNextGaussianMoment finSum
        exact Q'.mul_zero_eqv _
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.ge_of_eqv hright)
  | N + 1 => by
      have ih := lowerSixNextGaussianDifferenceMoment_augmented_le
        q hzero hinc k N
      have hW0 : (0 : Q') ≤ lowerSixModeWeight (k + 1) (N + 1) :=
        lowerSixModeWeight_nonnegative (k + 1) (N + 1)
      have hstep := Q'.mul_le_mul_of_nonneg_right _ _
        (lowerSixModeWeight (k + 1) (N + 1)) (hinc N) hW0
      have hadd := Q'.add_le_add ih hstep
      have hleft :
          lowerSixNextGaussianDifferenceMoment k q (N + 1) +
              lowerSixQPower (N + 1) q *
                lowerSixModeWeight (k + 1) (N + 2) ≈
        (lowerSixNextGaussianDifferenceMoment k q N +
              lowerSixQPower N q *
                lowerSixModeWeight (k + 1) (N + 1)) +
            ((lowerSixQPower (N + 1) q + -lowerSixQPower N q) *
              lowerSixModeWeight (k + 1) (N + 1)) := by
        unfold lowerSixNextGaussianDifferenceMoment
        rw [finSum_succ]
        simpa only [show N + 1 + 1 = N + 2 by omega] using
          (abel_step_algebra
            (finSum
              (fun j => lowerSixQPower (j + 1) q *
                (lowerSixModeWeight (k + 1) (j + 1) +
                  -lowerSixModeWeight (k + 1) (j + 2))) N)
            (lowerSixQPower N q) (lowerSixQPower (N + 1) q)
            (lowerSixModeWeight (k + 1) (N + 1))
            (lowerSixModeWeight (k + 1) (N + 2)))
      have hright :
          (Q'.ofNat q * lowerSixNextGaussianMoment k (q - 1) N) +
              ((Q'.ofNat q * lowerSixQPower (N + 1) (q - 1)) *
                lowerSixModeWeight (k + 1) (N + 1)) ≈
            Q'.ofNat q *
              lowerSixNextGaussianMoment k (q - 1) (N + 1) := by
        unfold lowerSixNextGaussianMoment
        rw [finSum_succ]
        refine Q'.eqv_trans _
          ((Q'.ofNat q *
              finSum
                (fun j => lowerSixQPower (j + 1) (q - 1) *
                  lowerSixModeWeight (k + 1) (j + 1)) N) +
            Q'.ofNat q *
              (lowerSixQPower (N + 1) (q - 1) *
                lowerSixModeWeight (k + 1) (N + 1))) _ ?_ ?_
        · exact Q'.add_eqv_congr_left _ _ _
            (Q'.mul_assoc_eqv _ _ _)
        · exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

private theorem lowerSixNextGaussianDifferenceMoment_le_of_increment
    (q : Nat) (hzero : lowerSixQPower 0 q ≈ (0 : Q'))
    (hinc : ∀ n : Nat,
      lowerSixQPower (n + 1) q + -lowerSixQPower n q ≤
        Q'.ofNat q * lowerSixQPower (n + 1) (q - 1))
    (k N : Nat) :
    lowerSixNextGaussianDifferenceMoment k q N ≤
      Q'.ofNat q * lowerSixNextGaussianMoment k (q - 1) N := by
  have haug := lowerSixNextGaussianDifferenceMoment_augmented_le
    q hzero hinc k N
  have hboundary0 : (0 : Q') ≤
      lowerSixQPower N q * lowerSixModeWeight (k + 1) (N + 1) :=
    Q'.mul_nonneg _ _ (lowerSixQPower_nonnegative N q)
      (lowerSixModeWeight_nonnegative (k + 1) (N + 1))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ hboundary0) haug

theorem lowerSixNextGaussianDifferenceMoment_one_le (k N : Nat) :
    lowerSixNextGaussianDifferenceMoment k 1 N ≤
      Q'.ofNat 1 * lowerSixNextGaussianMoment k 0 N := by
  apply lowerSixNextGaussianDifferenceMoment_le_of_increment 1
  · unfold lowerSixQPower RingNormaliser.qpow
    decide
  · exact lowerSixQPower_increment_le_one

theorem lowerSixNextGaussianDifferenceMoment_three_le (k N : Nat) :
    lowerSixNextGaussianDifferenceMoment k 3 N ≤
      Q'.ofNat 3 * lowerSixNextGaussianMoment k 2 N := by
  apply lowerSixNextGaussianDifferenceMoment_le_of_increment 3
  · unfold lowerSixQPower RingNormaliser.qpow
    decide
  · exact lowerSixQPower_increment_le_three

theorem lowerSixNextGaussianDifferenceMoment_five_le (k N : Nat) :
    lowerSixNextGaussianDifferenceMoment k 5 N ≤
      Q'.ofNat 5 * lowerSixNextGaussianMoment k 4 N := by
  apply lowerSixNextGaussianDifferenceMoment_le_of_increment 5
  · unfold lowerSixQPower RingNormaliser.qpow
    decide
  · exact lowerSixQPower_increment_le_five

theorem lowerSixNextGaussianDifferenceMoment_seven_le (k N : Nat) :
    lowerSixNextGaussianDifferenceMoment k 7 N ≤
      Q'.ofNat 7 * lowerSixNextGaussianMoment k 6 N := by
  apply lowerSixNextGaussianDifferenceMoment_le_of_increment 7
  · unfold lowerSixQPower RingNormaliser.qpow
    decide
  · exact lowerSixQPower_increment_le_seven

/-! ## Moment lowering from the local Gaussian decrement -/

/-- The reciprocal-Bernoulli quarter window on all modes in the finite
moment prefix. -/
def lowerSixNextGaussianQuarterWindow (k N : Nat) : Prop :=
  ∀ j : Nat, j < N →
    Q'.ofNat (2 * (j + 1) + 1) * lowerSixNextGaussianSeparation k ≤
      oneFourth

private theorem lowerSixMomentCell_le_scaledDifference
    {k : Nat} (hk : 5 ≤ k) (q n : Nat)
    (hsmall :
      Q'.ofNat (2 * n + 1) * lowerSixNextGaussianSeparation k ≤
        oneFourth) :
    Q'.ofNat 3 *
        (lowerSixQPower n (q + 1) * lowerSixModeWeight (k + 1) n) ≤
      Q'.ofNat (k + 3) *
        (lowerSixQPower n q *
          (lowerSixModeWeight (k + 1) n +
            -lowerSixModeWeight (k + 1) (n + 1))) := by
  have hlocal := three_mode_weight_le_scaled_nextDifference hk n hsmall
  have hpow0 : (0 : Q') ≤ lowerSixQPower n q :=
    lowerSixQPower_nonnegative n q
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (lowerSixQPower n q) hlocal hpow0
  have hleft :
      Q'.ofNat 3 *
          (lowerSixQPower n (q + 1) * lowerSixModeWeight (k + 1) n) ≈
        lowerSixQPower n q *
          ((Q'.ofNat 3 * Q'.ofNat n) *
            lowerSixModeWeight (k + 1) n) := by
    unfold lowerSixQPower
    rw [RingNormaliser.qpow_succ]
    summation_ring
  have hright :
      lowerSixQPower n q *
          (Q'.ofNat (k + 3) *
            (lowerSixModeWeight (k + 1) n +
              -lowerSixModeWeight (k + 1) (n + 1))) ≈
        Q'.ofNat (k + 3) *
          (lowerSixQPower n q *
            (lowerSixModeWeight (k + 1) n +
              -lowerSixModeWeight (k + 1) (n + 1))) := by
    summation_ring
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hright))

private theorem lowerSixThreeMoment_le_scaledDifference
    {k : Nat} (hk : 5 ≤ k) (q N : Nat)
    (hwindow : lowerSixNextGaussianQuarterWindow k N) :
    Q'.ofNat 3 * lowerSixNextGaussianMoment k (q + 1) N ≤
      Q'.ofNat (k + 3) *
        lowerSixNextGaussianDifferenceMoment k q N := by
  let f : Nat → Q' := fun j =>
    Q'.ofNat 3 *
      (lowerSixQPower (j + 1) (q + 1) *
        lowerSixModeWeight (k + 1) (j + 1))
  let g : Nat → Q' := fun j =>
    Q'.ofNat (k + 3) *
      (lowerSixQPower (j + 1) q *
        (lowerSixModeWeight (k + 1) (j + 1) +
          -lowerSixModeWeight (k + 1) (j + 2)))
  have hsum : finSum f N ≤ finSum g N := by
    apply finSum_le_lt
    intro j hj
    dsimp only [f, g]
    exact lowerSixMomentCell_le_scaledDifference hk q (j + 1)
      (hwindow j hj)
  have hleft :
      Q'.ofNat 3 * lowerSixNextGaussianMoment k (q + 1) N ≈
        finSum f N := by
    unfold lowerSixNextGaussianMoment
    dsimp only [f]
    exact const_mul_finSum _ _ _
  have hright :
      Q'.ofNat (k + 3) *
          lowerSixNextGaussianDifferenceMoment k q N ≈
        finSum g N := by
    unfold lowerSixNextGaussianDifferenceMoment
    dsimp only [g]
    exact const_mul_finSum _ _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hright))

private theorem lowerSixGaussianMoment_recurrence_of_difference
    {k : Nat} (hk : 5 ≤ k) (q N : Nat)
    (hwindow : lowerSixNextGaussianQuarterWindow k N)
    (hdifference :
      lowerSixNextGaussianDifferenceMoment k q N ≤
        Q'.ofNat q * lowerSixNextGaussianMoment k (q - 1) N) :
    Q'.ofNat 3 * lowerSixNextGaussianMoment k (q + 1) N ≤
      Q'.ofNat (k + 3) *
        (Q'.ofNat q * lowerSixNextGaussianMoment k (q - 1) N) := by
  have hmoment := lowerSixThreeMoment_le_scaledDifference hk q N hwindow
  have hD0 : (0 : Q') ≤ Q'.ofNat (k + 3) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (k + 3)) hdifference hD0
  exact Q'.le_trans' _ _ _ hmoment hscaled

theorem lowerSixGaussianMoment_two_recurrence
    {k N : Nat} (hk : 5 ≤ k)
    (hwindow : lowerSixNextGaussianQuarterWindow k N) :
    Q'.ofNat 3 * lowerSixNextGaussianMoment k 2 N ≤
      Q'.ofNat (k + 3) *
        (Q'.ofNat 1 * lowerSixNextGaussianMoment k 0 N) := by
  simpa only using lowerSixGaussianMoment_recurrence_of_difference
    hk 1 N hwindow (lowerSixNextGaussianDifferenceMoment_one_le k N)

theorem lowerSixGaussianMoment_four_recurrence
    {k N : Nat} (hk : 5 ≤ k)
    (hwindow : lowerSixNextGaussianQuarterWindow k N) :
    Q'.ofNat 3 * lowerSixNextGaussianMoment k 4 N ≤
      Q'.ofNat (k + 3) *
        (Q'.ofNat 3 * lowerSixNextGaussianMoment k 2 N) := by
  simpa only using lowerSixGaussianMoment_recurrence_of_difference
    hk 3 N hwindow (lowerSixNextGaussianDifferenceMoment_three_le k N)

theorem lowerSixGaussianMoment_six_recurrence
    {k N : Nat} (hk : 5 ≤ k)
    (hwindow : lowerSixNextGaussianQuarterWindow k N) :
    Q'.ofNat 3 * lowerSixNextGaussianMoment k 6 N ≤
      Q'.ofNat (k + 3) *
        (Q'.ofNat 5 * lowerSixNextGaussianMoment k 4 N) := by
  simpa only using lowerSixGaussianMoment_recurrence_of_difference
    hk 5 N hwindow (lowerSixNextGaussianDifferenceMoment_five_le k N)

theorem lowerSixGaussianMoment_eight_recurrence
    {k N : Nat} (hk : 5 ≤ k)
    (hwindow : lowerSixNextGaussianQuarterWindow k N) :
    Q'.ofNat 3 * lowerSixNextGaussianMoment k 8 N ≤
      Q'.ofNat (k + 3) *
        (Q'.ofNat 7 * lowerSixNextGaussianMoment k 6 N) := by
  simpa only using lowerSixGaussianMoment_recurrence_of_difference
    hk 7 N hwindow (lowerSixNextGaussianDifferenceMoment_seven_le k N)

/-- Four iterations of the moment-lowering recurrence.  The double-factorial
constant is exact: `1·3·5·7 = 105`, while four decrement steps contribute
`3⁴ = 81`. -/
theorem lowerSixGaussianMoment_eight_divisionFree
    {k N : Nat} (hk : 5 ≤ k)
    (hwindow : lowerSixNextGaussianQuarterWindow k N) :
    Q'.ofNat 81 * lowerSixNextGaussianMoment k 8 N ≤
      Q'.ofNat 105 *
        (lowerSixQPower (k + 3) 4 *
          lowerSixNextGaussianMoment k 0 N) := by
  let D := Q'.ofNat (k + 3)
  let M0 := lowerSixNextGaussianMoment k 0 N
  let M2 := lowerSixNextGaussianMoment k 2 N
  let M4 := lowerSixNextGaussianMoment k 4 N
  let M6 := lowerSixNextGaussianMoment k 6 N
  let M8 := lowerSixNextGaussianMoment k 8 N
  have h2 := lowerSixGaussianMoment_two_recurrence hk hwindow
  have h4 := lowerSixGaussianMoment_four_recurrence hk hwindow
  have h6 := lowerSixGaussianMoment_six_recurrence hk hwindow
  have h8 := lowerSixGaussianMoment_eight_recurrence hk hwindow
  change Q'.ofNat 3 * M2 ≤ D * (Q'.ofNat 1 * M0) at h2
  change Q'.ofNat 3 * M4 ≤ D * (Q'.ofNat 3 * M2) at h4
  change Q'.ofNat 3 * M6 ≤ D * (Q'.ofNat 5 * M4) at h6
  change Q'.ofNat 3 * M8 ≤ D * (Q'.ofNat 7 * M6) at h8
  change Q'.ofNat 81 * M8 ≤
    Q'.ofNat 105 * (lowerSixQPower (k + 3) 4 * M0)
  have hD0 : (0 : Q') ≤ D := by
    dsimp only [D]
    exact HeatKernelRGStep.zero_le_ofNat _
  have h8m := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 27) h8
    (HeatKernelRGStep.zero_le_ofNat 27)
  have hstep8 : Q'.ofNat 81 * M8 ≤
      Q'.ofNat 189 * (D * M6) := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by summation_ring))
      (Q'.le_trans' _ _ _ h8m (Q'.le_of_eqv (by summation_ring)))
  have h63D0 : (0 : Q') ≤ Q'.ofNat 63 * D :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 63) hD0
  have h6m := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat 63 * D) h6 h63D0
  have hstep6 : Q'.ofNat 189 * (D * M6) ≤
      Q'.ofNat 315 * (D * (D * M4)) := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by summation_ring))
      (Q'.le_trans' _ _ _ h6m (Q'.le_of_eqv (by summation_ring)))
  have h105DD0 : (0 : Q') ≤ (Q'.ofNat 105 * D) * D :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat 105) hD0) hD0
  have h4m := Q'.mul_le_mul_of_nonneg_left _ _
    ((Q'.ofNat 105 * D) * D) h4 h105DD0
  have hstep4 : Q'.ofNat 315 * (D * (D * M4)) ≤
      Q'.ofNat 315 * (D * (D * (D * M2))) := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by summation_ring))
      (Q'.le_trans' _ _ _ h4m (Q'.le_of_eqv (by summation_ring)))
  have h105DDD0 : (0 : Q') ≤ ((Q'.ofNat 105 * D) * D) * D :=
    Q'.mul_nonneg _ _ h105DD0 hD0
  have h2m := Q'.mul_le_mul_of_nonneg_left _ _
    (((Q'.ofNat 105 * D) * D) * D) h2 h105DDD0
  have hstep2 : Q'.ofNat 315 * (D * (D * (D * M2))) ≤
      Q'.ofNat 105 *
        (lowerSixQPower (k + 3) 4 * M0) := by
    have hpow : lowerSixQPower (k + 3) 4 ≈ D * (D * (D * D)) := by
      change RingNormaliser.qpow D 4 ≈ D * (D * (D * D))
      simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
      summation_ring
    have hright :
        (((Q'.ofNat 105 * D) * D) * D) *
            (D * (Q'.ofNat 1 * M0)) ≈
          Q'.ofNat 105 *
            (lowerSixQPower (k + 3) 4 * M0) := by
      refine Q'.eqv_trans _
        (Q'.ofNat 105 * ((D * (D * (D * D))) * M0)) _ ?_ ?_
      · summation_ring
      · exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hpow))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by summation_ring))
      (Q'.le_trans' _ _ _ h2m (Q'.le_of_eqv hright))
  exact Q'.le_trans' _ _ _ hstep8
    (Q'.le_trans' _ _ _ hstep6
      (Q'.le_trans' _ _ _ hstep4 hstep2))

#print axioms lowerSixQPower_increment_le_one
#print axioms lowerSixQPower_increment_le_three
#print axioms lowerSixQPower_increment_le_five
#print axioms lowerSixQPower_increment_le_seven
#print axioms lowerSixNextGaussianMoment_nonnegative
#print axioms lowerSixNextGaussianDifferenceMoment_one_le
#print axioms lowerSixNextGaussianDifferenceMoment_three_le
#print axioms lowerSixNextGaussianDifferenceMoment_five_le
#print axioms lowerSixNextGaussianDifferenceMoment_seven_le
#print axioms lowerSixGaussianMoment_two_recurrence
#print axioms lowerSixGaussianMoment_four_recurrence
#print axioms lowerSixGaussianMoment_six_recurrence
#print axioms lowerSixGaussianMoment_eight_recurrence
#print axioms lowerSixGaussianMoment_eight_divisionFree

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentSummation
