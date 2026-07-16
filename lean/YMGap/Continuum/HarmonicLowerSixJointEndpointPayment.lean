import YMGap.Continuum.HarmonicLowerSixSecondFluxSign
import YMGap.Continuum.HarmonicLowerSixFirstBlockGeometric
import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCenterBands
import YMGap.Continuum.HarmonicThetaLinearCarrier
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope

namespace YMGap.Continuum.HarmonicLowerSixJointEndpointPayment

set_option maxHeartbeats 1000000
set_option maxRecDepth 15000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicLowerSixFirstBlockGeometric
open YMGap.Continuum.HarmonicLowerSixSecondFluxSign
open YMGap.Continuum.HarmonicLowerSixSquareRootBlockTail
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCenterBands
open YMGap.Continuum.HarmonicThetaLinearCarrier
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

/-! A second-order reciprocal-Bernoulli denominator.  Its quadratic
coefficient is defined by the Pascal recurrence, avoiding division by two. -/

def lowerSixQuadraticBernoulliCoeff : Nat → Nat
  | 0 => 0
  | n + 1 => lowerSixQuadraticBernoulliCoeff n + (n + 1)

def lowerSixQuadraticBernoulliDen (u : Q') (n : Nat) : Q' :=
  (1 : Q') + Q'.ofNat n * u +
    Q'.ofNat (lowerSixQuadraticBernoulliCoeff n) * (u * u)

private abbrev JointPE := RingNormaliser.PolyExpr

private def pQuadraticBernoulliStepL : JointPE :=
  let u : JointPE := .var 0
  let n : JointPE := .var 1
  let c : JointPE := .var 2
  let one : JointPE := .const 1
  let np : JointPE := .add n one
  let cp : JointPE := .add c np
  .add
    (.mul (.add one (.neg u))
      (.add (.add one (.mul np u)) (.mul cp (.mul u u))))
    (.mul cp (.mul (.mul u u) u))

private def pQuadraticBernoulliStepR : JointPE :=
  let u : JointPE := .var 0
  let n : JointPE := .var 1
  let c : JointPE := .var 2
  .add (.add (.const 1) (.mul n u)) (.mul c (.mul u u))

private theorem pQuadraticBernoulliStep_normal :
    RingNormaliser.normalize pQuadraticBernoulliStepL =
      RingNormaliser.normalize pQuadraticBernoulliStepR := by decide

private theorem quadraticBernoulliStep_algebra (u n c : Q') :
    ((1 : Q') + -u) *
          ((1 : Q') + (n + 1) * u + (c + (n + 1)) * (u * u)) +
        (c + (n + 1)) * ((u * u) * u) ≈
      (1 : Q') + n * u + c * (u * u) := by
  simpa [pQuadraticBernoulliStepL, pQuadraticBernoulliStepR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pQuadraticBernoulliStepL pQuadraticBernoulliStepR
      pQuadraticBernoulliStep_normal
      (fun | 0 => u | 1 => n | _ => c))

private def pQuadraticBernoulliBaseL : JointPE :=
  .mul (.const 1)
    (.add
      (.add (.const 1) (.mul (.const 0) (.var 0)))
      (.mul (.const 0) (.mul (.var 0) (.var 0))))

private theorem pQuadraticBernoulliBase_normal :
    RingNormaliser.normalize pQuadraticBernoulliBaseL =
      RingNormaliser.normalize (.const 1) := by decide

private theorem quadraticBernoulliBase_algebra (u : Q') :
    (1 : Q') *
        ((1 : Q') + Q'.ofNat 0 * u + Q'.ofNat 0 * (u * u)) ≈
      (1 : Q') := by
  simpa [pQuadraticBernoulliBaseL, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pQuadraticBernoulliBaseL (.const 1)
      pQuadraticBernoulliBase_normal (fun _ => u))

theorem lowerSixQuadraticBernoulli_step (u : Q') (n : Nat) :
    ((1 : Q') + -u) * lowerSixQuadraticBernoulliDen u (n + 1) +
        Q'.ofNat (lowerSixQuadraticBernoulliCoeff (n + 1)) *
          ((u * u) * u) ≈
      lowerSixQuadraticBernoulliDen u n := by
  unfold lowerSixQuadraticBernoulliDen
  rw [lowerSixQuadraticBernoulliCoeff]
  have hn : Q'.ofNat (n + 1) ≈ Q'.ofNat n + (1 : Q') := by
    exact Q'.ofNat_add_eqv n 1
  have hc : Q'.ofNat (lowerSixQuadraticBernoulliCoeff n + (n + 1)) ≈
      Q'.ofNat (lowerSixQuadraticBernoulliCoeff n) +
        (Q'.ofNat n + (1 : Q')) := by
    exact Q'.eqv_trans _ _ _
      (Q'.ofNat_add_eqv _ _)
      (Q'.add_eqv_congr_left _ _ _ hn)
  let N := Q'.ofNat n
  let C := Q'.ofNat (lowerSixQuadraticBernoulliCoeff n)
  have hden :
      (1 : Q') + Q'.ofNat (n + 1) * u +
          Q'.ofNat (lowerSixQuadraticBernoulliCoeff n + (n + 1)) * (u * u) ≈
        (1 : Q') + (N + 1) * u + (C + (N + 1)) * (u * u) := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left (1 : Q') _ _
        (Q'.mul_eqv_congr_right _ _ u hn))
      (Q'.mul_eqv_congr_right _ _ (u * u) hc)
  have hslack :
      Q'.ofNat (lowerSixQuadraticBernoulliCoeff n + (n + 1)) *
          ((u * u) * u) ≈
        (C + (N + 1)) * ((u * u) * u) :=
    Q'.mul_eqv_congr_right _ _ _ hc
  have hlhs := Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left ((1 : Q') + -u) _ _ hden) hslack
  exact Q'.eqv_trans _ _ _ hlhs (quadraticBernoulliStep_algebra u N C)

theorem lowerSixQuadraticBernoulli_cleared
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) : ∀ n,
    qpow ((1 : Q') + -u) n * lowerSixQuadraticBernoulliDen u n ≤
      (1 : Q')
  | 0 => by
      unfold lowerSixQuadraticBernoulliDen lowerSixQuadraticBernoulliCoeff qpow
      exact Q'.le_of_eqv (quadraticBernoulliBase_algebra u)
  | n + 1 => by
      have hw0 : (0 : Q') ≤ (1 : Q') + -u := Q'.sub_nonneg_of_le hu1
      have hcoef0 : (0 : Q') ≤
          Q'.ofNat (lowerSixQuadraticBernoulliCoeff (n + 1)) :=
        HeatKernelRGStep.zero_le_ofNat _
      have hu2 : (0 : Q') ≤ u * u := Q'.mul_nonneg _ _ hu0 hu0
      have hu3 : (0 : Q') ≤ (u * u) * u := Q'.mul_nonneg _ _ hu2 hu0
      have hslack0 : (0 : Q') ≤
          Q'.ofNat (lowerSixQuadraticBernoulliCoeff (n + 1)) *
            ((u * u) * u) := Q'.mul_nonneg _ _ hcoef0 hu3
      have hstep : ((1 : Q') + -u) *
            lowerSixQuadraticBernoulliDen u (n + 1) ≤
          lowerSixQuadraticBernoulliDen u n := by
        have hadd := Q'.add_le_self_of_nonneg
          (((1 : Q') + -u) * lowerSixQuadraticBernoulliDen u (n + 1))
          _ hslack0
        exact Q'.le_trans' _ _ _ hadd
          (Q'.le_of_eqv (lowerSixQuadraticBernoulli_step u n))
      have hpow0 : (0 : Q') ≤ qpow ((1 : Q') + -u) n :=
        qpow_nonneg _ hw0 _
      have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ hstep hpow0
      have hnormal :
          qpow ((1 : Q') + -u) (n + 1) *
              lowerSixQuadraticBernoulliDen u (n + 1) ≈
            qpow ((1 : Q') + -u) n *
              (((1 : Q') + -u) *
                lowerSixQuadraticBernoulliDen u (n + 1)) := by
        change (qpow ((1 : Q') + -u) n * ((1 : Q') + -u)) *
            lowerSixQuadraticBernoulliDen u (n + 1) ≈ _
        exact Q'.mul_assoc_eqv _ _ _
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hnormal)
        (Q'.le_trans' _ _ _ hmul
          (lowerSixQuadraticBernoulli_cleared hu0 hu1 n))

/-- The quadratic reciprocal-Bernoulli denominator clears the exact
lower-six Gaussian mode weight. -/
theorem lowerSixModeWeight_mul_quadraticBernoulliDen_le_one
    (k n : Nat) :
    lowerSixModeWeight k n *
        lowerSixQuadraticBernoulliDen (harmU k) (2 * (n * n)) ≤
      (1 : Q') := by
  let e := n * n
  let q := 2 * e
  let B := lowerSixQuadraticBernoulliDen (harmU k) q
  have hweight : lowerSixModeWeight k n ≈ qpow (harmW k) q := by
    refine Q'.eqv_trans _ (qpow (harmW k) e * qpow (harmW k) e) _ ?_ ?_
    · unfold lowerSixModeWeight
      dsimp only [e]
      exact FusionQuotientCollapse.qpow_mul_self (harmW k) (n * n)
    · have hadd := Q'.eqv_symm (HeatKernelRGStep.qpow_add (harmW k) e e)
      have hq : e + e = q := by dsimp only [q]; omega
      rw [hq] at hadd
      exact hadd
  have hbern := lowerSixQuadraticBernoulli_cleared
    (harmU_nonneg k) (harmU_le_one k) q
  have hbase : ((1 : Q') + -harmU k) = harmW k := by
    rfl
  rw [hbase] at hbern
  have hscaled : lowerSixModeWeight k n * B ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ B hweight)) hbern
  dsimp only [B, q, e] at hscaled ⊢
  exact hscaled

/-! Positivity reflection for the center-band polynomial certificate. -/

private theorem jointEvalMonoFrom_nonnegative
  (rho : Nat → Q') (hrho : ∀ i, (0 : Q') ≤ rho i) :
    ∀ i m, (0 : Q') ≤ RingNormaliser.evalMonoFrom rho i m
  | _, [] => by
      change (0 : Q') ≤ (1 : Q')
      decide
  | i, e :: es => by
      exact Q'.mul_nonneg _ _
        (ringQpow_nonnegative (hrho i) e)
        (jointEvalMonoFrom_nonnegative rho hrho (i + 1) es)

private theorem jointOfInt_nonnegative {c : Int} (hc : (0 : Int) ≤ c) :
    (0 : Q') ≤ Q'.ofInt c := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact hc

private theorem jointEvalRaw_nonnegative
    (rho : Nat → Q') (hrho : ∀ i, (0 : Q') ≤ rho i) :
    ∀ p : RingNormaliser.RawPoly,
      (∀ mc, mc ∈ p → (0 : Int) ≤ mc.2) →
      (0 : Q') ≤ RingNormaliser.evalRaw rho p
  | [], _ => Q'.le_refl' 0
  | (m, c) :: p, hcoeff => by
      have hc : (0 : Int) ≤ c := hcoeff (m, c) (by simp)
      have hp : ∀ mc, mc ∈ p → (0 : Int) ≤ mc.2 := by
        intro mc hmc
        exact hcoeff mc (by simp [hmc])
      exact Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (jointOfInt_nonnegative hc)
          (jointEvalMonoFrom_nonnegative rho hrho 0 m))
        (jointEvalRaw_nonnegative rho hrho p hp)

private theorem jointNormalizedExpr_nonnegative
    (e : JointPE) (rho : Nat → Q') (hrho : ∀ i, (0 : Q') ≤ rho i)
    (hcoeff : ∀ mc, mc ∈ RingNormaliser.normalize e →
      (0 : Int) ≤ mc.2) :
    (0 : Q') ≤ RingNormaliser.eval rho e := by
  have hraw := jointEvalRaw_nonnegative rho hrho
    (RingNormaliser.normalize e) hcoeff
  exact Q'.le_trans' _ _ _ hraw
    (Q'.ge_of_eqv (RingNormaliser.normalize_eval rho e))

private def jointSubstituteAll (s : JointPE) : JointPE → JointPE
  | .const c => .const c
  | .var _ => s
  | .add a b => .add (jointSubstituteAll s a) (jointSubstituteAll s b)
  | .mul a b => .mul (jointSubstituteAll s a) (jointSubstituteAll s b)
  | .neg a => .neg (jointSubstituteAll s a)
  | .pow a n => .pow (jointSubstituteAll s a) n

private theorem jointEval_substituteAll (rho : Nat → Q') (s : JointPE) : ∀ e,
    RingNormaliser.eval rho (jointSubstituteAll s e) ≈
      RingNormaliser.eval (fun _ => RingNormaliser.eval rho s) e
  | .const _ => Q'.eqv_refl _
  | .var _ => Q'.eqv_refl _
  | .add a b => Q'.add_eqv_congr'
      (jointEval_substituteAll rho s a) (jointEval_substituteAll rho s b)
  | .mul a b => by
      exact Q'.eqv_trans _
        (RingNormaliser.eval (fun _ => RingNormaliser.eval rho s) a *
          RingNormaliser.eval rho (jointSubstituteAll s b)) _
        (Q'.mul_eqv_congr_right _ _ _ (jointEval_substituteAll rho s a))
        (Q'.mul_eqv_congr_left _ _ _ (jointEval_substituteAll rho s b))
  | .neg a => Q'.neg_eqv_congr _ _ (jointEval_substituteAll rho s a)
  | .pow a n => RingNormaliser.qpow_eqv_congr
      (jointEval_substituteAll rho s a) n

private theorem jointQpow_eqv_congr {a b : Q'} (h : a ≈ b) : ∀ n,
    RingNormaliser.qpow a n ≈ RingNormaliser.qpow b n
  | 0 => Q'.eqv_refl _
  | n + 1 => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (jointQpow_eqv_congr h n))
      (Q'.mul_eqv_congr_left _ _ _ h)

private theorem jointEval_eqv_congr
    (rho sigma : Nat → Q') (h : ∀ i, rho i ≈ sigma i) : ∀ e : JointPE,
    RingNormaliser.eval rho e ≈ RingNormaliser.eval sigma e
  | .const _ => Q'.eqv_refl _
  | .var i => h i
  | .add a b => Q'.add_eqv_congr'
      (jointEval_eqv_congr rho sigma h a)
      (jointEval_eqv_congr rho sigma h b)
  | .mul a b => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (jointEval_eqv_congr rho sigma h a))
      (Q'.mul_eqv_congr_left _ _ _
        (jointEval_eqv_congr rho sigma h b))
  | .neg a => Q'.neg_eqv_congr _ _
      (jointEval_eqv_congr rho sigma h a)
  | .pow a n => jointQpow_eqv_congr
      (jointEval_eqv_congr rho sigma h a) n

private theorem jointOfNat_mul_eqv (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a * b)).den : Int) = 1 := rfl
  show ((a * b : Nat) : Int) *
      ((Q'.ofNat a * Q'.ofNat b).den : Int) =
    (((a : Nat) : Int) * ((b : Nat) : Int)) *
      ((Q'.ofNat (a * b)).den : Int)
  rw [hd1, hd2]
  push_cast
  rfl

private theorem jointQpow_two_ofNat (m : Nat) :
    RingNormaliser.qpow (Q'.ofNat m) 2 ≈ Q'.ofNat (m * m) := by
  refine Q'.eqv_trans _ (Q'.ofNat m * Q'.ofNat m) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)
  · exact Q'.eqv_symm (jointOfNat_mul_eqv m m)

private theorem jointEvenBandD_eqv
    {mq : Q'} {m r : Nat} (hm : mq ≈ Q'.ofNat m) :
    Q'.ofNat 2 * RingNormaliser.qpow mq 2 + Q'.ofNat r ≈
      Q'.ofNat (2 * m * m + r) := by
  have hp := jointQpow_eqv_congr hm 2
  have hsq : RingNormaliser.qpow mq 2 ≈ Q'.ofNat (m * m) :=
    Q'.eqv_trans _ _ _ hp (jointQpow_two_ofNat m)
  have htwo : Q'.ofNat 2 * RingNormaliser.qpow mq 2 ≈
      Q'.ofNat (2 * m * m) := by
    refine Q'.eqv_trans _ (Q'.ofNat 2 * Q'.ofNat (m * m)) _
      (Q'.mul_eqv_congr_left _ _ _ hsq) ?_
    have hcast := jointOfNat_mul_eqv 2 (m * m)
    rw [← Nat.mul_assoc] at hcast
    exact Q'.eqv_symm hcast
  exact Q'.eqv_trans _
    (Q'.ofNat (2 * m * m) + Q'.ofNat r) _
    (Q'.add_eqv_congr_right _ _ _ htwo)
    (Q'.eqv_symm (Q'.ofNat_add_eqv _ _))

private theorem jointOddBandD_eqv
    {mq : Q'} {m r : Nat} (hm : mq ≈ Q'.ofNat m) :
    Q'.ofNat 2 * (mq * (mq + Q'.ofNat 1)) + Q'.ofNat r ≈
      Q'.ofNat (2 * m * (m + 1) + r) := by
  have hm1 : mq + Q'.ofNat 1 ≈ Q'.ofNat (m + 1) := by
    exact Q'.eqv_trans _ (Q'.ofNat m + Q'.ofNat 1) _
      (Q'.add_eqv_congr_right _ _ _ hm)
      (Q'.eqv_symm (Q'.ofNat_add_eqv m 1))
  have hprod : mq * (mq + Q'.ofNat 1) ≈
      Q'.ofNat (m * (m + 1)) := by
    refine Q'.eqv_trans _ (Q'.ofNat m * Q'.ofNat (m + 1)) _ ?_ ?_
    · exact Q'.eqv_trans _
        (Q'.ofNat m * (mq + Q'.ofNat 1)) _
        (Q'.mul_eqv_congr_right _ _ _ hm)
        (Q'.mul_eqv_congr_left _ _ _ hm1)
    · exact Q'.eqv_symm (jointOfNat_mul_eqv m (m + 1))
  have htwo : Q'.ofNat 2 * (mq * (mq + Q'.ofNat 1)) ≈
      Q'.ofNat (2 * m * (m + 1)) := by
    refine Q'.eqv_trans _
      (Q'.ofNat 2 * Q'.ofNat (m * (m + 1))) _
      (Q'.mul_eqv_congr_left _ _ _ hprod) ?_
    have hcast := jointOfNat_mul_eqv 2 (m * (m + 1))
    rw [← Nat.mul_assoc] at hcast
    exact Q'.eqv_symm hcast
  exact Q'.eqv_trans _
    (Q'.ofNat (2 * m * (m + 1)) + Q'.ofNat r) _
    (Q'.add_eqv_congr_right _ _ _ htwo)
    (Q'.eqv_symm (Q'.ofNat_add_eqv _ _))

private def pJointDefectClearL : JointPE :=
  let D : JointPE := .var 0
  let u : JointPE := .var 1
  let w := .add (.const 1) (.neg u)
  .mul (.pow D 2) (.add (.const 1) (.neg (.mul w w)))

private def pJointDefectClearR : JointPE :=
  let D : JointPE := .var 0
  let u : JointPE := .var 1
  let x := .mul D u
  .mul x (.add (.mul (.const 2) D) (.neg x))

private theorem pJointDefectClear_normal :
    RingNormaliser.normalize pJointDefectClearL =
      RingNormaliser.normalize pJointDefectClearR := by decide

private theorem jointDefectClear_algebra (D u : Q') :
    RingNormaliser.qpow D 2 *
        ((1 : Q') + -(((1 : Q') + -u) * ((1 : Q') + -u))) ≈
      (D * u) * (Q'.ofNat 2 * D + -(D * u)) := by
  simpa [pJointDefectClearL, pJointDefectClearR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pJointDefectClearL pJointDefectClearR
      pJointDefectClear_normal (fun | 0 => D | _ => u))

private theorem lowerSixHarmonicSquareDefect_cleared (k : Nat) :
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 *
        ((1 : Q') + -(harmW k * harmW k)) ≈
      Q'.ofNat 2 * Q'.ofNat (k + 2) + -(1 : Q') := by
  let D := Q'.ofNat (k + 2)
  let u := harmU k
  let x := D * u
  have hdu : x ≈ (1 : Q') := by
    dsimp only [x, D, u]
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (harmonicUnit_mul_den k)
  have hinner : Q'.ofNat 2 * D + -x ≈
      Q'.ofNat 2 * D + -(1 : Q') :=
    Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hdu)
  have hright : x * (Q'.ofNat 2 * D + -x) ≈
      Q'.ofNat 2 * D + -(1 : Q') := by
    refine Q'.eqv_trans _
      ((1 : Q') * (Q'.ofNat 2 * D + -x)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hdu
    · exact Q'.eqv_trans _
        ((1 : Q') * (Q'.ofNat 2 * D + -(1 : Q'))) _
        (Q'.mul_eqv_congr_left _ _ _ hinner)
        (Q'.one_mul_eqv _)
  have halg := jointDefectClear_algebra D u
  unfold harmW ReciprocalBernoulliUpper.oneSub
  dsimp only [D, u, x] at halg hright ⊢
  exact Q'.eqv_trans _ _ _ halg hright

/-! A linear-cost Horner translation engine.  This avoids exponentially
expanding `(t+14)^n` inside the reflective normalizer. -/

private def jointCoeffAdd : List Int → List Int → List Int
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: jointCoeffAdd as bs

private def jointCoeffScale (c : Int) : List Int → List Int
  | [] => []
  | a :: as => (c * a) :: jointCoeffScale c as

private def jointCoeffShift (c : Int) : List Int → List Int
  | [] => []
  | a :: as =>
      let bs := jointCoeffShift c as
      jointCoeffAdd [a]
        (jointCoeffAdd (jointCoeffScale c bs) (0 :: bs))

private def jointHornerEval : List Int → Q' → Q'
  | [], _ => 0
  | a :: as, x => Q'.ofInt a + x * jointHornerEval as x

private theorem jointHornerAdd_algebra (a b x A B : Q') :
    (a + b) + x * (A + B) ≈ (a + x * A) + (b + x * B) := by
  ring_qeqv

private theorem jointHornerEval_add (x : Q') : ∀ as bs,
    jointHornerEval (jointCoeffAdd as bs) x ≈
      jointHornerEval as x + jointHornerEval bs x
  | [], bs => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | as, [] => by
      cases as with
      | nil => exact Q'.eqv_symm (QPoly.q_add_zero_eqv _)
      | cons a as => exact Q'.eqv_symm (QPoly.q_add_zero_eqv _)
  | a :: as, b :: bs => by
      have ih := jointHornerEval_add x as bs
      change Q'.ofInt (a + b) +
          x * jointHornerEval (jointCoeffAdd as bs) x ≈
        (Q'.ofInt a + x * jointHornerEval as x) +
          (Q'.ofInt b + x * jointHornerEval bs x)
      refine Q'.eqv_trans _
        ((Q'.ofInt a + Q'.ofInt b) +
          x * (jointHornerEval as x + jointHornerEval bs x)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (RingNormaliser.ofInt_add a b)
          (Q'.mul_eqv_congr_left x _ _ ih)
      · exact jointHornerAdd_algebra _ _ _ _ _

private theorem jointHornerScale_algebra (c a x T : Q') :
    c * a + x * (c * T) ≈ c * (a + x * T) := by
  ring_qeqv

private theorem jointHornerEval_scale (c : Int) (x : Q') : ∀ as,
    jointHornerEval (jointCoeffScale c as) x ≈
      Q'.ofInt c * jointHornerEval as x
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | a :: as => by
      have ih := jointHornerEval_scale c x as
      change Q'.ofInt (c * a) +
          x * jointHornerEval (jointCoeffScale c as) x ≈
        Q'.ofInt c * (Q'.ofInt a + x * jointHornerEval as x)
      refine Q'.eqv_trans _
        (Q'.ofInt c * Q'.ofInt a +
          x * (Q'.ofInt c * jointHornerEval as x)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (RingNormaliser.ofInt_mul c a)
          (Q'.mul_eqv_congr_left x _ _ ih)
      · exact jointHornerScale_algebra _ _ _ _

private theorem jointHornerTranslate_algebra (a c t B : Q') :
    a + (t + c) * B ≈ (a + c * B) + t * B := by
  ring_qeqv

private theorem jointHornerEval_shift (c : Int) (t : Q') : ∀ as,
    jointHornerEval as (t + Q'.ofInt c) ≈
      jointHornerEval (jointCoeffShift c as) t
  | [] => Q'.eqv_refl _
  | a :: as => by
      let bs := jointCoeffShift c as
      let B := jointHornerEval bs t
      have ih : jointHornerEval as (t + Q'.ofInt c) ≈ B := by
        dsimp only [B, bs]
        exact jointHornerEval_shift c t as
      have hadd1 := jointHornerEval_add t [a]
        (jointCoeffAdd (jointCoeffScale c bs) (0 :: bs))
      have hadd2 := jointHornerEval_add t (jointCoeffScale c bs) (0 :: bs)
      have hscale := jointHornerEval_scale c t bs
      have hzero : jointHornerEval (0 :: bs) t ≈ t * B := by
        dsimp only [jointHornerEval, B]
        refine Q'.eqv_trans _ ((0 : Q') + t * jointHornerEval bs t) _ ?_ ?_
        · exact Q'.add_eqv_congr_right _ _ _ (by decide)
        · exact Q'.eqv_of_eq (Q'.zero_add' _)
      have haeval : jointHornerEval [a] t ≈ Q'.ofInt a := by
        change Q'.ofInt a + t * (0 : Q') ≈ Q'.ofInt a
        exact Q'.eqv_trans _ (Q'.ofInt a + 0) _
          (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv t))
          (QPoly.q_add_zero_eqv _)
      have hinner : jointHornerEval
            (jointCoeffAdd (jointCoeffScale c bs) (0 :: bs)) t ≈
          Q'.ofInt c * B + t * B := by
        refine Q'.eqv_trans _
          (jointHornerEval (jointCoeffScale c bs) t +
            jointHornerEval (0 :: bs) t) _ hadd2 ?_
        dsimp only [B] at hscale hzero ⊢
        exact Q'.add_eqv_congr' hscale hzero
      have hshifted : jointHornerEval (jointCoeffShift c (a :: as)) t ≈
          (Q'.ofInt a + Q'.ofInt c * B) + t * B := by
        dsimp only [jointCoeffShift]
        refine Q'.eqv_trans _
          (jointHornerEval [a] t +
            jointHornerEval
              (jointCoeffAdd (jointCoeffScale c bs) (0 :: bs)) t) _
          hadd1 ?_
        refine Q'.eqv_trans _
          (Q'.ofInt a + (Q'.ofInt c * B + t * B)) _
          (Q'.add_eqv_congr' haeval hinner) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
      refine Q'.eqv_trans _
        (Q'.ofInt a + (t + Q'.ofInt c) * B) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left (t + Q'.ofInt c) _ _ ih)
      refine Q'.eqv_trans _
        ((Q'.ofInt a + Q'.ofInt c * B) + t * B) _
        (jointHornerTranslate_algebra _ _ _ _) ?_
      exact Q'.eqv_symm hshifted

private theorem jointHornerEval_nonnegative
    {x : Q'} (hx : (0 : Q') ≤ x) : ∀ as,
    (∀ c, c ∈ as → (0 : Int) ≤ c) →
    (0 : Q') ≤ jointHornerEval as x
  | [], _ => Q'.le_refl' 0
  | a :: as, hcoeff => by
      have ha : (0 : Int) ≤ a := hcoeff a (by simp)
      have has : ∀ c, c ∈ as → (0 : Int) ≤ c := by
        intro c hc
        exact hcoeff c (by simp [hc])
      exact Q'.zero_le_add _ _ (jointOfInt_nonnegative ha)
        (Q'.mul_nonneg _ _ hx (jointHornerEval_nonnegative hx as has))

private def pJointCoreCleared (D m : JointPE) : JointPE :=
  let one : JointPE := .const 1
  let K := .add m one
  let D2 := .pow D 2
  let D3 := .pow D 3
  let D4 := .pow D 4
  let D6 := .pow D 6
  let K2 := .pow K 2
  let K3 := .pow K 3
  let K5 := .pow K 5
  let K7 := .pow K 7
  let K9 := .pow K 9
  let S := .add (.mul (.const 2) D) (.neg one)
  let mf := .add (.mul (.const 2) m) (.const 3)
  let q := .mul (.const 2) K2
  let c := .mul K2 (.add (.mul (.const 2) K2) one)
  let bern := .add (.add D2 (.mul q D)) c
  let sumSq6 := .mul (.mul m (.add m one))
    (.add (.mul (.const 2) m) one)
  let Y := .add
    (.mul (.const 72)
      (.mul mf (.mul S (.mul D (.mul m D2)))))
    (.neg
      (.mul (.const 12)
        (.mul mf (.mul (.pow S 2) (.mul D sumSq6)))))
  let J :=
    .add
      (.add
        (.add
          (.add
            (.mul (.const 15750) (.mul K D4))
            (.mul (.const 45560) (.mul K3 D3)))
          (.neg (.mul (.const 10976) (.mul K5 D2))))
        (.mul (.const 30848) (.mul K7 D)))
      (.mul (.const 4608) K9)
  .add
    (.add
      (.mul (.const 635) (.mul bern Y))
      (.neg (.mul (.const 508) (.mul mf (.mul S J)))))
    (.neg (.mul (.const 10003200) D6))

private def pJointCoreMF (m : JointPE) : JointPE :=
  .add (.mul (.const 2) m) (.const 3)

private def pJointCoreS (D : JointPE) : JointPE :=
  .add (.mul (.const 2) D) (.neg (.const 1))

private def pJointCoreBern (D m : JointPE) : JointPE :=
  let K := .add m (.const 1)
  let K2 := .pow K 2
  .add (.add (.pow D 2) (.mul (.mul (.const 2) K2) D))
    (.mul K2 (.add (.mul (.const 2) K2) (.const 1)))

private def pJointCoreReserve (D m : JointPE) : JointPE :=
  let S := pJointCoreS D
  let mf := pJointCoreMF m
  let sum6 := .mul (.mul m (.add m (.const 1)))
    (.add (.mul (.const 2) m) (.const 1))
  .add
    (.mul (.const 72)
      (.mul mf (.mul S (.mul D (.mul m (.pow D 2))))))
    (.neg
      (.mul (.const 12)
        (.mul mf (.mul (.pow S 2) (.mul D sum6)))))

private def pJointCoreEndpointPositive (D m : JointPE) : JointPE :=
  let K := .add m (.const 1)
  .add
    (.add
      (.add
        (.add
          (.mul (.const 15750) (.mul K (.pow D 4)))
          (.mul (.const 45560) (.mul (.pow K 3) (.pow D 3))))
        (.neg (.mul (.const 10976) (.mul (.pow K 5) (.pow D 2)))))
      (.mul (.const 30848) (.mul (.pow K 7) D)))
    (.mul (.const 4608) (.pow K 9))

private theorem jointCoreCleared_eval_shape
    (rho : Nat → Q') (D m : JointPE) :
    RingNormaliser.eval rho (pJointCoreCleared D m) ≈
      (Q'.ofNat 635 *
          (RingNormaliser.eval rho (pJointCoreBern D m) *
            RingNormaliser.eval rho (pJointCoreReserve D m)) +
        -(Q'.ofNat 508 *
          (RingNormaliser.eval rho (pJointCoreMF m) *
            (RingNormaliser.eval rho (pJointCoreS D) *
              RingNormaliser.eval rho (pJointCoreEndpointPositive D m))))) +
        -(Q'.ofNat 10003200 *
          RingNormaliser.qpow (RingNormaliser.eval rho D) 6) := by
  dsimp only [pJointCoreCleared, pJointCoreBern, pJointCoreReserve,
    pJointCoreMF, pJointCoreS, pJointCoreEndpointPositive,
    RingNormaliser.eval]
  exact Q'.eqv_refl _

private def pJointUni (cs : List (Nat × Int)) (x : JointPE) : JointPE :=
  cs.foldr (fun ec acc =>
    .add (.mul (.const ec.2) (.pow x ec.1)) acc) (.const 0)

private def pJointA (i : Nat) (m : JointPE) : JointPE :=
  pJointUni (match i with
    | 0 => [(0, 7022592), (1, 67885056), (2, 294948864),
        (3, 758439936), (4, 1278111744), (5, 1474744320),
        (6, 1179795456), (7, 646078464), (8, 231745536),
        (9, 49158144), (10, 4681728)]
    | 1 => [(0, 32967168), (1, 224589340), (2, 616272580),
        (3, 785315676), (4, 183885332), (5, -867484168),
        (6, -1373626920), (7, -1026180320), (8, -432210464),
        (9, -98316288), (10, -9363456)]
    | 2 => [(0, -110752128), (1, -815416200), (2, -2634671896),
        (3, -4880925976), (4, -5671408520), (5, -4232379648),
        (6, -1980549760), (7, -531099776), (8, -62439296)]
    | 3 => [(0, 102888288), (1, 443640972), (2, 790618180),
        (3, 759708920), (4, 427542960), (5, 136345168),
        (6, 17182592), (7, -1706880), (8, -243840)]
    | 4 => [(0, -114863880), (1, -468716360), (2, -676473120),
        (3, -413735520), (4, -90444320), (5, 792480), (6, 121920)]
    | 5 => [(0, -48006000), (1, -79689960), (2, -30967680),
        (3, 914400), (4, 243840)]
    | _ => [(0, -10003200), (1, 274320), (2, 182880)]) m

private def pJointCoreExpanded (D m : JointPE) : JointPE :=
  .add (.add (.add (.add (.add (.add
    (pJointA 0 m)
    (.mul (pJointA 1 m) D))
    (.mul (pJointA 2 m) (.pow D 2)))
    (.mul (pJointA 3 m) (.pow D 3)))
    (.mul (pJointA 4 m) (.pow D 4)))
    (.mul (pJointA 5 m) (.pow D 5)))
    (.mul (pJointA 6 m) (.pow D 6))

/-! A staged coefficient expansion of `pJointCoreCleared`.  The definitions
below retain the natural `m`-dependent blocks, so the seven coefficient
certificates can be normalized independently instead of asking the
reflective normalizer to expand the whole bivariate polynomial at once. -/

private def pJointCoreCoeffStructured (i : Nat) (m : JointPE) : JointPE :=
  let one : JointPE := .const 1
  let K := .add m one
  let K2 := .pow K 2
  let K3 := .pow K 3
  let K5 := .pow K 5
  let K7 := .pow K 7
  let K9 := .pow K 9
  let mf := .add (.mul (.const 2) m) (.const 3)
  let q := .mul (.const 2) K2
  let c := .mul K2 (.add (.mul (.const 2) K2) one)
  let ss := .mul (.mul m (.add m one))
    (.add (.mul (.const 2) m) one)
  let y1 := .neg (.mul (.const 12) ss)
  let y2 := .mul (.const 48) ss
  let y3 := .add (.neg (.mul (.const 72) m))
    (.neg (.mul (.const 48) ss))
  let y4 := .mul (.const 144) m
  let b := match i with
    | 0 => .const 0
    | 1 => .mul c y1
    | 2 => .add (.mul c y2) (.mul q y1)
    | 3 => .add (.add (.mul c y3) (.mul q y2)) y1
    | 4 => .add (.add (.mul c y4) (.mul q y3)) y2
    | 5 => .add (.mul q y4) y3
    | _ => y4
  let j0 := .mul (.const 4608) K9
  let j1 := .mul (.const 30848) K7
  let j2 := .neg (.mul (.const 10976) K5)
  let j3 := .mul (.const 45560) K3
  let j4 := .mul (.const 15750) K
  let s := match i with
    | 0 => .neg j0
    | 1 => .add (.mul (.const 2) j0) (.neg j1)
    | 2 => .add (.mul (.const 2) j1) (.neg j2)
    | 3 => .add (.mul (.const 2) j2) (.neg j3)
    | 4 => .add (.mul (.const 2) j3) (.neg j4)
    | 5 => .mul (.const 2) j4
    | _ => .const 0
  let base := .add
    (.mul (.const 635) (.mul mf b))
    (.neg (.mul (.const 508) (.mul mf s)))
  if i = 6 then .add base (.neg (.const 10003200)) else base

private def pJointCoreStructuredExpanded (D m : JointPE) : JointPE :=
  .add (.add (.add (.add (.add (.add
    (pJointCoreCoeffStructured 0 m)
    (.mul (pJointCoreCoeffStructured 1 m) D))
    (.mul (pJointCoreCoeffStructured 2 m) (.pow D 2)))
    (.mul (pJointCoreCoeffStructured 3 m) (.pow D 3)))
    (.mul (pJointCoreCoeffStructured 4 m) (.pow D 4)))
    (.mul (pJointCoreCoeffStructured 5 m) (.pow D 5)))
    (.mul (pJointCoreCoeffStructured 6 m) (.pow D 6))

private theorem pJointCoreCoeffStructured0_normal :
    RingNormaliser.normalize (pJointCoreCoeffStructured 0 (.var 0)) =
      RingNormaliser.normalize (pJointA 0 (.var 0)) := by decide

private theorem pJointCoreCoeffStructured1_normal :
    RingNormaliser.normalize (pJointCoreCoeffStructured 1 (.var 0)) =
      RingNormaliser.normalize (pJointA 1 (.var 0)) := by decide

private theorem pJointCoreCoeffStructured2_normal :
    RingNormaliser.normalize (pJointCoreCoeffStructured 2 (.var 0)) =
      RingNormaliser.normalize (pJointA 2 (.var 0)) := by decide

private theorem pJointCoreCoeffStructured3_normal :
    RingNormaliser.normalize (pJointCoreCoeffStructured 3 (.var 0)) =
      RingNormaliser.normalize (pJointA 3 (.var 0)) := by decide

private theorem pJointCoreCoeffStructured4_normal :
    RingNormaliser.normalize (pJointCoreCoeffStructured 4 (.var 0)) =
      RingNormaliser.normalize (pJointA 4 (.var 0)) := by decide

private theorem pJointCoreCoeffStructured5_normal :
    RingNormaliser.normalize (pJointCoreCoeffStructured 5 (.var 0)) =
      RingNormaliser.normalize (pJointA 5 (.var 0)) := by decide

private theorem pJointCoreCoeffStructured6_normal :
    RingNormaliser.normalize (pJointCoreCoeffStructured 6 (.var 0)) =
      RingNormaliser.normalize (pJointA 6 (.var 0)) := by decide

/-! The remaining expansion in the scale variable is proved with every
`m`-dependent block represented by an independent atom.  This is the small
generic identity whose instantiation avoids the previous stack overflow. -/

private def pJointCoreStageCoeff (i : Nat) : JointPE :=
  let m : JointPE := .var 1
  let K : JointPE := .var 2
  let mf : JointPE := .var 3
  let q : JointPE := .var 4
  let c : JointPE := .var 5
  let ss : JointPE := .var 6
  let K3 : JointPE := .var 7
  let K5 : JointPE := .var 8
  let K7 : JointPE := .var 9
  let K9 : JointPE := .var 10
  let y1 := .neg (.mul (.const 12) ss)
  let y2 := .mul (.const 48) ss
  let y3 := .add (.neg (.mul (.const 72) m))
    (.neg (.mul (.const 48) ss))
  let y4 := .mul (.const 144) m
  let b := match i with
    | 0 => .const 0
    | 1 => .mul c y1
    | 2 => .add (.mul c y2) (.mul q y1)
    | 3 => .add (.add (.mul c y3) (.mul q y2)) y1
    | 4 => .add (.add (.mul c y4) (.mul q y3)) y2
    | 5 => .add (.mul q y4) y3
    | _ => y4
  let j0 := .mul (.const 4608) K9
  let j1 := .mul (.const 30848) K7
  let j2 := .neg (.mul (.const 10976) K5)
  let j3 := .mul (.const 45560) K3
  let j4 := .mul (.const 15750) K
  let s := match i with
    | 0 => .neg j0
    | 1 => .add (.mul (.const 2) j0) (.neg j1)
    | 2 => .add (.mul (.const 2) j1) (.neg j2)
    | 3 => .add (.mul (.const 2) j2) (.neg j3)
    | 4 => .add (.mul (.const 2) j3) (.neg j4)
    | 5 => .mul (.const 2) j4
    | _ => .const 0
  let base := .add
    (.mul (.const 635) (.mul mf b))
    (.neg (.mul (.const 508) (.mul mf s)))
  if i = 6 then .add base (.neg (.const 10003200)) else base

private def pJointCoreStageOriginal : JointPE :=
  let D : JointPE := .var 0
  let m : JointPE := .var 1
  let K : JointPE := .var 2
  let mf : JointPE := .var 3
  let q : JointPE := .var 4
  let c : JointPE := .var 5
  let ss : JointPE := .var 6
  let K3 : JointPE := .var 7
  let K5 : JointPE := .var 8
  let K7 : JointPE := .var 9
  let K9 : JointPE := .var 10
  let one : JointPE := .const 1
  let S := .add (.mul (.const 2) D) (.neg one)
  let bern := .add (.add (.pow D 2) (.mul q D)) c
  let Y := .add
    (.mul (.const 72)
      (.mul mf (.mul S (.mul D (.mul m (.pow D 2))))))
    (.neg
      (.mul (.const 12)
        (.mul mf (.mul (.pow S 2) (.mul D ss)))))
  let J :=
    .add
      (.add
        (.add
          (.add
            (.mul (.const 15750) (.mul K (.pow D 4)))
            (.mul (.const 45560) (.mul K3 (.pow D 3))))
          (.neg (.mul (.const 10976) (.mul K5 (.pow D 2)))))
        (.mul (.const 30848) (.mul K7 D)))
      (.mul (.const 4608) K9)
  .add
    (.add
      (.mul (.const 635) (.mul bern Y))
      (.neg (.mul (.const 508) (.mul mf (.mul S J)))))
    (.neg (.mul (.const 10003200) (.pow D 6)))

private def pJointCoreStageExpanded : JointPE :=
  let D : JointPE := .var 0
  .add (.add (.add (.add (.add (.add
    (pJointCoreStageCoeff 0)
    (.mul (pJointCoreStageCoeff 1) D))
    (.mul (pJointCoreStageCoeff 2) (.pow D 2)))
    (.mul (pJointCoreStageCoeff 3) (.pow D 3)))
    (.mul (pJointCoreStageCoeff 4) (.pow D 4)))
    (.mul (pJointCoreStageCoeff 5) (.pow D 5)))
    (.mul (pJointCoreStageCoeff 6) (.pow D 6))

private theorem pJointCoreStage_normal :
    RingNormaliser.normalize pJointCoreStageOriginal =
      RingNormaliser.normalize pJointCoreStageExpanded := by decide

private theorem jointCoreCleared_eqv_structuredExpanded
    (rho : Nat → Q') (D m : JointPE) :
    RingNormaliser.eval rho (pJointCoreCleared D m) ≈
      RingNormaliser.eval rho (pJointCoreStructuredExpanded D m) := by
  let one : JointPE := .const 1
  let K : JointPE := .add m one
  let K2 : JointPE := .pow K 2
  let mf : JointPE := .add (.mul (.const 2) m) (.const 3)
  let q : JointPE := .mul (.const 2) K2
  let c : JointPE := .mul K2 (.add (.mul (.const 2) K2) one)
  let ss : JointPE := .mul (.mul m (.add m one))
    (.add (.mul (.const 2) m) one)
  let sigma : Nat → Q' := fun
    | 0 => RingNormaliser.eval rho D
    | 1 => RingNormaliser.eval rho m
    | 2 => RingNormaliser.eval rho K
    | 3 => RingNormaliser.eval rho mf
    | 4 => RingNormaliser.eval rho q
    | 5 => RingNormaliser.eval rho c
    | 6 => RingNormaliser.eval rho ss
    | 7 => RingNormaliser.eval rho (.pow K 3)
    | 8 => RingNormaliser.eval rho (.pow K 5)
    | 9 => RingNormaliser.eval rho (.pow K 7)
    | _ => RingNormaliser.eval rho (.pow K 9)
  simpa [pJointCoreStageOriginal, pJointCoreStageExpanded,
    pJointCoreStageCoeff, pJointCoreCleared,
    pJointCoreStructuredExpanded, pJointCoreCoeffStructured,
    RingNormaliser.eval, sigma, ss, c, q, mf, K2, K, one] using
    (RingNormaliser.poly_identity_of_normal_eq
      pJointCoreStageOriginal pJointCoreStageExpanded
      pJointCoreStage_normal sigma)

private theorem jointCoreCoeffStructured_eqv_A
    (rho : Nat → Q') (m : JointPE) (i : Nat) (hi : i ≤ 6) :
    RingNormaliser.eval rho (pJointCoreCoeffStructured i m) ≈
      RingNormaliser.eval rho (pJointA i m) := by
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 := by omega
  have hn :
      RingNormaliser.normalize (pJointCoreCoeffStructured i (.var 0)) =
        RingNormaliser.normalize (pJointA i (.var 0)) := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pJointCoreCoeffStructured0_normal
    · exact pJointCoreCoeffStructured1_normal
    · exact pJointCoreCoeffStructured2_normal
    · exact pJointCoreCoeffStructured3_normal
    · exact pJointCoreCoeffStructured4_normal
    · exact pJointCoreCoeffStructured5_normal
    · exact pJointCoreCoeffStructured6_normal
  have hid := RingNormaliser.poly_identity_of_normal_eq
    (pJointCoreCoeffStructured i (.var 0)) (pJointA i (.var 0))
    hn (fun _ => RingNormaliser.eval rho m)
  have hl := jointEval_substituteAll rho m
    (pJointCoreCoeffStructured i (.var 0))
  have hr := jointEval_substituteAll rho m (pJointA i (.var 0))
  have hsynl :
      jointSubstituteAll m (pJointCoreCoeffStructured i (.var 0)) =
        pJointCoreCoeffStructured i m := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hsynr : jointSubstituteAll m (pJointA i (.var 0)) =
      pJointA i m := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hsynl] at hl
  rw [hsynr] at hr
  exact Q'.eqv_trans _ _ _ hl
    (Q'.eqv_trans _ _ _ hid (Q'.eqv_symm hr))

private theorem jointCoreStructuredExpanded_eqv_coreExpanded
    (rho : Nat → Q') (D m : JointPE) :
    RingNormaliser.eval rho (pJointCoreStructuredExpanded D m) ≈
      RingNormaliser.eval rho (pJointCoreExpanded D m) := by
  have h0 := jointCoreCoeffStructured_eqv_A rho m 0 (by omega)
  have h1 := jointCoreCoeffStructured_eqv_A rho m 1 (by omega)
  have h2 := jointCoreCoeffStructured_eqv_A rho m 2 (by omega)
  have h3 := jointCoreCoeffStructured_eqv_A rho m 3 (by omega)
  have h4 := jointCoreCoeffStructured_eqv_A rho m 4 (by omega)
  have h5 := jointCoreCoeffStructured_eqv_A rho m 5 (by omega)
  have h6 := jointCoreCoeffStructured_eqv_A rho m 6 (by omega)
  dsimp only [pJointCoreStructuredExpanded, pJointCoreExpanded,
    RingNormaliser.eval]
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr' h0
              (Q'.mul_eqv_congr_right _ _ _ h1))
            (Q'.mul_eqv_congr_right _ _ _ h2))
          (Q'.mul_eqv_congr_right _ _ _ h3))
        (Q'.mul_eqv_congr_right _ _ _ h4))
      (Q'.mul_eqv_congr_right _ _ _ h5))
    (Q'.mul_eqv_congr_right _ _ _ h6)

private theorem jointCoreCleared_eqv_coreExpanded
    (rho : Nat → Q') (D m : JointPE) :
    RingNormaliser.eval rho (pJointCoreCleared D m) ≈
      RingNormaliser.eval rho (pJointCoreExpanded D m) :=
  Q'.eqv_trans _ _ _
    (jointCoreCleared_eqv_structuredExpanded rho D m)
    (jointCoreStructuredExpanded_eqv_coreExpanded rho D m)

private def pJointBandCoeff (j : Nat) (B m : JointPE) : JointPE :=
  match j with
  | 0 => .add (.add (.add (.add (.add (.add
      (pJointA 0 m)
      (.mul (pJointA 1 m) B))
      (.mul (pJointA 2 m) (.pow B 2)))
      (.mul (pJointA 3 m) (.pow B 3)))
      (.mul (pJointA 4 m) (.pow B 4)))
      (.mul (pJointA 5 m) (.pow B 5)))
      (.mul (pJointA 6 m) (.pow B 6))
  | 1 => .add (.add (.add (.add (.add
      (pJointA 1 m)
      (.mul (.const 2) (.mul (pJointA 2 m) B)))
      (.mul (.const 3) (.mul (pJointA 3 m) (.pow B 2))))
      (.mul (.const 4) (.mul (pJointA 4 m) (.pow B 3))))
      (.mul (.const 5) (.mul (pJointA 5 m) (.pow B 4))))
      (.mul (.const 6) (.mul (pJointA 6 m) (.pow B 5)))
  | 2 => .add (.add (.add (.add
      (pJointA 2 m)
      (.mul (.const 3) (.mul (pJointA 3 m) B)))
      (.mul (.const 6) (.mul (pJointA 4 m) (.pow B 2))))
      (.mul (.const 10) (.mul (pJointA 5 m) (.pow B 3))))
      (.mul (.const 15) (.mul (pJointA 6 m) (.pow B 4)))
  | 3 => .add (.add (.add
      (pJointA 3 m)
      (.mul (.const 4) (.mul (pJointA 4 m) B)))
      (.mul (.const 10) (.mul (pJointA 5 m) (.pow B 2))))
      (.mul (.const 20) (.mul (pJointA 6 m) (.pow B 3)))
  | 4 => .add (.add
      (pJointA 4 m)
      (.mul (.const 5) (.mul (pJointA 5 m) B)))
      (.mul (.const 15) (.mul (pJointA 6 m) (.pow B 2)))
  | 5 => .add (pJointA 5 m)
      (.mul (.const 6) (.mul (pJointA 6 m) B))
  | _ => pJointA 6 m

private def pJointBandExpanded (B m r : JointPE) : JointPE :=
  .add (.add (.add (.add (.add (.add
    (pJointBandCoeff 0 B m)
    (.mul (pJointBandCoeff 1 B m) r))
    (.mul (pJointBandCoeff 2 B m) (.pow r 2)))
    (.mul (pJointBandCoeff 3 B m) (.pow r 3)))
    (.mul (pJointBandCoeff 4 B m) (.pow r 4)))
    (.mul (pJointBandCoeff 5 B m) (.pow r 5)))
    (.mul (pJointBandCoeff 6 B m) (.pow r 6))

/-! The degree-six binomial recombination is certified once with abstract
coefficients.  Keeping the seven `A_i` atomic prevents the reflective
normalizer from expanding the large concrete coefficient polynomials. -/

private def pJointGenericBandCoeff (j : Nat) : JointPE :=
  let A := fun i => (.var i : JointPE)
  let B : JointPE := .var 7
  match j with
  | 0 => .add (.add (.add (.add (.add (.add
      (A 0)
      (.mul (A 1) B))
      (.mul (A 2) (.pow B 2)))
      (.mul (A 3) (.pow B 3)))
      (.mul (A 4) (.pow B 4)))
      (.mul (A 5) (.pow B 5)))
      (.mul (A 6) (.pow B 6))
  | 1 => .add (.add (.add (.add (.add
      (A 1)
      (.mul (.const 2) (.mul (A 2) B)))
      (.mul (.const 3) (.mul (A 3) (.pow B 2))))
      (.mul (.const 4) (.mul (A 4) (.pow B 3))))
      (.mul (.const 5) (.mul (A 5) (.pow B 4))))
      (.mul (.const 6) (.mul (A 6) (.pow B 5)))
  | 2 => .add (.add (.add (.add
      (A 2)
      (.mul (.const 3) (.mul (A 3) B)))
      (.mul (.const 6) (.mul (A 4) (.pow B 2))))
      (.mul (.const 10) (.mul (A 5) (.pow B 3))))
      (.mul (.const 15) (.mul (A 6) (.pow B 4)))
  | 3 => .add (.add (.add
      (A 3)
      (.mul (.const 4) (.mul (A 4) B)))
      (.mul (.const 10) (.mul (A 5) (.pow B 2))))
      (.mul (.const 20) (.mul (A 6) (.pow B 3)))
  | 4 => .add (.add
      (A 4)
      (.mul (.const 5) (.mul (A 5) B)))
      (.mul (.const 15) (.mul (A 6) (.pow B 2)))
  | 5 => .add (A 5) (.mul (.const 6) (.mul (A 6) B))
  | _ => A 6

private def pJointGenericCore : JointPE :=
  let A := fun i => (.var i : JointPE)
  let D : JointPE := .add (.var 7) (.var 8)
  .add (.add (.add (.add (.add (.add
    (A 0)
    (.mul (A 1) D))
    (.mul (A 2) (.pow D 2)))
    (.mul (A 3) (.pow D 3)))
    (.mul (A 4) (.pow D 4)))
    (.mul (A 5) (.pow D 5)))
    (.mul (A 6) (.pow D 6))

private def pJointGenericBand : JointPE :=
  let r : JointPE := .var 8
  .add (.add (.add (.add (.add (.add
    (pJointGenericBandCoeff 0)
    (.mul (pJointGenericBandCoeff 1) r))
    (.mul (pJointGenericBandCoeff 2) (.pow r 2)))
    (.mul (pJointGenericBandCoeff 3) (.pow r 3)))
    (.mul (pJointGenericBandCoeff 4) (.pow r 4)))
    (.mul (pJointGenericBandCoeff 5) (.pow r 5)))
    (.mul (pJointGenericBandCoeff 6) (.pow r 6))

private theorem pJointGenericBand_normal :
    RingNormaliser.normalize pJointGenericCore =
      RingNormaliser.normalize pJointGenericBand := by decide

private theorem jointCoreExpanded_add_eqv_bandExpanded
    (rho : Nat → Q') (B m r : JointPE) :
    RingNormaliser.eval rho
        (pJointCoreExpanded (.add B r) m) ≈
      RingNormaliser.eval rho (pJointBandExpanded B m r) := by
  let sigma : Nat → Q' := fun
    | 0 => RingNormaliser.eval rho (pJointA 0 m)
    | 1 => RingNormaliser.eval rho (pJointA 1 m)
    | 2 => RingNormaliser.eval rho (pJointA 2 m)
    | 3 => RingNormaliser.eval rho (pJointA 3 m)
    | 4 => RingNormaliser.eval rho (pJointA 4 m)
    | 5 => RingNormaliser.eval rho (pJointA 5 m)
    | 6 => RingNormaliser.eval rho (pJointA 6 m)
    | 7 => RingNormaliser.eval rho B
    | _ => RingNormaliser.eval rho r
  simpa [pJointGenericCore, pJointGenericBand,
    pJointGenericBandCoeff, pJointCoreExpanded,
    pJointBandExpanded, pJointBandCoeff,
    RingNormaliser.eval, sigma] using
    (RingNormaliser.poly_identity_of_normal_eq
      pJointGenericCore pJointGenericBand
      pJointGenericBand_normal sigma)



private def pJointCoreEvenBand : JointPE :=
  let t : JointPE := .var 0
  let r : JointPE := .var 1
  let m := .add t (.const 14)
  let D := .add (.mul (.const 2) (.pow m 2)) r
  pJointCoreCleared D m

private def pJointCoreOddBand : JointPE :=
  let t : JointPE := .var 0
  let r : JointPE := .var 1
  let m := .add t (.const 14)
  let D := .add (.mul (.const 2) (.mul m (.add m (.const 1)))) r
  pJointCoreCleared D m

private def pJointEvenBandExpanded : JointPE :=
  let t : JointPE := .var 0
  let r : JointPE := .var 1
  let m := .add t (.const 14)
  let B := .mul (.const 2) (.pow m 2)
  pJointBandExpanded B m r

private def pJointOddBandExpanded : JointPE :=
  let t : JointPE := .var 0
  let r : JointPE := .var 1
  let m := .add t (.const 14)
  let B := .mul (.const 2) (.mul m (.add m (.const 1)))
  pJointBandExpanded B m r

private def pJointEvenBandCoefficient (j : Nat) : JointPE :=
  let t : JointPE := .var 0
  let m := .add t (.const 14)
  let B := .mul (.const 2) (.pow m 2)
  pJointBandCoeff j B m

private def pJointOddBandCoefficient (j : Nat) : JointPE :=
  let t : JointPE := .var 0
  let m := .add t (.const 14)
  let B := .mul (.const 2) (.mul m (.add m (.const 1)))
  pJointBandCoeff j B m

private theorem pJointEvenBandCoefficient6_nonnegative :
    ∀ mc, mc ∈ RingNormaliser.normalize (pJointEvenBandCoefficient 6) →
      (0 : Int) ≤ mc.2 := by decide

private def jointEvenCoefficient0 : List Int :=
  [7022592, 67885056, 360883200,
    1207618616, 2067648392, -216289128,
    -8168015160, -17063466000, -20714019024,
    -20354511488, -17721356480, -10400117376,
    -3209303040, 45841920, 19507200]

private def jointEvenCoefficient : Nat → List Int
  | 0 => jointEvenCoefficient0
  | 1 => [32967168, 224589340, 173264068, -2476349124,
      -9120142796, -15067496408, -18247487000, -23838115392,
      -28711513824, -20201306816, -7345176576, 130698240, 55595520]
  | 2 => [-110752128, -815416200, -2017342168, -2219080144,
      -3684432560, -10923318768, -19491126880, -16017878048,
      -7008189824, 147767040, 64861440]
  | 3 => [102888288, 443640972, -128292860, -2990021960,
      -6904482000, -6361137392, -3545591168, 85100160, 39745920]
  | 4 => [-114863880, -468716360, -1156533120, -1210635120,
      -1000313120, 26395680, 13533120]
  | 5 => [-48006000, -79689960, -151006080, 4206240, 2438400]
  | _ => [-10003200, 274320, 182880]

private def jointOddCoefficient : Nat → List Int
  | 0 => [7022592, 133819392, 367053368, -884411744,
      -9243112832, -37394891936, -98655727336, -176672371072,
      -213102562384, -169713420992, -85259398208, -24181435008,
      -2688460800, 157032960, 19507200]
  | 1 => [32967168, -218419172, -1853741276, -8897670292,
      -38375381212, -110990361208, -195562686872, -209774679296,
      -134290386272, -46779804352, -6277157376, 390144000, 55595520]
  | 2 => [-110752128, -198086472, -2112229456, -18078509944,
      -58157324000, -93420103248, -81285075712, -36462856736,
      -6172793984, 386242560, 64861440]
  | 3 => [102888288, -475270068, -5798263740, -17030397320,
      -22585914960, -14166131952, -3236889728, 193365120, 39745920]
  | 4 => [-114863880, -948776360, -2553624720, -2704236720,
      -947277920, 50779680, 13533120]
  | 5 => [-48006000, -199728360, -147714240, 6400800, 2438400]
  | _ => [-10003200, 274320, 182880]

private def pJointEvenCoefficient0Closed (m : JointPE) : JointPE :=
  pJointUni [(0, 7022592), (1, 67885056), (2, 360883200),
    (3, 1207618616), (4, 2067648392), (5, -216289128),
    (6, -8168015160), (7, -17063466000), (8, -20714019024),
    (9, -20354511488), (10, -17721356480), (11, -10400117376),
    (12, -3209303040), (13, 45841920), (14, 19507200)] m

private def pJointEvenCoefficient0Unshifted : JointPE :=
  let m : JointPE := .var 0
  pJointBandCoeff 0 (.mul (.const 2) (.pow m 2)) m

private def pJointEvenCoefficientUnshifted (j : Nat) : JointPE :=
  let m : JointPE := .var 0
  pJointBandCoeff j (.mul (.const 2) (.pow m 2)) m

private def pJointOddCoefficientUnshifted (j : Nat) : JointPE :=
  let m : JointPE := .var 0
  pJointBandCoeff j
    (.mul (.const 2) (.mul m (.add m (.const 1)))) m

private theorem pJointEvenCoefficient0Unshifted_normal :
    RingNormaliser.normalize pJointEvenCoefficient0Unshifted =
      RingNormaliser.normalize (pJointEvenCoefficient0Closed (.var 0)) := by
  decide

private def pJointHorner : List Int → JointPE → JointPE
  | [], _ => .const 0
  | a :: as, x => .add (.const a) (.mul x (pJointHorner as x))

private theorem pJointHorner_eval (rho : Nat → Q') (x : JointPE) : ∀ cs,
    RingNormaliser.eval rho (pJointHorner cs x) ≈
      jointHornerEval cs (RingNormaliser.eval rho x)
  | [] => Q'.eqv_refl _
  | a :: as => by
      exact Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left (RingNormaliser.eval rho x) _ _
          (pJointHorner_eval rho x as))

private theorem pJointEvenCoefficient0Closed_horner_normal :
    RingNormaliser.normalize (pJointEvenCoefficient0Closed (.var 0)) =
      RingNormaliser.normalize (pJointHorner jointEvenCoefficient0 (.var 0)) := by
  decide

private theorem pJointEvenCoefficient0_normal :
    RingNormaliser.normalize (pJointEvenCoefficientUnshifted 0) =
      RingNormaliser.normalize (pJointHorner (jointEvenCoefficient 0) (.var 0)) := by
  exact Eq.trans pJointEvenCoefficient0Unshifted_normal
    pJointEvenCoefficient0Closed_horner_normal

private theorem jointEvenCoefficient0_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 jointEvenCoefficient0 →
      (0 : Int) ≤ c := by decide

private theorem pJointEvenCoefficient1_normal :
    RingNormaliser.normalize (pJointEvenCoefficientUnshifted 1) =
      RingNormaliser.normalize (pJointHorner (jointEvenCoefficient 1) (.var 0)) := by decide
private theorem pJointEvenCoefficient2_normal :
    RingNormaliser.normalize (pJointEvenCoefficientUnshifted 2) =
      RingNormaliser.normalize (pJointHorner (jointEvenCoefficient 2) (.var 0)) := by decide
private theorem pJointEvenCoefficient3_normal :
    RingNormaliser.normalize (pJointEvenCoefficientUnshifted 3) =
      RingNormaliser.normalize (pJointHorner (jointEvenCoefficient 3) (.var 0)) := by decide
private theorem pJointEvenCoefficient4_normal :
    RingNormaliser.normalize (pJointEvenCoefficientUnshifted 4) =
      RingNormaliser.normalize (pJointHorner (jointEvenCoefficient 4) (.var 0)) := by decide
private theorem pJointEvenCoefficient5_normal :
    RingNormaliser.normalize (pJointEvenCoefficientUnshifted 5) =
      RingNormaliser.normalize (pJointHorner (jointEvenCoefficient 5) (.var 0)) := by decide
private theorem pJointEvenCoefficient6_normal :
    RingNormaliser.normalize (pJointEvenCoefficientUnshifted 6) =
      RingNormaliser.normalize (pJointHorner (jointEvenCoefficient 6) (.var 0)) := by decide

private theorem jointEvenCoefficient1_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointEvenCoefficient 1) → (0 : Int) ≤ c := by decide
private theorem jointEvenCoefficient2_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointEvenCoefficient 2) → (0 : Int) ≤ c := by decide
private theorem jointEvenCoefficient3_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointEvenCoefficient 3) → (0 : Int) ≤ c := by decide
private theorem jointEvenCoefficient4_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointEvenCoefficient 4) → (0 : Int) ≤ c := by decide
private theorem jointEvenCoefficient5_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointEvenCoefficient 5) → (0 : Int) ≤ c := by decide
private theorem jointEvenCoefficient6_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointEvenCoefficient 6) → (0 : Int) ≤ c := by decide

private theorem pJointOddCoefficient0_normal :
    RingNormaliser.normalize (pJointOddCoefficientUnshifted 0) =
      RingNormaliser.normalize (pJointHorner (jointOddCoefficient 0) (.var 0)) := by decide
private theorem pJointOddCoefficient1_normal :
    RingNormaliser.normalize (pJointOddCoefficientUnshifted 1) =
      RingNormaliser.normalize (pJointHorner (jointOddCoefficient 1) (.var 0)) := by decide
private theorem pJointOddCoefficient2_normal :
    RingNormaliser.normalize (pJointOddCoefficientUnshifted 2) =
      RingNormaliser.normalize (pJointHorner (jointOddCoefficient 2) (.var 0)) := by decide
private theorem pJointOddCoefficient3_normal :
    RingNormaliser.normalize (pJointOddCoefficientUnshifted 3) =
      RingNormaliser.normalize (pJointHorner (jointOddCoefficient 3) (.var 0)) := by decide
private theorem pJointOddCoefficient4_normal :
    RingNormaliser.normalize (pJointOddCoefficientUnshifted 4) =
      RingNormaliser.normalize (pJointHorner (jointOddCoefficient 4) (.var 0)) := by decide
private theorem pJointOddCoefficient5_normal :
    RingNormaliser.normalize (pJointOddCoefficientUnshifted 5) =
      RingNormaliser.normalize (pJointHorner (jointOddCoefficient 5) (.var 0)) := by decide
private theorem pJointOddCoefficient6_normal :
    RingNormaliser.normalize (pJointOddCoefficientUnshifted 6) =
      RingNormaliser.normalize (pJointHorner (jointOddCoefficient 6) (.var 0)) := by decide

private theorem jointOddCoefficient0_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointOddCoefficient 0) → (0 : Int) ≤ c := by decide
private theorem jointOddCoefficient1_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointOddCoefficient 1) → (0 : Int) ≤ c := by decide
private theorem jointOddCoefficient2_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointOddCoefficient 2) → (0 : Int) ≤ c := by decide
private theorem jointOddCoefficient3_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointOddCoefficient 3) → (0 : Int) ≤ c := by decide
private theorem jointOddCoefficient4_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointOddCoefficient 4) → (0 : Int) ≤ c := by decide
private theorem jointOddCoefficient5_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointOddCoefficient 5) → (0 : Int) ≤ c := by decide
private theorem jointOddCoefficient6_shift_nonnegative :
    ∀ c, c ∈ jointCoeffShift 14 (jointOddCoefficient 6) → (0 : Int) ≤ c := by decide

private theorem pJointEvenCoefficient_normal (j : Nat) (hj : j ≤ 6) :
    RingNormaliser.normalize (pJointEvenCoefficientUnshifted j) =
      RingNormaliser.normalize (pJointHorner (jointEvenCoefficient j) (.var 0)) := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
      j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pJointEvenCoefficient0_normal
  · exact pJointEvenCoefficient1_normal
  · exact pJointEvenCoefficient2_normal
  · exact pJointEvenCoefficient3_normal
  · exact pJointEvenCoefficient4_normal
  · exact pJointEvenCoefficient5_normal
  · exact pJointEvenCoefficient6_normal

private theorem jointEvenCoefficient_shift_nonnegative (j : Nat) (hj : j ≤ 6) :
    ∀ c, c ∈ jointCoeffShift 14 (jointEvenCoefficient j) →
      (0 : Int) ≤ c := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
      j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact jointEvenCoefficient0_shift_nonnegative
  · exact jointEvenCoefficient1_shift_nonnegative
  · exact jointEvenCoefficient2_shift_nonnegative
  · exact jointEvenCoefficient3_shift_nonnegative
  · exact jointEvenCoefficient4_shift_nonnegative
  · exact jointEvenCoefficient5_shift_nonnegative
  · exact jointEvenCoefficient6_shift_nonnegative

private theorem pJointOddCoefficient_normal (j : Nat) (hj : j ≤ 6) :
    RingNormaliser.normalize (pJointOddCoefficientUnshifted j) =
      RingNormaliser.normalize (pJointHorner (jointOddCoefficient j) (.var 0)) := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
      j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pJointOddCoefficient0_normal
  · exact pJointOddCoefficient1_normal
  · exact pJointOddCoefficient2_normal
  · exact pJointOddCoefficient3_normal
  · exact pJointOddCoefficient4_normal
  · exact pJointOddCoefficient5_normal
  · exact pJointOddCoefficient6_normal

private theorem jointOddCoefficient_shift_nonnegative (j : Nat) (hj : j ≤ 6) :
    ∀ c, c ∈ jointCoeffShift 14 (jointOddCoefficient j) →
      (0 : Int) ≤ c := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
      j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact jointOddCoefficient0_shift_nonnegative
  · exact jointOddCoefficient1_shift_nonnegative
  · exact jointOddCoefficient2_shift_nonnegative
  · exact jointOddCoefficient3_shift_nonnegative
  · exact jointOddCoefficient4_shift_nonnegative
  · exact jointOddCoefficient5_shift_nonnegative
  · exact jointOddCoefficient6_shift_nonnegative

private theorem jointUnshiftedPolynomial_nonnegative
    (source : JointPE) (cs : List Int)
    (hnormal : RingNormaliser.normalize source =
      RingNormaliser.normalize (pJointHorner cs (.var 0)))
    (hcoeff : ∀ c, c ∈ jointCoeffShift 14 cs → (0 : Int) ≤ c)
    (t : Q') (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤ RingNormaliser.eval (fun _ => t + Q'.ofInt 14) source := by
  let m := t + Q'.ofInt 14
  have hshift := jointHornerEval_shift 14 t cs
  have hpositive : (0 : Q') ≤ jointHornerEval (jointCoeffShift 14 cs) t :=
    jointHornerEval_nonnegative ht _ hcoeff
  have hhorner : (0 : Q') ≤ jointHornerEval cs m :=
    Q'.le_trans' _ _ _ hpositive (Q'.ge_of_eqv hshift)
  have hsource := RingNormaliser.poly_identity_of_normal_eq
    source (pJointHorner cs (.var 0)) hnormal (fun _ => m)
  have hpeval := pJointHorner_eval (fun _ => m) (.var 0) cs
  have hchain : RingNormaliser.eval (fun _ => m) source ≈
      jointHornerEval cs m := Q'.eqv_trans _ _ _ hsource hpeval
  dsimp only [m] at hchain ⊢
  exact Q'.le_trans' _ _ _ hhorner (Q'.ge_of_eqv hchain)

theorem lowerSixJointEvenBandCoefficient_nonnegative
    {j : Nat} (hj : j ≤ 6) (t : Q') (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤ RingNormaliser.eval (fun _ => t)
      (pJointEvenBandCoefficient j) := by
  have h := jointUnshiftedPolynomial_nonnegative
    (pJointEvenCoefficientUnshifted j) (jointEvenCoefficient j)
    (pJointEvenCoefficient_normal j hj)
    (jointEvenCoefficient_shift_nonnegative j hj) t ht
  have heq : RingNormaliser.eval (fun _ => t)
        (pJointEvenBandCoefficient j) ≈
      RingNormaliser.eval (fun _ => t + Q'.ofInt 14)
        (pJointEvenCoefficientUnshifted j) := by
    let s : JointPE := .add (.var 0) (.const 14)
    have hs := jointEval_substituteAll (fun _ => t) s
      (pJointEvenCoefficientUnshifted j)
    change RingNormaliser.eval (fun _ => t)
        (jointSubstituteAll s (pJointEvenCoefficientUnshifted j)) ≈ _ at hs
    have hsyn : jointSubstituteAll s (pJointEvenCoefficientUnshifted j) =
        pJointEvenBandCoefficient j := by
      dsimp only [s]
      have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
          j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hsyn] at hs
    exact hs
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv heq)

theorem lowerSixJointOddBandCoefficient_nonnegative
    {j : Nat} (hj : j ≤ 6) (t : Q') (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤ RingNormaliser.eval (fun _ => t)
      (pJointOddBandCoefficient j) := by
  have h := jointUnshiftedPolynomial_nonnegative
    (pJointOddCoefficientUnshifted j) (jointOddCoefficient j)
    (pJointOddCoefficient_normal j hj)
    (jointOddCoefficient_shift_nonnegative j hj) t ht
  have heq : RingNormaliser.eval (fun _ => t)
        (pJointOddBandCoefficient j) ≈
      RingNormaliser.eval (fun _ => t + Q'.ofInt 14)
        (pJointOddCoefficientUnshifted j) := by
    let s : JointPE := .add (.var 0) (.const 14)
    have hs := jointEval_substituteAll (fun _ => t) s
      (pJointOddCoefficientUnshifted j)
    change RingNormaliser.eval (fun _ => t)
        (jointSubstituteAll s (pJointOddCoefficientUnshifted j)) ≈ _ at hs
    have hsyn : jointSubstituteAll s (pJointOddCoefficientUnshifted j) =
        pJointOddBandCoefficient j := by
      dsimp only [s]
      have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
          j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hsyn] at hs
    exact hs
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv heq)

private theorem jointBandExpanded_eval_nonnegative
    (rho : Nat → Q') (B m r : JointPE)
    (hr : (0 : Q') ≤ RingNormaliser.eval rho r)
    (hcoeff : ∀ j, j ≤ 6 →
      (0 : Q') ≤ RingNormaliser.eval rho (pJointBandCoeff j B m)) :
    (0 : Q') ≤ RingNormaliser.eval rho (pJointBandExpanded B m r) := by
  let R := RingNormaliser.eval rho r
  let C := fun j => RingNormaliser.eval rho (pJointBandCoeff j B m)
  have h0 := hcoeff 0 (by omega)
  have h1 := hcoeff 1 (by omega)
  have h2 := hcoeff 2 (by omega)
  have h3 := hcoeff 3 (by omega)
  have h4 := hcoeff 4 (by omega)
  have h5 := hcoeff 5 (by omega)
  have h6 := hcoeff 6 (by omega)
  have hp2 := ringQpow_nonnegative hr 2
  have hp3 := ringQpow_nonnegative hr 3
  have hp4 := ringQpow_nonnegative hr 4
  have hp5 := ringQpow_nonnegative hr 5
  have hp6 := ringQpow_nonnegative hr 6
  have hs1 : (0 : Q') ≤ C 0 + C 1 * R :=
    Q'.zero_le_add _ _ h0 (Q'.mul_nonneg _ _ h1 hr)
  have hs2 : (0 : Q') ≤ (C 0 + C 1 * R) +
      C 2 * RingNormaliser.qpow R 2 :=
    Q'.zero_le_add _ _ hs1 (Q'.mul_nonneg _ _ h2 hp2)
  have hs3 : (0 : Q') ≤ ((C 0 + C 1 * R) +
        C 2 * RingNormaliser.qpow R 2) +
      C 3 * RingNormaliser.qpow R 3 :=
    Q'.zero_le_add _ _ hs2 (Q'.mul_nonneg _ _ h3 hp3)
  have hs4 : (0 : Q') ≤ (((C 0 + C 1 * R) +
        C 2 * RingNormaliser.qpow R 2) +
        C 3 * RingNormaliser.qpow R 3) +
      C 4 * RingNormaliser.qpow R 4 :=
    Q'.zero_le_add _ _ hs3 (Q'.mul_nonneg _ _ h4 hp4)
  have hs5 : (0 : Q') ≤ ((((C 0 + C 1 * R) +
        C 2 * RingNormaliser.qpow R 2) +
        C 3 * RingNormaliser.qpow R 3) +
        C 4 * RingNormaliser.qpow R 4) +
      C 5 * RingNormaliser.qpow R 5 :=
    Q'.zero_le_add _ _ hs4 (Q'.mul_nonneg _ _ h5 hp5)
  have hs6 : (0 : Q') ≤ (((((C 0 + C 1 * R) +
        C 2 * RingNormaliser.qpow R 2) +
        C 3 * RingNormaliser.qpow R 3) +
        C 4 * RingNormaliser.qpow R 4) +
        C 5 * RingNormaliser.qpow R 5) +
      C 6 * RingNormaliser.qpow R 6 :=
    Q'.zero_le_add _ _ hs5 (Q'.mul_nonneg _ _ h6 hp6)
  dsimp only [C, R] at hs6
  exact hs6

theorem lowerSixJointEvenBandExpanded_nonnegative
    (t r : Q') (ht : (0 : Q') ≤ t) (hr : (0 : Q') ≤ r) :
    (0 : Q') ≤ RingNormaliser.eval (fun | 0 => t | _ => r)
      pJointEvenBandExpanded := by
  let rho : Nat → Q' := fun | 0 => t | _ => r
  let m : JointPE := .add (.var 0) (.const 14)
  let B : JointPE := .mul (.const 2) (.pow m 2)
  have hcoeff : ∀ j, j ≤ 6 →
      (0 : Q') ≤ RingNormaliser.eval rho (pJointBandCoeff j B m) := by
    intro j hj
    have h := lowerSixJointEvenBandCoefficient_nonnegative hj t ht
    let e := pJointEvenBandCoefficient j
    have hs := jointEval_substituteAll rho (.var 0) e
    have hsyn : jointSubstituteAll (.var 0) e = e := by
      dsimp only [e]
      have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
          j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hsyn] at hs
    have heq : RingNormaliser.eval rho (pJointBandCoeff j B m) ≈
        RingNormaliser.eval (fun _ => t) (pJointEvenBandCoefficient j) := by
      dsimp only [rho, B, m, e] at hs ⊢
      exact hs
    exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv heq)
  have h := jointBandExpanded_eval_nonnegative rho B m (.var 1) hr hcoeff
  dsimp only [rho, B, m, pJointEvenBandExpanded] at h ⊢
  exact h

theorem lowerSixJointOddBandExpanded_nonnegative
    (t r : Q') (ht : (0 : Q') ≤ t) (hr : (0 : Q') ≤ r) :
    (0 : Q') ≤ RingNormaliser.eval (fun | 0 => t | _ => r)
      pJointOddBandExpanded := by
  let rho : Nat → Q' := fun | 0 => t | _ => r
  let m : JointPE := .add (.var 0) (.const 14)
  let B : JointPE := .mul (.const 2) (.mul m (.add m (.const 1)))
  have hcoeff : ∀ j, j ≤ 6 →
      (0 : Q') ≤ RingNormaliser.eval rho (pJointBandCoeff j B m) := by
    intro j hj
    have h := lowerSixJointOddBandCoefficient_nonnegative hj t ht
    let e := pJointOddBandCoefficient j
    have hs := jointEval_substituteAll rho (.var 0) e
    have hsyn : jointSubstituteAll (.var 0) e = e := by
      dsimp only [e]
      have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
          j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hsyn] at hs
    have heq : RingNormaliser.eval rho (pJointBandCoeff j B m) ≈
        RingNormaliser.eval (fun _ => t) (pJointOddBandCoefficient j) := by
      dsimp only [rho, B, m, e] at hs ⊢
      exact hs
    exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv heq)
  have h := jointBandExpanded_eval_nonnegative rho B m (.var 1) hr hcoeff
  dsimp only [rho, B, m, pJointOddBandExpanded] at h ⊢
  exact h

theorem lowerSixJointEvenCore_nonnegative
    (t r : Q') (ht : (0 : Q') ≤ t) (hr : (0 : Q') ≤ r) :
    (0 : Q') ≤ RingNormaliser.eval (fun | 0 => t | _ => r)
      pJointCoreEvenBand := by
  let rho : Nat → Q' := fun | 0 => t | _ => r
  let m : JointPE := .add (.var 0) (.const 14)
  let B : JointPE := .mul (.const 2) (.pow m 2)
  let R : JointPE := .var 1
  have hc := jointCoreCleared_eqv_coreExpanded rho (.add B R) m
  have hb := jointCoreExpanded_add_eqv_bandExpanded rho B m R
  have hchain := Q'.eqv_trans _ _ _ hc hb
  have hband := lowerSixJointEvenBandExpanded_nonnegative t r ht hr
  have htarget : RingNormaliser.eval rho pJointCoreEvenBand ≈
      RingNormaliser.eval rho pJointEvenBandExpanded := by
    dsimp only [rho, B, m, R, pJointCoreEvenBand,
      pJointEvenBandExpanded] at hchain ⊢
    exact hchain
  exact Q'.le_trans' _ _ _ hband (Q'.ge_of_eqv htarget)

theorem lowerSixJointOddCore_nonnegative
    (t r : Q') (ht : (0 : Q') ≤ t) (hr : (0 : Q') ≤ r) :
    (0 : Q') ≤ RingNormaliser.eval (fun | 0 => t | _ => r)
      pJointCoreOddBand := by
  let rho : Nat → Q' := fun | 0 => t | _ => r
  let m : JointPE := .add (.var 0) (.const 14)
  let B : JointPE :=
    .mul (.const 2) (.mul m (.add m (.const 1)))
  let R : JointPE := .var 1
  have hc := jointCoreCleared_eqv_coreExpanded rho (.add B R) m
  have hb := jointCoreExpanded_add_eqv_bandExpanded rho B m R
  have hchain := Q'.eqv_trans _ _ _ hc hb
  have hband := lowerSixJointOddBandExpanded_nonnegative t r ht hr
  have htarget : RingNormaliser.eval rho pJointCoreOddBand ≈
      RingNormaliser.eval rho pJointOddBandExpanded := by
    dsimp only [rho, B, m, R, pJointCoreOddBand,
      pJointOddBandExpanded] at hchain ⊢
    exact hchain
  exact Q'.le_trans' _ _ _ hband (Q'.ge_of_eqv htarget)

/-- The parity-band certificate instantiated at the actual square-root
window.  The production threshold is much larger than the shift threshold
`m ≥ 14`, so no finite bootstrap is needed here. -/
theorem lowerSixJointCorePolynomial_nonnegative_large
    {k : Nat} (hk : 8189 ≤ k) :
    (0 : Q') ≤ RingNormaliser.eval
      (fun | 0 => Q'.ofNat (k + 2)
           | _ => Q'.ofNat (thetaWindowLeft k))
      (pJointCoreCleared (.var 0) (.var 1)) := by
  have hc28 : 28 ≤ thetaWindowCenter k := by
    unfold thetaWindowCenter thetaWindowLength
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hbands := thetaWindowCenter_band_data (k := k) (by omega)
  rcases hbands with ⟨M, r, hc, hD, _⟩ | ⟨M, r, hc, hD, _⟩
  · have hM : 9 ≤ M := by omega
    have hmNat : thetaWindowLeft k = M + 5 := by
      unfold thetaWindowLeft
      rw [hc]
      omega
    let tq := Q'.ofNat (M - 9)
    let rq := Q'.ofNat r
    let rho : Nat → Q' := fun | 0 => tq | _ => rq
    let mq := tq + Q'.ofNat 14
    let dq := Q'.ofNat 2 * RingNormaliser.qpow mq 2 + rq
    let sigma : Nat → Q' := fun | 0 => dq | _ => mq
    let actual : Nat → Q' := fun
      | 0 => Q'.ofNat (k + 2)
      | _ => Q'.ofNat (thetaWindowLeft k)
    have ht : (0 : Q') ≤ tq := by
      dsimp only [tq]
      exact HeatKernelRGStep.zero_le_ofNat _
    have hr : (0 : Q') ≤ rq := by
      dsimp only [rq]
      exact HeatKernelRGStep.zero_le_ofNat _
    have hcore := lowerSixJointEvenCore_nonnegative tq rq ht hr
    have hmShift : M - 9 + 14 = M + 5 := by omega
    have hmq : mq ≈ Q'.ofNat (M + 5) := by
      dsimp only [mq, tq]
      have h := Q'.eqv_symm (Q'.ofNat_add_eqv (M - 9) 14)
      rw [hmShift] at h
      exact h
    have hdq : dq ≈ Q'.ofNat (k + 2) := by
      dsimp only [dq, rq]
      have h := jointEvenBandD_eqv (r := r) hmq
      rw [← hD] at h
      exact h
    have henv : ∀ i, sigma i ≈ actual i := by
      intro i
      cases i with
      | zero =>
          dsimp only [sigma, actual]
          exact hdq
      | succ i =>
          dsimp only [sigma, actual]
          rw [hmNat]
          exact hmq
    have hpoly := jointEval_eqv_congr sigma actual henv
      (pJointCoreCleared (.var 0) (.var 1))
    have hsource :
        RingNormaliser.eval rho pJointCoreEvenBand ≈
          RingNormaliser.eval sigma
            (pJointCoreCleared (.var 0) (.var 1)) := by
      dsimp only [rho, sigma, dq, mq, tq, rq,
        pJointCoreEvenBand, RingNormaliser.eval]
      exact Q'.eqv_refl _
    have htarget := Q'.eqv_trans _ _ _ hsource hpoly
    dsimp only [rho, actual] at hcore htarget ⊢
    exact Q'.le_trans' _ _ _ hcore (Q'.le_of_eqv htarget)

  · have hM : 9 ≤ M := by omega
    have hmNat : thetaWindowLeft k = M + 5 := by
      unfold thetaWindowLeft
      rw [hc]
      omega
    let tq := Q'.ofNat (M - 9)
    let rq := Q'.ofNat r
    let rho : Nat → Q' := fun | 0 => tq | _ => rq
    let mq := tq + Q'.ofNat 14
    let dq := Q'.ofNat 2 * (mq * (mq + Q'.ofNat 1)) + rq
    let sigma : Nat → Q' := fun | 0 => dq | _ => mq
    let actual : Nat → Q' := fun
      | 0 => Q'.ofNat (k + 2)
      | _ => Q'.ofNat (thetaWindowLeft k)
    have ht : (0 : Q') ≤ tq := by
      dsimp only [tq]
      exact HeatKernelRGStep.zero_le_ofNat _
    have hr : (0 : Q') ≤ rq := by
      dsimp only [rq]
      exact HeatKernelRGStep.zero_le_ofNat _
    have hcore := lowerSixJointOddCore_nonnegative tq rq ht hr
    have hmShift : M - 9 + 14 = M + 5 := by omega
    have hmq : mq ≈ Q'.ofNat (M + 5) := by
      dsimp only [mq, tq]
      have h := Q'.eqv_symm (Q'.ofNat_add_eqv (M - 9) 14)
      rw [hmShift] at h
      exact h
    have hdq : dq ≈ Q'.ofNat (k + 2) := by
      dsimp only [dq, rq]
      have h := jointOddBandD_eqv (r := r) hmq
      rw [← hD] at h
      exact h
    have henv : ∀ i, sigma i ≈ actual i := by
      intro i
      cases i with
      | zero =>
          dsimp only [sigma, actual]
          exact hdq
      | succ i =>
          dsimp only [sigma, actual]
          rw [hmNat]
          exact hmq
    have hpoly := jointEval_eqv_congr sigma actual henv
      (pJointCoreCleared (.var 0) (.var 1))
    have hsource :
        RingNormaliser.eval rho pJointCoreOddBand ≈
          RingNormaliser.eval sigma
            (pJointCoreCleared (.var 0) (.var 1)) := by
      dsimp only [rho, sigma, dq, mq, tq, rq,
        pJointCoreOddBand, RingNormaliser.eval]
      exact Q'.eqv_refl _
    have htarget := Q'.eqv_trans _ _ _ hsource hpoly
    dsimp only [rho, actual] at hcore htarget ⊢
    exact Q'.le_trans' _ _ _ hcore (Q'.le_of_eqv htarget)

/-! ## Interpretation of the center-band polynomial -/

def lowerSixJointClearedBernoulli (k : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let m := Q'.ofNat (thetaWindowLeft k)
  let K := m + (1 : Q')
  let K2 := RingNormaliser.qpow K 2
  RingNormaliser.qpow D 2 + (Q'.ofNat 2 * K2) * D +
    K2 * (Q'.ofNat 2 * K2 + (1 : Q'))

def lowerSixJointReservePolynomial (k : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let m := Q'.ofNat (thetaWindowLeft k)
  let mf := Q'.ofNat 2 * m + Q'.ofNat 3
  let S := Q'.ofNat 2 * D + -(1 : Q')
  let sum6 := m * (m + (1 : Q')) *
    (Q'.ofNat 2 * m + (1 : Q'))
  Q'.ofNat 72 * (mf * (S * (D * (m * RingNormaliser.qpow D 2)))) +
    -(Q'.ofNat 12 *
      (mf * (RingNormaliser.qpow S 2 * (D * sum6))))

def lowerSixJointEndpointPositivePoly (k : Nat) : Q' :=
  RingNormaliser.eval
    (fun | 0 => Q'.ofNat (k + 2)
         | _ => Q'.ofNat (thetaWindowLeft k))
    (pJointCoreEndpointPositive (.var 0) (.var 1))

def lowerSixJointEndpointBlock (k : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let K := thetaWindowLeft k + 1
  let a := fourFifths *
    (Q'.ofNat (2 * K + 1) *
      ((1 : Q') + -(harmW k * harmW k)))
  let J := lowerSixJointEndpointPositivePoly k
  let C := (Q'.ofNat 15630 * RingNormaliser.qpow D 4) *
    lowerSixBlockClosure
  a * J + C

private def pJointPowTwoFourL : JointPE :=
  .mul (.pow (.var 0) 2) (.pow (.var 0) 4)

private def pJointPowSixR : JointPE := .pow (.var 0) 6

private theorem pJointPowTwoFour_normal :
    RingNormaliser.normalize pJointPowTwoFourL =
      RingNormaliser.normalize pJointPowSixR := by decide

private theorem jointPowTwo_mul_powFour (D : Q') :
    RingNormaliser.qpow D 2 * RingNormaliser.qpow D 4 ≈
      RingNormaliser.qpow D 6 := by
  simpa [pJointPowTwoFourL, pJointPowSixR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pJointPowTwoFourL pJointPowSixR pJointPowTwoFour_normal
      (fun _ => D))

private theorem lowerSixJointFactor_cleared (k : Nat) :
    let D := Q'.ofNat (k + 2)
    let m := Q'.ofNat (thetaWindowLeft k)
    let mf := Q'.ofNat 2 * m + Q'.ofNat 3
    let S := Q'.ofNat 2 * D + -(1 : Q')
    let a := fourFifths *
      (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
        ((1 : Q') + -(harmW k * harmW k)))
    Q'.ofNat 635 * RingNormaliser.qpow D 2 * a ≈
      Q'.ofNat 508 * (mf * S) := by
  let D := Q'.ofNat (k + 2)
  let m := Q'.ofNat (thetaWindowLeft k)
  let mf := Q'.ofNat 2 * m + Q'.ofNat 3
  let S := Q'.ofNat 2 * D + -(1 : Q')
  let delta := (1 : Q') + -(harmW k * harmW k)
  let mfNat := Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1)
  let a := fourFifths * (mfNat * delta)
  have hcoef : Q'.ofNat 635 * fourFifths ≈ Q'.ofNat 508 := by
    unfold fourFifths
    decide
  have hmf : mfNat ≈ mf := by
    dsimp only [mfNat, mf, m]
    have htwo := jointOfNat_mul_eqv 2 (thetaWindowLeft k)
    have hadd2 := Q'.ofNat_add_eqv (2 * thetaWindowLeft k) 3
    have hnat : 2 * (thetaWindowLeft k + 1) + 1 =
        2 * thetaWindowLeft k + 3 := by omega
    rw [hnat]
    refine Q'.eqv_trans _
      (Q'.ofNat (2 * thetaWindowLeft k) + Q'.ofNat 3) _ hadd2 ?_
    exact Q'.add_eqv_congr_right _ _ _ htwo
  have hdelta : RingNormaliser.qpow D 2 * delta ≈ S := by
    dsimp only [D, delta, S]
    exact lowerSixHarmonicSquareDefect_cleared k
  have hrearrange : Q'.ofNat 635 * RingNormaliser.qpow D 2 * a ≈
      (Q'.ofNat 635 * fourFifths) * mfNat *
        (RingNormaliser.qpow D 2 * delta) := by
    dsimp only [a]
    ring_qeqv
  have hreplace :
      (Q'.ofNat 635 * fourFifths) * mfNat *
          (RingNormaliser.qpow D 2 * delta) ≈
        Q'.ofNat 508 * mf * S := by
    exact Q'.eqv_trans _
      (Q'.ofNat 508 * mfNat *
        (RingNormaliser.qpow D 2 * delta)) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hcoef))
      (Q'.eqv_trans _ (Q'.ofNat 508 * mf *
          (RingNormaliser.qpow D 2 * delta)) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hmf))
        (Q'.mul_eqv_congr_left _ _ _ hdelta))
  have hreplaceAssoc :
      (Q'.ofNat 635 * fourFifths) * mfNat *
          (RingNormaliser.qpow D 2 * delta) ≈
        Q'.ofNat 508 * (mf * S) :=
    Q'.eqv_trans _ _ _ hreplace
      (Q'.mul_assoc_eqv (Q'.ofNat 508) mf S)
  dsimp only [D, m, mf, S, mfNat, a, delta] at hrearrange hreplaceAssoc ⊢
  exact Q'.eqv_trans _ _ _ hrearrange hreplaceAssoc

private theorem lowerSixJointClosure_cleared (k : Nat) :
    let D := Q'.ofNat (k + 2)
    let C := (Q'.ofNat 15630 * RingNormaliser.qpow D 4) *
      lowerSixBlockClosure
    Q'.ofNat 635 * RingNormaliser.qpow D 2 * C ≈
      Q'.ofNat 10003200 * RingNormaliser.qpow D 6 := by
  let D := Q'.ofNat (k + 2)
  let C := (Q'.ofNat 15630 * RingNormaliser.qpow D 4) *
    lowerSixBlockClosure
  have hcoef : (Q'.ofNat 635 * Q'.ofNat 15630) *
      lowerSixBlockClosure ≈ Q'.ofNat 10003200 := by
    unfold lowerSixBlockClosure
    decide
  have hrearrange : Q'.ofNat 635 * RingNormaliser.qpow D 2 * C ≈
      ((Q'.ofNat 635 * Q'.ofNat 15630) * lowerSixBlockClosure) *
        (RingNormaliser.qpow D 2 * RingNormaliser.qpow D 4) := by
    dsimp only [C]
    ring_qeqv
  have hreplace :
      ((Q'.ofNat 635 * Q'.ofNat 15630) * lowerSixBlockClosure) *
          (RingNormaliser.qpow D 2 * RingNormaliser.qpow D 4) ≈
        Q'.ofNat 10003200 * RingNormaliser.qpow D 6 :=
    Q'.eqv_trans _
      (Q'.ofNat 10003200 *
        (RingNormaliser.qpow D 2 * RingNormaliser.qpow D 4)) _
      (Q'.mul_eqv_congr_right _ _ _ hcoef)
      (Q'.mul_eqv_congr_left _ _ _ (jointPowTwo_mul_powFour D))
  dsimp only [D, C] at hrearrange hreplace ⊢
  exact Q'.eqv_trans _ _ _ hrearrange hreplace

private theorem lowerSixJointEndpointBlock_cleared (k : Nat) :
    let D := Q'.ofNat (k + 2)
    let m := Q'.ofNat (thetaWindowLeft k)
    let mf := Q'.ofNat 2 * m + Q'.ofNat 3
    let S := Q'.ofNat 2 * D + -(1 : Q')
    Q'.ofNat 635 * RingNormaliser.qpow D 2 *
        lowerSixJointEndpointBlock k ≈
      Q'.ofNat 508 *
          (mf * (S * lowerSixJointEndpointPositivePoly k)) +
        Q'.ofNat 10003200 * RingNormaliser.qpow D 6 := by
  let D := Q'.ofNat (k + 2)
  let m := Q'.ofNat (thetaWindowLeft k)
  let mf := Q'.ofNat 2 * m + Q'.ofNat 3
  let S := Q'.ofNat 2 * D + -(1 : Q')
  let J := lowerSixJointEndpointPositivePoly k
  let a := fourFifths *
    (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
      ((1 : Q') + -(harmW k * harmW k)))
  let C := (Q'.ofNat 15630 * RingNormaliser.qpow D 4) *
    lowerSixBlockClosure
  have ha := lowerSixJointFactor_cleared k
  have hC := lowerSixJointClosure_cleared k
  let T := Q'.ofNat 635 * RingNormaliser.qpow D 2
  have hrearrange : Q'.ofNat 635 * RingNormaliser.qpow D 2 *
        (a * J + C) ≈
      (Q'.ofNat 635 * RingNormaliser.qpow D 2 * a) * J +
        Q'.ofNat 635 * RingNormaliser.qpow D 2 * C := by
    refine Q'.eqv_trans _
      (T * (a * J) + T * C) _ ?_ ?_
    · dsimp only [T]
      exact Q'.mul_add_eqv _ _ _
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv T a J))
  have hreplace0 := Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ J ha) hC
  have hreplace :
      (Q'.ofNat 635 * RingNormaliser.qpow D 2 * a) * J +
          Q'.ofNat 635 * RingNormaliser.qpow D 2 * C ≈
        Q'.ofNat 508 * (mf * (S * J)) +
          Q'.ofNat 10003200 * RingNormaliser.qpow D 6 :=
    Q'.eqv_trans _ _ _ hreplace0
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv (Q'.ofNat 508) (mf * S) J)
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_assoc_eqv mf S J))))
  unfold lowerSixJointEndpointBlock
  dsimp only [D, m, mf, S, J, a, C, T] at hrearrange hreplace ⊢
  exact Q'.eqv_trans _ _ _ hrearrange hreplace

private theorem lowerSixJointCoreBern_eval (k : Nat) :
    let rho : Nat → Q' := fun
      | 0 => Q'.ofNat (k + 2)
      | _ => Q'.ofNat (thetaWindowLeft k)
    RingNormaliser.eval rho (pJointCoreBern (.var 0) (.var 1)) ≈
      lowerSixJointClearedBernoulli k := by
  dsimp only [pJointCoreBern, lowerSixJointClearedBernoulli,
    RingNormaliser.eval]
  exact Q'.eqv_refl _

private theorem lowerSixJointCoreReserve_eval (k : Nat) :
    let rho : Nat → Q' := fun
      | 0 => Q'.ofNat (k + 2)
      | _ => Q'.ofNat (thetaWindowLeft k)
    RingNormaliser.eval rho (pJointCoreReserve (.var 0) (.var 1)) ≈
      lowerSixJointReservePolynomial k := by
  dsimp only [pJointCoreReserve, pJointCoreMF, pJointCoreS,
    lowerSixJointReservePolynomial, RingNormaliser.eval]
  exact Q'.eqv_refl _

private theorem lowerSixJointCoreEndpoint_eval (k : Nat) :
    let rho : Nat → Q' := fun
      | 0 => Q'.ofNat (k + 2)
      | _ => Q'.ofNat (thetaWindowLeft k)
    RingNormaliser.eval rho
        (pJointCoreEndpointPositive (.var 0) (.var 1)) ≈
      lowerSixJointEndpointPositivePoly k := by
  dsimp only [lowerSixJointEndpointPositivePoly]
  exact Q'.eqv_refl _

private theorem lowerSixJointCoreMF_eval (k : Nat) :
    let rho : Nat → Q' := fun
      | 0 => Q'.ofNat (k + 2)
      | _ => Q'.ofNat (thetaWindowLeft k)
    RingNormaliser.eval rho (pJointCoreMF (.var 1)) ≈
      Q'.ofNat 2 * Q'.ofNat (thetaWindowLeft k) + Q'.ofNat 3 := by
  dsimp only [pJointCoreMF, RingNormaliser.eval]
  exact Q'.eqv_refl _

private theorem lowerSixJointCoreS_eval (k : Nat) :
    let rho : Nat → Q' := fun
      | 0 => Q'.ofNat (k + 2)
      | _ => Q'.ofNat (thetaWindowLeft k)
    RingNormaliser.eval rho (pJointCoreS (.var 0)) ≈
      Q'.ofNat 2 * Q'.ofNat (k + 2) + -(1 : Q') := by
  dsimp only [pJointCoreS, RingNormaliser.eval]
  exact Q'.eqv_refl _

private def lowerSixJointCoreShapePositive (k : Nat) : Q' :=
  let rho : Nat → Q' := fun
    | 0 => Q'.ofNat (k + 2)
    | _ => Q'.ofNat (thetaWindowLeft k)
  Q'.ofNat 635 *
    (RingNormaliser.eval rho (pJointCoreBern (.var 0) (.var 1)) *
      RingNormaliser.eval rho (pJointCoreReserve (.var 0) (.var 1)))

private def lowerSixJointCoreShapeEndpoint (k : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let rho : Nat → Q' := fun
    | 0 => D
    | _ => Q'.ofNat (thetaWindowLeft k)
  Q'.ofNat 508 *
      (RingNormaliser.eval rho (pJointCoreMF (.var 1)) *
        (RingNormaliser.eval rho (pJointCoreS (.var 0)) *
          RingNormaliser.eval rho
            (pJointCoreEndpointPositive (.var 0) (.var 1)))) +
    Q'.ofNat 10003200 * RingNormaliser.qpow D 6

private theorem jointCore_shape_order
    {P A E C : Q'} (hP : (0 : Q') ≤ P)
    (hshape : P ≈ (A + -E) + -C) : E + C ≤ A := by
  have hnonneg : (0 : Q') ≤ (A + -E) + -C :=
    Q'.le_trans' _ _ _ hP (Q'.le_of_eqv hshape)
  have hgroup : (A + -E) + -C ≈ A + -(E + C) := by
    ring_qeqv
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hnonneg (Q'.le_of_eqv hgroup))

private theorem lowerSixJointCoreShapeEndpoint_le_positive_large
    {k : Nat} (hk : 8189 ≤ k) :
    lowerSixJointCoreShapeEndpoint k ≤
      lowerSixJointCoreShapePositive k := by
  let D := Q'.ofNat (k + 2)
  let m := Q'.ofNat (thetaWindowLeft k)
  let rho : Nat → Q' := fun | 0 => D | _ => m
  let A := Q'.ofNat 635 *
    (RingNormaliser.eval rho (pJointCoreBern (.var 0) (.var 1)) *
      RingNormaliser.eval rho (pJointCoreReserve (.var 0) (.var 1)))
  let E := Q'.ofNat 508 *
    (RingNormaliser.eval rho (pJointCoreMF (.var 1)) *
      (RingNormaliser.eval rho (pJointCoreS (.var 0)) *
        RingNormaliser.eval rho
          (pJointCoreEndpointPositive (.var 0) (.var 1))))
  let C6 := Q'.ofNat 10003200 * RingNormaliser.qpow D 6
  have hpoly := lowerSixJointCorePolynomial_nonnegative_large hk
  have hshape := jointCoreCleared_eval_shape rho (.var 0) (.var 1)
  have horder : E + C6 ≤ A := by
    apply jointCore_shape_order hpoly
    dsimp only [D, m, rho, A, E, C6] at hshape ⊢
    exact hshape
  dsimp only [lowerSixJointCoreShapeEndpoint,
    lowerSixJointCoreShapePositive, D, m, rho, A, E, C6] at horder ⊢
  exact horder

private theorem lowerSixJointCoreShapePositive_eqv (k : Nat) :
    lowerSixJointCoreShapePositive k ≈
      Q'.ofNat 635 *
        (lowerSixJointClearedBernoulli k *
          lowerSixJointReservePolynomial k) := by
  let rho : Nat → Q' := fun
    | 0 => Q'.ofNat (k + 2)
    | _ => Q'.ofNat (thetaWindowLeft k)
  have hB := lowerSixJointCoreBern_eval k
  have hY := lowerSixJointCoreReserve_eval k
  have hprod := Q'.eqv_trans _
    (lowerSixJointClearedBernoulli k *
      RingNormaliser.eval rho (pJointCoreReserve (.var 0) (.var 1))) _
    (Q'.mul_eqv_congr_right _ _ _ hB)
    (Q'.mul_eqv_congr_left _ _ _ hY)
  unfold lowerSixJointCoreShapePositive
  dsimp only [rho] at hprod ⊢
  exact Q'.mul_eqv_congr_left _ _ _ hprod

private theorem lowerSixJointCoreShapeEndpoint_eqv (k : Nat) :
    lowerSixJointCoreShapeEndpoint k ≈
      Q'.ofNat 635 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 *
        lowerSixJointEndpointBlock k := by
  let D := Q'.ofNat (k + 2)
  let m := Q'.ofNat (thetaWindowLeft k)
  let rho : Nat → Q' := fun | 0 => D | _ => m
  let mf := Q'.ofNat 2 * m + Q'.ofNat 3
  let S := Q'.ofNat 2 * D + -(1 : Q')
  let J := lowerSixJointEndpointPositivePoly k
  let E := Q'.ofNat 508 * (mf * (S * J))
  let C6 := Q'.ofNat 10003200 * RingNormaliser.qpow D 6
  have hmf := lowerSixJointCoreMF_eval k
  have hS := lowerSixJointCoreS_eval k
  have hJ := lowerSixJointCoreEndpoint_eval k
  have hSJ :
      RingNormaliser.eval rho (pJointCoreS (.var 0)) *
          RingNormaliser.eval rho
            (pJointCoreEndpointPositive (.var 0) (.var 1)) ≈
        S * J :=
    Q'.eqv_trans _
      (S * RingNormaliser.eval rho
        (pJointCoreEndpointPositive (.var 0) (.var 1))) _
      (Q'.mul_eqv_congr_right _ _ _ hS)
      (Q'.mul_eqv_congr_left _ _ _ hJ)
  have htriple :
      RingNormaliser.eval rho (pJointCoreMF (.var 1)) *
          (RingNormaliser.eval rho (pJointCoreS (.var 0)) *
            RingNormaliser.eval rho
              (pJointCoreEndpointPositive (.var 0) (.var 1))) ≈
        mf * (S * J) :=
    Q'.eqv_trans _
      (mf * (RingNormaliser.eval rho (pJointCoreS (.var 0)) *
        RingNormaliser.eval rho
          (pJointCoreEndpointPositive (.var 0) (.var 1)))) _
      (Q'.mul_eqv_congr_right _ _ _ hmf)
      (Q'.mul_eqv_congr_left _ _ _ hSJ)
  have hcomponents : lowerSixJointCoreShapeEndpoint k ≈ E + C6 := by
    unfold lowerSixJointCoreShapeEndpoint
    dsimp only [D, m, rho, mf, S, J, E, C6]
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ htriple)
  have hZ := lowerSixJointEndpointBlock_cleared k
  dsimp only [D, m, mf, S, J, E, C6] at hZ ⊢
  exact Q'.eqv_trans _ _ _ hcomponents (Q'.eqv_symm hZ)

theorem lowerSixJointEndpointBlock_le_reserve_cleared_large
    {k : Nat} (hk : 8189 ≤ k) :
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 *
        lowerSixJointEndpointBlock k ≤
      lowerSixJointClearedBernoulli k *
        lowerSixJointReservePolynomial k := by
  let D := Q'.ofNat (k + 2)
  let Z := lowerSixJointEndpointBlock k
  let R := lowerSixJointClearedBernoulli k *
    lowerSixJointReservePolynomial k
  have horder := lowerSixJointCoreShapeEndpoint_le_positive_large hk
  have hleft := lowerSixJointCoreShapeEndpoint_eqv k
  have hright := lowerSixJointCoreShapePositive_eqv k
  have hscaled0 : (Q'.ofNat 635 * RingNormaliser.qpow D 2) * Z ≤
      Q'.ofNat 635 * R := by
    dsimp only [D, Z, R] at hleft hright ⊢
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ horder (Q'.le_of_eqv hright))
  have hassoc := Q'.mul_assoc_eqv (Q'.ofNat 635)
    (RingNormaliser.qpow D 2) Z
  have hscaled : Q'.ofNat 635 *
        (RingNormaliser.qpow D 2 * Z) ≤ Q'.ofNat 635 * R :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hassoc) hscaled0
  have hcancel := Q'.le_of_mul_le_mul_left hscaled (by decide)
  dsimp only [D, Z, R] at hcancel ⊢
  exact hcancel

private theorem lowerSixQuadraticBernoulliCoeff_double (e : Nat) :
    lowerSixQuadraticBernoulliCoeff (2 * e) = e * (2 * e + 1) := by
  induction e with
  | zero => rfl
  | succ e ih =>
      have htwo : 2 * (e + 1) = 2 * e + 1 + 1 := by omega
      rw [htwo, lowerSixQuadraticBernoulliCoeff,
        lowerSixQuadraticBernoulliCoeff, ih]
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
      omega

private def pJointBernoulliClearL : JointPE :=
  let D : JointPE := .var 0
  let u : JointPE := .var 1
  let q : JointPE := .var 2
  let c : JointPE := .var 3
  .mul (.pow D 2)
    (.add (.add (.const 1) (.mul q u)) (.mul c (.mul u u)))

private def pJointBernoulliClearR : JointPE :=
  let D : JointPE := .var 0
  let u : JointPE := .var 1
  let q : JointPE := .var 2
  let c : JointPE := .var 3
  let x := .mul D u
  .add (.add (.pow D 2) (.mul q (.mul D x)))
    (.mul c (.mul x x))

private theorem pJointBernoulliClear_normal :
    RingNormaliser.normalize pJointBernoulliClearL =
      RingNormaliser.normalize pJointBernoulliClearR := by decide

private theorem jointBernoulliClear_algebra (D u q c : Q') :
    RingNormaliser.qpow D 2 *
        (((1 : Q') + q * u) + c * (u * u)) ≈
      (RingNormaliser.qpow D 2 + q * (D * (D * u))) +
        c * ((D * u) * (D * u)) := by
  simpa [pJointBernoulliClearL, pJointBernoulliClearR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pJointBernoulliClearL pJointBernoulliClearR
      pJointBernoulliClear_normal
      (fun | 0 => D | 1 => u | 2 => q | _ => c))

private theorem lowerSixJointBernoulli_cleared_eqv (k : Nat) :
    let D := Q'.ofNat (k + 2)
    let K := thetaWindowLeft k + 1
    RingNormaliser.qpow D 2 *
        lowerSixQuadraticBernoulliDen (harmU k) (2 * (K * K)) ≈
      lowerSixJointClearedBernoulli k := by
  let D := Q'.ofNat (k + 2)
  let u := harmU k
  let Kn := thetaWindowLeft k + 1
  let e := Kn * Kn
  let q := 2 * e
  let c := e * (2 * e + 1)
  let qQ := Q'.ofNat q
  let cQ := Q'.ofNat c
  let m := Q'.ofNat (thetaWindowLeft k)
  let KQ := m + (1 : Q')
  let K2 := RingNormaliser.qpow KQ 2
  let x := D * u
  have hcoef : lowerSixQuadraticBernoulliCoeff q = c := by
    dsimp only [q, c]
    exact lowerSixQuadraticBernoulliCoeff_double e
  have hden : RingNormaliser.qpow D 2 *
        lowerSixQuadraticBernoulliDen u q ≈
      RingNormaliser.qpow D 2 *
        (((1 : Q') + qQ * u) + cQ * (u * u)) := by
    unfold lowerSixQuadraticBernoulliDen
    rw [hcoef]
    exact Q'.eqv_refl _
  have halg := jointBernoulliClear_algebra D u qQ cQ
  have hx : x ≈ (1 : Q') := by
    dsimp only [x, D, u]
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (harmonicUnit_mul_den k)
  have hDx : D * x ≈ D :=
    Q'.eqv_trans _ (D * (1 : Q')) _
      (Q'.mul_eqv_congr_left _ _ _ hx) (Q'.mul_one_eqv D)
  have hxx : x * x ≈ (1 : Q') :=
    Q'.eqv_trans _ ((1 : Q') * x) _
      (Q'.mul_eqv_congr_right _ _ _ hx)
      (Q'.eqv_trans _ ((1 : Q') * (1 : Q')) _
        (Q'.mul_eqv_congr_left _ _ _ hx) (Q'.one_mul_eqv _))
  have hcollapse :
      (RingNormaliser.qpow D 2 + qQ * (D * x)) + cQ * (x * x) ≈
        (RingNormaliser.qpow D 2 + qQ * D) + cQ := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hDx))
      (Q'.eqv_trans _ (cQ * (1 : Q')) _
        (Q'.mul_eqv_congr_left _ _ _ hxx) (Q'.mul_one_eqv cQ))
  have hK : KQ ≈ Q'.ofNat Kn := by
    dsimp only [KQ, m, Kn]
    exact Q'.eqv_symm
      (Q'.ofNat_add_eqv (thetaWindowLeft k) 1)
  have hK2 : K2 ≈ Q'.ofNat e := by
    dsimp only [K2, e, Kn]
    exact Q'.eqv_trans _ _ _ (jointQpow_eqv_congr hK 2)
      (jointQpow_two_ofNat (thetaWindowLeft k + 1))
  have hq : qQ ≈ Q'.ofNat 2 * K2 := by
    dsimp only [qQ, q, e]
    exact Q'.eqv_trans _
      (Q'.ofNat 2 * Q'.ofNat ((thetaWindowLeft k + 1) *
        (thetaWindowLeft k + 1))) _
      (jointOfNat_mul_eqv 2 _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hK2))
  have hinner : Q'.ofNat (2 * e + 1) ≈
      Q'.ofNat 2 * K2 + (1 : Q') := by
    refine Q'.eqv_trans _
      (Q'.ofNat (2 * e) + Q'.ofNat 1) _
      (Q'.ofNat_add_eqv (2 * e) 1) ?_
    exact Q'.add_eqv_congr'
      (by dsimp only [qQ, q] at hq; exact hq)
      (by decide)
  have hc : cQ ≈ K2 * (Q'.ofNat 2 * K2 + (1 : Q')) := by
    dsimp only [cQ, c]
    exact Q'.eqv_trans _
      (Q'.ofNat e * Q'.ofNat (2 * e + 1)) _
      (jointOfNat_mul_eqv e (2 * e + 1))
      (Q'.eqv_trans _
        (K2 * Q'.ofNat (2 * e + 1)) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hK2))
        (Q'.mul_eqv_congr_left _ _ _ hinner))
  have hcast : (RingNormaliser.qpow D 2 + qQ * D) + cQ ≈
      lowerSixJointClearedBernoulli k := by
    unfold lowerSixJointClearedBernoulli
    dsimp only [D, m, KQ, K2]
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hq)) hc
  dsimp only [D, u, Kn, e, q, c, qQ, cQ, m, KQ, K2, x] at hden halg hcollapse hcast ⊢
  exact Q'.eqv_trans _ _ _ hden
    (Q'.eqv_trans _ _ _ halg (Q'.eqv_trans _ _ _ hcollapse hcast))

/-- The exact endpoint mode weight cancels the cleared quadratic
Bernoulli factor, leaving precisely the square of the harmonic denominator. -/
theorem lowerSixJointModeWeight_mul_clearedBernoulli_le_D2 (k : Nat) :
    let D := Q'.ofNat (k + 2)
    let K := thetaWindowLeft k + 1
    lowerSixModeWeight k K * lowerSixJointClearedBernoulli k ≤
      RingNormaliser.qpow D 2 := by
  let D := Q'.ofNat (k + 2)
  let K := thetaWindowLeft k + 1
  let W := lowerSixModeWeight k K
  let B := lowerSixQuadraticBernoulliDen (harmU k) (2 * (K * K))
  let C := lowerSixJointClearedBernoulli k
  let D2 := RingNormaliser.qpow D 2
  have hWB : W * B ≤ (1 : Q') := by
    dsimp only [W, B]
    exact lowerSixModeWeight_mul_quadraticBernoulliDen_le_one k K
  have hD0 : (0 : Q') ≤ D := by
    dsimp only [D]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hD20 : (0 : Q') ≤ D2 := by
    dsimp only [D2]
    exact ringQpow_nonnegative hD0 2
  have hscaled : D2 * (W * B) ≤ D2 * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hWB hD20
  have hclear : D2 * B ≈ C := by
    dsimp only [D2, D, B, K, C]
    exact lowerSixJointBernoulli_cleared_eqv k
  have hreassoc : D2 * (W * B) ≈ W * (D2 * B) := by
    ring_qeqv
  have hleft : D2 * (W * B) ≈ W * C :=
    Q'.eqv_trans _ _ _ hreassoc
      (Q'.mul_eqv_congr_left _ _ _ hclear)
  have hright : D2 * (1 : Q') ≈ D2 := Q'.mul_one_eqv D2
  have hresult : W * C ≤ D2 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
  dsimp only [D, K, W, C, D2] at hresult ⊢
  exact hresult

def lowerSixJointSecondClearingScale (k : Nat) : Q' :=
  Q'.ofNat 15 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 2

/-- Positive reciprocal-Bernoulli factor clearing the first Gaussian block. -/
def lowerSixJointBlockFactor (k : Nat) : Q' :=
  fourFifths *
    (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
      ((1 : Q') + -(harmW k * harmW k)))

theorem lowerSixJointBlockFactor_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixJointBlockFactor k := by
  have hmul := Q'.mul_le_mul_of_nonneg
    (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
  have hσ1 : harmW k * harmW k ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have hu0 : (0 : Q') ≤ (1 : Q') + -(harmW k * harmW k) :=
    Q'.sub_nonneg_of_le hσ1
  unfold lowerSixJointBlockFactor
  exact Q'.mul_nonneg _ _ (by
    unfold fourFifths
    decide) (Q'.mul_nonneg _ _
      (HeatKernelRGStep.zero_le_ofNat _) hu0)

private theorem jointReserveScale_algebra
    (D mf delta H : Q') :
    (fourFifths * (mf * delta)) *
          (Q'.ofNat 15 * RingNormaliser.qpow D 2) *
          ((Q'.ofNat 6 * RingNormaliser.qpow D 3) * H) ≈
      Q'.ofNat 72 *
        (mf * ((RingNormaliser.qpow D 2 * delta) *
          (RingNormaliser.qpow D 3 * H))) := by
  have hcoef : (fourFifths * Q'.ofNat 15) * Q'.ofNat 6 ≈
      Q'.ofNat 72 := by
    unfold fourFifths
    decide
  have hrearrange :
      (fourFifths * (mf * delta)) *
            (Q'.ofNat 15 * RingNormaliser.qpow D 2) *
            ((Q'.ofNat 6 * RingNormaliser.qpow D 3) * H) ≈
        ((fourFifths * Q'.ofNat 15) * Q'.ofNat 6) *
          (mf * ((RingNormaliser.qpow D 2 * delta) *
            (RingNormaliser.qpow D 3 * H))) := by
    ring_qeqv
  exact Q'.eqv_trans _ _ _ hrearrange
    (Q'.mul_eqv_congr_right _ _ _ hcoef)

private def pJointReserveSplitL : JointPE :=
  let D : JointPE := .var 0
  let m : JointPE := .var 1
  let mf : JointPE := .var 2
  let delta : JointPE := .var 3
  let ss : JointPE := .var 4
  let X := .mul (.pow D 2) delta
  .mul (.const 72)
    (.mul mf (.mul X
      (.mul (.pow D 3) (.add m (.neg (.mul delta ss))))))

private def pJointReserveSplitR : JointPE :=
  let D : JointPE := .var 0
  let m : JointPE := .var 1
  let mf : JointPE := .var 2
  let delta : JointPE := .var 3
  let ss : JointPE := .var 4
  let X := .mul (.pow D 2) delta
  .add
    (.mul (.const 72)
      (.mul mf (.mul X (.mul D (.mul m (.pow D 2))))))
    (.neg
      (.mul (.const 12)
        (.mul mf (.mul (.pow X 2) (.mul D (.mul (.const 6) ss))))))

private theorem pJointReserveSplit_normal :
    RingNormaliser.normalize pJointReserveSplitL =
      RingNormaliser.normalize pJointReserveSplitR := by decide

private theorem jointReserveSplit_algebra
    (D m mf delta ss : Q') :
    Q'.ofNat 72 *
        (mf * ((RingNormaliser.qpow D 2 * delta) *
          (RingNormaliser.qpow D 3 * (m + -(delta * ss))))) ≈
      Q'.ofNat 72 *
          (mf * ((RingNormaliser.qpow D 2 * delta) *
            (D * (m * RingNormaliser.qpow D 2)))) +
        -(Q'.ofNat 12 *
          (mf *
            (RingNormaliser.qpow
              (RingNormaliser.qpow D 2 * delta) 2 *
              (D * (Q'.ofNat 6 * ss))))) := by
  simpa [pJointReserveSplitL, pJointReserveSplitR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pJointReserveSplitL pJointReserveSplitR
      pJointReserveSplit_normal
      (fun | 0 => D | 1 => m | 2 => mf | 3 => delta | _ => ss))

private def pJointReserveTarget : JointPE :=
  let D : JointPE := .var 0
  let m : JointPE := .var 1
  let mf : JointPE := .var 2
  let X : JointPE := .var 3
  let q : JointPE := .var 4
  .add
    (.mul (.const 72)
      (.mul mf (.mul X (.mul D (.mul m (.pow D 2))))))
    (.neg
      (.mul (.const 12)
        (.mul mf (.mul (.pow X 2) (.mul D q)))))

private theorem jointReserveTarget_eval
    (D m mf X q : Q') :
    RingNormaliser.eval
        (fun | 0 => D | 1 => m | 2 => mf | 3 => X | _ => q)
        pJointReserveTarget ≈
      Q'.ofNat 72 * (mf * (X * (D * (m * RingNormaliser.qpow D 2)))) +
        -(Q'.ofNat 12 *
          (mf * (RingNormaliser.qpow X 2 * (D * q)))) := by
  exact Q'.eqv_refl _

/-- Exact factorization of the positive polynomial reserve into the first
block factor, the second-flux clearing scale, and the tapered head mass. -/
theorem lowerSixJointBlockPayment_eqv_reserve (k : Nat) :
    lowerSixJointBlockFactor k * lowerSixJointSecondClearingScale k *
        lowerSixHermiteLinearHeadMassFloor k ≈
      lowerSixJointReservePolynomial k := by
  let D := Q'.ofNat (k + 2)
  let d := thetaWindowLeft k
  let m := Q'.ofNat d
  let mf := Q'.ofNat 2 * m + Q'.ofNat 3
  let delta := (1 : Q') + -(harmW k * harmW k)
  let S := Q'.ofNat 2 * D + -(1 : Q')
  let ss := Q'.ofNat (MovingCutoff.sumSq d)
  let sum6 := m * (m + (1 : Q')) * (Q'.ofNat 2 * m + (1 : Q'))
  let H := lowerSixHermiteLinearHeadSum k
  have hmd : Q'.ofNat d ≈ m := by
    dsimp only [m]
    exact Q'.eqv_refl _
  have hmfNat : Q'.ofNat (2 * (d + 1) + 1) ≈ mf := by
    have htwo := jointOfNat_mul_eqv 2 d
    have hadd := Q'.ofNat_add_eqv (2 * d) 3
    have hnat : 2 * (d + 1) + 1 = 2 * d + 3 := by omega
    rw [hnat]
    refine Q'.eqv_trans _ (Q'.ofNat (2 * d) + Q'.ofNat 3) _ hadd ?_
    dsimp only [mf, m]
    exact Q'.add_eqv_congr_right _ _ _ htwo
  have hhead : H ≈ m + -(delta * ss) := by
    dsimp only [H, m, delta, ss, d]
    exact lowerSixHermiteLinearHeadSum_eqv_closed k
  have hS : RingNormaliser.qpow D 2 * delta ≈ S := by
    dsimp only [D, delta, S]
    exact lowerSixHarmonicSquareDefect_cleared k
  have hsum6 : Q'.ofNat 6 * ss ≈ sum6 := by
    have hcast := jointOfNat_mul_eqv 6 (MovingCutoff.sumSq d)
    rw [MovingCutoff.six_sumSq d] at hcast
    have hm1 : Q'.ofNat (d + 1) ≈ m + (1 : Q') := by
      exact Q'.eqv_trans _ (Q'.ofNat d + Q'.ofNat 1) _
        (Q'.ofNat_add_eqv d 1)
        (Q'.add_eqv_congr' hmd (by decide))
    have h2m1 : Q'.ofNat (2 * d + 1) ≈
        Q'.ofNat 2 * m + (1 : Q') := by
      exact Q'.eqv_trans _ (Q'.ofNat (2 * d) + Q'.ofNat 1) _
        (Q'.ofNat_add_eqv (2 * d) 1)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ (Q'.ofNat 2 * Q'.ofNat d) _
            (jointOfNat_mul_eqv 2 d)
            (Q'.mul_eqv_congr_left _ _ _ hmd))
          (by decide))
    have hprodNat : Q'.ofNat (d * (d + 1) * (2 * d + 1)) ≈ sum6 := by
      exact Q'.eqv_trans _
        ((Q'.ofNat d * Q'.ofNat (d + 1)) * Q'.ofNat (2 * d + 1)) _
        (Q'.eqv_trans _
          (Q'.ofNat (d * (d + 1)) * Q'.ofNat (2 * d + 1)) _
          (jointOfNat_mul_eqv (d * (d + 1)) (2 * d + 1))
          (Q'.mul_eqv_congr_right _ _ _ (jointOfNat_mul_eqv d (d + 1))))
        (Q'.eqv_trans _
          ((m * (m + (1 : Q'))) * Q'.ofNat (2 * d + 1)) _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_trans _ (m * Q'.ofNat (d + 1)) _
              (Q'.mul_eqv_congr_right _ _ _ hmd)
              (Q'.mul_eqv_congr_left _ _ _ hm1)))
          (Q'.mul_eqv_congr_left _ _ _ h2m1))
    dsimp only [ss]
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcast) hprodNat
  have hscale0 :
      (fourFifths * (mf * delta)) *
          (Q'.ofNat 15 * RingNormaliser.qpow D 2) *
          ((Q'.ofNat 6 * RingNormaliser.qpow D 3) * H) ≈
        Q'.ofNat 72 *
          (mf * ((RingNormaliser.qpow D 2 * delta) *
            (RingNormaliser.qpow D 3 * H))) :=
    jointReserveScale_algebra D mf delta H
  have hheadSub :
      Q'.ofNat 72 *
          (mf * ((RingNormaliser.qpow D 2 * delta) *
            (RingNormaliser.qpow D 3 * H))) ≈
        Q'.ofNat 72 *
          (mf * ((RingNormaliser.qpow D 2 * delta) *
            (RingNormaliser.qpow D 3 * (m + -(delta * ss))))) := by
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hhead)))
  have hsplit := jointReserveSplit_algebra D m mf delta ss
  let rho : Nat → Q' := fun
    | 0 => D | 1 => m | 2 => mf
    | 3 => RingNormaliser.qpow D 2 * delta
    | _ => Q'.ofNat 6 * ss
  let sigma : Nat → Q' := fun
    | 0 => D | 1 => m | 2 => mf | 3 => S | _ => sum6
  have henv : ∀ i, rho i ≈ sigma i := by
    intro i
    cases i with
    | zero => exact Q'.eqv_refl _
    | succ i =>
      cases i with
      | zero => exact Q'.eqv_refl _
      | succ i =>
        cases i with
        | zero => exact Q'.eqv_refl _
        | succ i =>
          cases i with
          | zero => exact hS
          | succ i => exact hsum6
  have htargetReplace := jointEval_eqv_congr rho sigma henv pJointReserveTarget
  have hrawEval := jointReserveTarget_eval D m mf
    (RingNormaliser.qpow D 2 * delta) (Q'.ofNat 6 * ss)
  have htargetEval := jointReserveTarget_eval D m mf S sum6
  have hreplace :
      Q'.ofNat 72 *
          (mf * ((RingNormaliser.qpow D 2 * delta) *
            (D * (m * RingNormaliser.qpow D 2)))) +
        -(Q'.ofNat 12 *
          (mf * (RingNormaliser.qpow
            (RingNormaliser.qpow D 2 * delta) 2 *
            (D * (Q'.ofNat 6 * ss))))) ≈
      Q'.ofNat 72 * (mf * (S * (D * (m * RingNormaliser.qpow D 2)))) +
        -(Q'.ofNat 12 *
          (mf * (RingNormaliser.qpow S 2 * (D * sum6)))) := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hrawEval)
      (Q'.eqv_trans _ _ _ htargetReplace htargetEval)
  have htargetShape :
      Q'.ofNat 72 * (mf * (S * (D * (m * RingNormaliser.qpow D 2)))) +
          -(Q'.ofNat 12 *
            (mf * (RingNormaliser.qpow S 2 * (D * sum6)))) ≈
        lowerSixJointReservePolynomial k := by
    unfold lowerSixJointReservePolynomial
    dsimp only [D, d, m, mf, S, sum6]
    exact Q'.eqv_refl _
  have hfactorCast :
      lowerSixJointBlockFactor k * lowerSixJointSecondClearingScale k *
          lowerSixHermiteLinearHeadMassFloor k ≈
        (fourFifths * (mf * delta)) *
          (Q'.ofNat 15 * RingNormaliser.qpow D 2) *
          ((Q'.ofNat 6 * RingNormaliser.qpow D 3) * H) := by
    unfold lowerSixJointBlockFactor lowerSixJointSecondClearingScale
    unfold lowerSixHermiteLinearHeadMassFloor
    dsimp only [D, d, m, mf, delta, H]
    have hinner :
        Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
            ((1 : Q') + -(harmW k * harmW k)) ≈
          (Q'.ofNat 2 * Q'.ofNat (thetaWindowLeft k) + Q'.ofNat 3) *
            ((1 : Q') + -(harmW k * harmW k)) :=
      Q'.mul_eqv_congr_right _ _ _ hmfNat
    have hfactor :
        fourFifths *
            (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
              ((1 : Q') + -(harmW k * harmW k))) ≈
          fourFifths *
            ((Q'.ofNat 2 * Q'.ofNat (thetaWindowLeft k) + Q'.ofNat 3) *
              ((1 : Q') + -(harmW k * harmW k))) :=
      Q'.mul_eqv_congr_left _ _ _ hinner
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hfactor)
  exact Q'.eqv_trans _ _ _ hfactorCast
    (Q'.eqv_trans _ _ _ hscale0
      (Q'.eqv_trans _ _ _ hheadSub
        (Q'.eqv_trans _ _ _ hsplit
          (Q'.eqv_trans _ _ _ hreplace htargetShape))))

theorem lowerSixJointReservePolynomial_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixJointReservePolynomial k := by
  let D := Q'.ofNat (k + 2)
  let a := lowerSixJointBlockFactor k
  let T := lowerSixJointSecondClearingScale k
  let H := lowerSixHermiteLinearHeadMassFloor k
  have hD0 : (0 : Q') ≤ D := by
    dsimp only [D]
    exact HeatKernelRGStep.zero_le_ofNat _
  have ha0 : (0 : Q') ≤ a := by
    dsimp only [a]
    exact lowerSixJointBlockFactor_nonnegative k
  have hT0 : (0 : Q') ≤ T := by
    dsimp only [T, lowerSixJointSecondClearingScale, D]
    exact Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative hD0 2)
  have hH0 : (0 : Q') ≤ H := by
    dsimp only [H]
    unfold lowerSixHermiteLinearHeadMassFloor
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative hD0 3))
      (lowerSixHermiteLinearHeadSum_nonnegative k)
  have hprod : (0 : Q') ≤ a * T * H :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha0 hT0) hH0
  have heq := lowerSixJointBlockPayment_eqv_reserve k
  dsimp only [a, T, H] at hprod heq
  exact Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv heq)

/-- The center-band certificate, quadratic Bernoulli cancellation, and exact
reserve factorization pay the endpoint block with its actual Gaussian weight. -/
theorem lowerSixJointEndpointBlock_weight_le_reserve_large
    {k : Nat} (hk : 8189 ≤ k) :
    let K := thetaWindowLeft k + 1
    lowerSixModeWeight k K * lowerSixJointEndpointBlock k ≤
      lowerSixJointReservePolynomial k := by
  let D := Q'.ofNat (k + 2)
  let D2 := RingNormaliser.qpow D 2
  let K := thetaWindowLeft k + 1
  let W := lowerSixModeWeight k K
  let B := lowerSixJointClearedBernoulli k
  let Z := lowerSixJointEndpointBlock k
  let R := lowerSixJointReservePolynomial k
  have hendpoint : D2 * Z ≤ B * R := by
    dsimp only [D2, D, Z, B, R]
    exact lowerSixJointEndpointBlock_le_reserve_cleared_large hk
  have hW0 : (0 : Q') ≤ W := by
    dsimp only [W]
    exact
      HarmonicMassCrossLowerSixScaledCrossDriftCarrier.lowerSixModeWeight_nonnegative
        k K
  have hR0 : (0 : Q') ≤ R := by
    dsimp only [R]
    exact lowerSixJointReservePolynomial_nonnegative k
  have hscaled : W * (D2 * Z) ≤ W * (B * R) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hendpoint hW0
  have hleft : W * (D2 * Z) ≈ D2 * (W * Z) := by
    ring_qeqv
  have hright : W * (B * R) ≈ (W * B) * R := by
    ring_qeqv
  have hWB : W * B ≤ D2 := by
    dsimp only [W, B, D2, D, K]
    exact lowerSixJointModeWeight_mul_clearedBernoulli_le_D2 k
  have hreplace : (W * B) * R ≤ D2 * R :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hWB hR0
  have hcleared : D2 * (W * Z) ≤ D2 * R :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright) hreplace))
  have hDpos : (0 : Q') < D := by
    dsimp only [D]
    exact Q'.ofNat_succ_pos (k + 1)
  have hD2pos : (0 : Q') < D2 := by
    dsimp only [D2]
    exact BondMovingScaledNorm.qpow_pos hDpos 2
  have hresult : W * Z ≤ R :=
    Q'.le_of_mul_le_mul_left hcleared hD2pos
  dsimp only [K, W, Z, R] at hresult ⊢
  exact hresult

private def pJointEndpointNegSecondFlux (D m : JointPE) : JointPE :=
  let N := .add m (.const 1)
  let D2 := .pow D 2
  let D3 := .pow D 3
  let D4 := .pow D 4
  let N3 := .pow N 3
  let N5 := .pow N 5
  let N7 := .pow N 7
  let N9 := .pow N 9
  .neg
    (.add
      (.add
        (.add
          (.add
            (.neg (.mul (.mul (.const 15750) N) D4))
            (.neg (.mul (.mul (.const 45560) N3) D3)))
          (.mul (.mul (.const 10976) N5) D2))
        (.neg (.mul (.mul (.const 30848) N7) D)))
      (.neg (.mul (.const 4608) N9)))

private theorem pJointEndpointNegSecondFlux_normal :
    RingNormaliser.normalize
        (pJointCoreEndpointPositive (.var 0) (.var 1)) =
      RingNormaliser.normalize
        (pJointEndpointNegSecondFlux (.var 0) (.var 1)) := by
  decide

/-- Semantic identification of the endpoint polynomial used above: it is
exactly the negative weight-free second Hermite flux at the first mode beyond
the certified square-root head. -/
theorem lowerSixJointEndpointPositivePoly_eqv_neg_secondFlux (k : Nat) :
    lowerSixJointEndpointPositivePoly k ≈
      -lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2))
        (Q'.ofNat (thetaWindowLeft k) + (1 : Q')) := by
  let D := Q'.ofNat (k + 2)
  let m := Q'.ofNat (thetaWindowLeft k)
  let rho : Nat → Q' := fun | 0 => D | _ => m
  have hJ := lowerSixJointCoreEndpoint_eval k
  have hpoly := RingNormaliser.poly_identity_of_normal_eq
    (pJointCoreEndpointPositive (.var 0) (.var 1))
    (pJointEndpointNegSecondFlux (.var 0) (.var 1))
    pJointEndpointNegSecondFlux_normal rho
  have hrhs :
      RingNormaliser.eval rho
          (pJointEndpointNegSecondFlux (.var 0) (.var 1)) ≈
        -lowerSixHermiteSecondFluxPoly D (m + (1 : Q')) := by
    dsimp only [rho, pJointEndpointNegSecondFlux,
      lowerSixHermiteSecondFluxPoly, RingNormaliser.eval]
    exact Q'.eqv_refl _
  dsimp only [rho, D, m] at hJ
  dsimp only [D, m] at hpoly hrhs ⊢
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hJ)
    (Q'.eqv_trans _ _ _ hpoly hrhs)

#print axioms lowerSixJointCorePolynomial_nonnegative_large
#print axioms lowerSixJointEndpointBlock_le_reserve_cleared_large
#print axioms lowerSixJointModeWeight_mul_clearedBernoulli_le_D2
#print axioms lowerSixJointBlockPayment_eqv_reserve
#print axioms lowerSixJointReservePolynomial_nonnegative
#print axioms lowerSixJointEndpointBlock_weight_le_reserve_large
#print axioms lowerSixJointEndpointPositivePoly_eqv_neg_secondFlux

end YMGap.Continuum.HarmonicLowerSixJointEndpointPayment
