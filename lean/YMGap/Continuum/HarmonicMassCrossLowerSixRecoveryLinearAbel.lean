/-
Linear-preload Abel coordinates for the fixed-center recovery drop.

The full Gaussian mode weight hides a quadratic cross-scale drift.  Splitting
its exponent into the maximal linear preload `6j` and the complementary
decreasing exponent exposes two separate mechanisms: a scale drop of the
one-crossing carrier, and an adverse but explicit complementary-weight drift.
This file records that decomposition exactly, without estimates.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem linear_abel_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "linear_abel_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               linear_abel_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private abbrev LinearAbelPE := RingNormaliser.PolyExpr

private def pLinearAbelSplitL : LinearAbelPE :=
  let a : LinearAbelPE := .var 0
  let b : LinearAbelPE := .var 1
  let x : LinearAbelPE := .var 2
  let y : LinearAbelPE := .var 3
  .add (.mul a x) (.neg (.mul b y))

private def pLinearAbelSplitR : LinearAbelPE :=
  let a : LinearAbelPE := .var 0
  let b : LinearAbelPE := .var 1
  let x : LinearAbelPE := .var 2
  let y : LinearAbelPE := .var 3
  .add (.mul (.add a (.neg b)) x)
    (.mul b (.add x (.neg y)))

private theorem pLinearAbelSplit_normal :
    RingNormaliser.normalize pLinearAbelSplitL =
      RingNormaliser.normalize pLinearAbelSplitR := by
  decide

private theorem linear_abel_split_algebra (a b x y : Q') :
    a * x + -(b * y) ≈ (a + -b) * x + b * (x + -y) := by
  simpa [pLinearAbelSplitL, pLinearAbelSplitR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pLinearAbelSplitL pLinearAbelSplitR pLinearAbelSplit_normal
      (fun | 0 => a | 1 => b | 2 => x | _ => y))

private def pLinearCarrierFactorL : LinearAbelPE :=
  let a : LinearAbelPE := .var 0
  let x : LinearAbelPE := .var 1
  let r : LinearAbelPE := .var 2
  let p : LinearAbelPE := .var 3
  let q : LinearAbelPE := .var 4
  .add (.mul (.mul a x) p)
    (.neg (.mul (.mul a (.mul x r)) q))

private def pLinearCarrierFactorR : LinearAbelPE :=
  let a : LinearAbelPE := .var 0
  let x : LinearAbelPE := .var 1
  let r : LinearAbelPE := .var 2
  let p : LinearAbelPE := .var 3
  let q : LinearAbelPE := .var 4
  .mul (.mul a x) (.add p (.neg (.mul r q)))

private theorem pLinearCarrierFactor_normal :
    RingNormaliser.normalize pLinearCarrierFactorL =
      RingNormaliser.normalize pLinearCarrierFactorR := by
  decide

private theorem linear_carrier_factor_algebra (a x r p q : Q') :
    a * x * p + -(a * (x * r) * q) ≈
      a * x * (p + -(r * q)) := by
  simpa [pLinearCarrierFactorL, pLinearCarrierFactorR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pLinearCarrierFactorL pLinearCarrierFactorR
      pLinearCarrierFactor_normal
      (fun | 0 => a | 1 => x | 2 => r | 3 => p | _ => q))

/-- The maximal linear preload of a recovery mode.  Its sign is exactly the
sign of the normalized recovery slope. -/
def lowerSixRecoveryLinearCarrier (k j : Nat) : Q' :=
  let n := j + 1
  Q'.ofNat n * qpow (harmW k) (6 * j) *
    lowerSixRecoveryModeSlope k n

/-- The complementary Gaussian weight left after extracting `6j`. -/
def lowerSixRecoveryComplementWeight (k j : Nat) : Q' :=
  qpow (harmW k) (2 * j * (j - 1) + 2)

def lowerSixRecoveryLinearCarrierDrop (k j : Nat) : Q' :=
  lowerSixRecoveryLinearCarrier k j +
    -lowerSixRecoveryLinearCarrier (k + 1) j

/-- Weight-free scale-drop carrier left after transporting only the linear
preload.  This is the pointwise post-bootstrap positivity target. -/
def lowerSixRecoveryLinearSlopeDropCarrier (k j : Nat) : Q' :=
  let n := j + 1
  lowerSixRecoveryModeSlope k n +
    -(qpow (driftRatio k) (6 * j) *
      lowerSixRecoveryModeSlope (k + 1) n)

def lowerSixRecoveryComplementWeightDrop (k j : Nat) : Q' :=
  lowerSixRecoveryComplementWeight k j +
    -lowerSixRecoveryComplementWeight (k + 1) j

/-- Favorable scale-drop reserve after the linear preload. -/
def lowerSixRecoveryLinearScaleReserve (k c : Nat) : Q' :=
  finSum (fun j =>
    lowerSixRecoveryLinearCarrierDrop k j *
      lowerSixRecoveryComplementWeight k j) (2 * c)

/-- Remaining drift debt: the next-scale one-crossing carrier paired with the
adverse complementary-weight drift, together with the terminal mode. -/
def lowerSixRecoveryLinearDriftDebt (k c : Nat) : Q' :=
  finSum (fun j =>
    lowerSixRecoveryLinearCarrier (k + 1) j *
      lowerSixRecoveryComplementWeightDrop k j) (2 * c) +
    lowerSixRecoveryTerminalDrop k (2 * c)

private theorem lowerSixModeWeight_eqv_linearComplement (k j : Nat) :
    qpow (harmW k) (6 * j) *
        lowerSixRecoveryComplementWeight k j ≈
      lowerSixModeWeight k (j + 1) := by
  let n := j + 1
  let r := 2 * j * (j - 1) + 2
  have htotal : 6 * j + r = 2 * n * n := by
    dsimp only [r, n]
    exact maximalLinearAbelExponent_total j
  have hadd := HeatKernelRGStep.qpow_add (harmW k) (6 * j) r
  rw [htotal] at hadd
  have hdouble : lowerSixModeWeight k n ≈
      qpow (harmW k) (2 * n * n) := by
    have hs := FusionQuotientCollapse.qpow_mul_self
      (harmW k) (n * n)
    have ha := HeatKernelRGStep.qpow_add
      (harmW k) (n * n) (n * n)
    have he : n * n + n * n = 2 * n * n := by
      rw [Nat.two_mul]
      exact (Nat.add_mul n n n).symm
    rw [he] at ha
    unfold lowerSixModeWeight
    exact Q'.eqv_trans _ _ _ hs (Q'.eqv_symm ha)
  unfold lowerSixRecoveryComplementWeight
  dsimp only [r, n] at hadd hdouble ⊢
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hadd)
    (Q'.eqv_symm hdouble)

/-- The preload split is exact: carrier times complementary weight is the
original sparse recovery mode. -/
theorem lowerSixRecoveryLinearCarrier_mul_complementWeight
    (k j : Nat) :
    lowerSixRecoveryLinearCarrier k j *
        lowerSixRecoveryComplementWeight k j ≈
      lowerSixRecoverySparseMode k (j + 1) := by
  have hweight := lowerSixModeWeight_eqv_linearComplement k j
  have hsparse := lowerSixRecoverySparseMode_eqv_weightSlope
    k (j + 1) (by omega)
  refine Q'.eqv_trans _
    (Q'.ofNat (j + 1) *
      (qpow (harmW k) (6 * j) *
        lowerSixRecoveryComplementWeight k j) *
      lowerSixRecoveryModeSlope k (j + 1)) _ ?_ ?_
  · unfold lowerSixRecoveryLinearCarrier
    linear_abel_ring
  refine Q'.eqv_trans _
    (lowerSixRecoveryDropWeight k (j + 1) *
      lowerSixRecoveryModeSlope k (j + 1)) _ ?_ ?_
  · unfold lowerSixRecoveryDropWeight
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (j + 1)) _ _ hweight)
  · exact Q'.eqv_symm hsparse

theorem lowerSixRecoveryComplementWeight_nonnegative (k j : Nat) :
    (0 : Q') ≤ lowerSixRecoveryComplementWeight k j := by
  unfold lowerSixRecoveryComplementWeight
  exact qpow_nonneg _ (harmW_nonneg k) _

theorem lowerSixRecoveryComplementWeight_pos (k j : Nat) :
    (0 : Q') < lowerSixRecoveryComplementWeight k j := by
  unfold lowerSixRecoveryComplementWeight
  exact BondMovingScaledNorm.qpow_pos
    (HarmonicFusedSchurObstruction.harmW_pos k) _

/-- The complementary mode weight decreases along the mode index. -/
theorem lowerSixRecoveryComplementWeight_antitone (k j : Nat) :
    lowerSixRecoveryComplementWeight k (j + 1) ≤
      lowerSixRecoveryComplementWeight k j := by
  unfold lowerSixRecoveryComplementWeight
  exact maximalLinearAbelWeight_antitone k j

/-- At fixed mode the complementary weight grows with the harmonic scale. -/
theorem lowerSixRecoveryComplementWeight_scale_mono (k j : Nat) :
    lowerSixRecoveryComplementWeight k j ≤
      lowerSixRecoveryComplementWeight (k + 1) j := by
  unfold lowerSixRecoveryComplementWeight
  exact FusedAmplitudeDerivation.qpow_mono_base
    (harmW_nonneg k)
    (HarmonicDriftAntisymmetry.harmW_mono_step k) _

theorem lowerSixRecoveryComplementWeightDrop_nonpositive (k j : Nat) :
    lowerSixRecoveryComplementWeightDrop k j ≤ (0 : Q') := by
  have h := lowerSixRecoveryComplementWeight_scale_mono k j
  have hsub := Q'.add_le_add_right
    (lowerSixRecoveryComplementWeight k j)
    (lowerSixRecoveryComplementWeight (k + 1) j)
    (-lowerSixRecoveryComplementWeight (k + 1) j) h
  unfold lowerSixRecoveryComplementWeightDrop
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_of_eqv (Q'.add_neg_self_eqv _))

private theorem lowerSixRecoveryLinearCarrierFactor_pos (k j : Nat) :
    (0 : Q') < Q'.ofNat (j + 1) * qpow (harmW k) (6 * j) := by
  exact Q'.mul_pos (Q'.ofNat_succ_pos j)
    (BondMovingScaledNorm.qpow_pos
      (HarmonicFusedSchurObstruction.harmW_pos k) _)

theorem lowerSixRecoveryLinearCarrier_nonnegative_of_slope
    {k j : Nat}
    (h : (0 : Q') ≤ lowerSixRecoveryModeSlope k (j + 1)) :
    (0 : Q') ≤ lowerSixRecoveryLinearCarrier k j := by
  unfold lowerSixRecoveryLinearCarrier
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt (lowerSixRecoveryLinearCarrierFactor_pos k j)) h

theorem lowerSixRecoveryModeSlope_nonnegative_of_linearCarrier
    {k j : Nat}
    (h : (0 : Q') ≤ lowerSixRecoveryLinearCarrier k j) :
    (0 : Q') ≤ lowerSixRecoveryModeSlope k (j + 1) := by
  unfold lowerSixRecoveryLinearCarrier at h
  exact Q'.nonneg_of_mul_pos
    (lowerSixRecoveryLinearCarrierFactor_pos k j) h

/-- The linearly preloaded carrier inherits the forward half of the exact
one-crossing property. -/
theorem lowerSixRecoveryLinearCarrier_nonnegative_succ
    {k j : Nat}
    (h : (0 : Q') ≤ lowerSixRecoveryLinearCarrier k j) :
    (0 : Q') ≤ lowerSixRecoveryLinearCarrier k (j + 1) := by
  have hslope := lowerSixRecoveryModeSlope_nonnegative_of_linearCarrier h
  have hnext := lowerSixRecoveryModeSlope_nonnegative_succ
    (k := k) (n := j + 1) (by omega) hslope
  exact lowerSixRecoveryLinearCarrier_nonnegative_of_slope hnext

/-- Dually, a nonpositive carrier forces the preceding carrier nonpositive. -/
theorem lowerSixRecoveryLinearCarrier_nonpositive_pred
    {k j : Nat}
    (h : lowerSixRecoveryLinearCarrier k (j + 1) ≤ (0 : Q')) :
    lowerSixRecoveryLinearCarrier k j ≤ (0 : Q') := by
  let A := Q'.ofNat (j + 1 + 1) * qpow (harmW k) (6 * (j + 1))
  have hA : (0 : Q') < A := by
    dsimp only [A]
    exact lowerSixRecoveryLinearCarrierFactor_pos k (j + 1)
  have hscaled : A * lowerSixRecoveryModeSlope k (j + 1 + 1) ≤
      A * (0 : Q') := by
    have hz : A * lowerSixRecoveryModeSlope k (j + 1 + 1) ≤
        (0 : Q') := by
      dsimp only [A]
      unfold lowerSixRecoveryLinearCarrier at h
      exact h
    exact Q'.le_trans' _ _ _ hz
      (Q'.ge_of_eqv (Q'.mul_zero_eqv A))
  have hslopeNext : lowerSixRecoveryModeSlope k (j + 1 + 1) ≤
      (0 : Q') := Q'.le_of_mul_le_mul_left hscaled hA
  have hslope := lowerSixRecoveryModeSlope_nonpositive_pred hslopeNext
  unfold lowerSixRecoveryLinearCarrier
  exact Q'.mul_nonpos_of_nonneg_nonpos
    (Q'.le_of_lt (lowerSixRecoveryLinearCarrierFactor_pos k j)) hslope

/-- Exact positive factorization of the scale-drop reserve carrier. -/
theorem lowerSixRecoveryLinearCarrierDrop_factor (k j : Nat) :
    lowerSixRecoveryLinearCarrierDrop k j ≈
      (Q'.ofNat (j + 1) * qpow (harmW k) (6 * j)) *
        lowerSixRecoveryLinearSlopeDropCarrier k j := by
  have hbase := BondMovingRelResidual.qpow_eqv_congr_base
    (harmW_step_eqv k) (6 * j)
  have hpow : qpow (harmW (k + 1)) (6 * j) ≈
      qpow (harmW k) (6 * j) * qpow (driftRatio k) (6 * j) :=
    Q'.eqv_trans _ _ _ hbase
      (qpow_mul_base (harmW k) (driftRatio k) (6 * j))
  unfold lowerSixRecoveryLinearCarrierDrop
    lowerSixRecoveryLinearCarrier lowerSixRecoveryLinearSlopeDropCarrier
  dsimp only
  refine Q'.eqv_trans _
    (Q'.ofNat (j + 1) * qpow (harmW k) (6 * j) *
        lowerSixRecoveryModeSlope k (j + 1) +
      -(Q'.ofNat (j + 1) *
        (qpow (harmW k) (6 * j) * qpow (driftRatio k) (6 * j)) *
        lowerSixRecoveryModeSlope (k + 1) (j + 1))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat (j + 1)) _ _ hpow)))
  · exact linear_carrier_factor_algebra _ _ _ _ _

theorem lowerSixRecoveryLinearCarrierDrop_nonnegative_of_slopeCarrier
    {k j : Nat}
    (h : (0 : Q') ≤ lowerSixRecoveryLinearSlopeDropCarrier k j) :
    (0 : Q') ≤ lowerSixRecoveryLinearCarrierDrop k j := by
  have hprod : (0 : Q') ≤
      (Q'.ofNat (j + 1) * qpow (harmW k) (6 * j)) *
        lowerSixRecoveryLinearSlopeDropCarrier k j :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt (lowerSixRecoveryLinearCarrierFactor_pos k j)) h
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_of_eqv (Q'.eqv_symm
      (lowerSixRecoveryLinearCarrierDrop_factor k j)))

theorem lowerSixRecoveryLinearSlopeDropCarrier_nonnegative_of_carrierDrop
    {k j : Nat}
    (h : (0 : Q') ≤ lowerSixRecoveryLinearCarrierDrop k j) :
    (0 : Q') ≤ lowerSixRecoveryLinearSlopeDropCarrier k j := by
  have hprod : (0 : Q') ≤
      (Q'.ofNat (j + 1) * qpow (harmW k) (6 * j)) *
        lowerSixRecoveryLinearSlopeDropCarrier k j :=
    Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (lowerSixRecoveryLinearCarrierDrop_factor k j))
  exact Q'.nonneg_of_mul_pos
    (lowerSixRecoveryLinearCarrierFactor_pos k j) hprod

/-! ## Exact cross-scale split -/

/-- Each sparse mode drop is the sum of a carrier-scale drop at the old
decreasing weight and the next carrier paired with the adverse weight drift. -/
theorem lowerSixRecoverySparseModeDrop_eqv_linearAbelSplit (k j : Nat) :
    lowerSixRecoverySparseModeDrop k (j + 1) ≈
      lowerSixRecoveryLinearCarrierDrop k j *
          lowerSixRecoveryComplementWeight k j +
        lowerSixRecoveryLinearCarrier (k + 1) j *
          lowerSixRecoveryComplementWeightDrop k j := by
  have hold := lowerSixRecoveryLinearCarrier_mul_complementWeight k j
  have hnew := lowerSixRecoveryLinearCarrier_mul_complementWeight (k + 1) j
  unfold lowerSixRecoverySparseModeDrop
  refine Q'.eqv_trans _
    (lowerSixRecoveryLinearCarrier k j *
        lowerSixRecoveryComplementWeight k j +
      -(lowerSixRecoveryLinearCarrier (k + 1) j *
        lowerSixRecoveryComplementWeight (k + 1) j)) _
    (Q'.add_eqv_congr' (Q'.eqv_symm hold)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hnew))) ?_
  unfold lowerSixRecoveryLinearCarrierDrop
    lowerSixRecoveryComplementWeightDrop
  exact linear_abel_split_algebra _ _ _ _

/-- Sum-level form of the linear-preload split, including the exact adverse
terminal mode.  This is the compensated-Abel target for the generic within
family. -/
theorem lowerSixFixedCenterDrop_eqv_linearAbelSplit (k c : Nat) :
    lowerSixFixedCenterDrop k c ≈
      (finSum (fun j =>
          lowerSixRecoveryLinearCarrierDrop k j *
            lowerSixRecoveryComplementWeight k j) (2 * c) +
        finSum (fun j =>
          lowerSixRecoveryLinearCarrier (k + 1) j *
            lowerSixRecoveryComplementWeightDrop k j) (2 * c)) +
      lowerSixRecoveryTerminalDrop k (2 * c) := by
  have hterms := RationalTail.finSum_eqv_congr
    (fun j => lowerSixRecoverySparseModeDrop k (j + 1))
    (fun j =>
      lowerSixRecoveryLinearCarrierDrop k j *
          lowerSixRecoveryComplementWeight k j +
        lowerSixRecoveryLinearCarrier (k + 1) j *
          lowerSixRecoveryComplementWeightDrop k j)
    (fun j => lowerSixRecoverySparseModeDrop_eqv_linearAbelSplit k j)
    (2 * c)
  have hadd := RationalTail.finSum_add
    (fun j => lowerSixRecoveryLinearCarrierDrop k j *
      lowerSixRecoveryComplementWeight k j)
    (fun j => lowerSixRecoveryLinearCarrier (k + 1) j *
      lowerSixRecoveryComplementWeightDrop k j)
    (2 * c)
  refine Q'.eqv_trans _ _ _
    (lowerSixFixedCenterDrop_eqv_modeDrops k c) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _ hterms hadd)

theorem lowerSixFixedCenterDrop_eqv_linearReserve_add_debt (k c : Nat) :
    lowerSixFixedCenterDrop k c ≈
      lowerSixRecoveryLinearScaleReserve k c +
        lowerSixRecoveryLinearDriftDebt k c := by
  refine Q'.eqv_trans _ _ _
    (lowerSixFixedCenterDrop_eqv_linearAbelSplit k c) ?_
  unfold lowerSixRecoveryLinearScaleReserve lowerSixRecoveryLinearDriftDebt
  exact Q'.add_assoc_eqv _ _ _

private theorem linear_finSum_nonnegative (f : Nat → Q') : ∀ N,
    (∀ j, j < N → (0 : Q') ≤ f j) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (linear_finSum_nonnegative f N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

/-- Pointwise nonnegative carrier-scale drops make the first Abel component
a genuine reserve. -/
theorem lowerSixRecoveryLinearScaleReserve_nonnegative_of_carrierDrops
    {k c : Nat}
    (hcarrier : ∀ j, j < 2 * c →
      (0 : Q') ≤ lowerSixRecoveryLinearCarrierDrop k j) :
    (0 : Q') ≤ lowerSixRecoveryLinearScaleReserve k c := by
  unfold lowerSixRecoveryLinearScaleReserve
  apply linear_finSum_nonnegative
  intro j hj
  exact Q'.mul_nonneg _ _ (hcarrier j hj)
    (lowerSixRecoveryComplementWeight_nonnegative k j)

/-- Final consumer for the linear-preload route.  The generic within sign is
reduced to paying the explicit drift debt from the scale-drop reserve. -/
theorem lowerSixFixedCenterDrop_nonnegative_of_linearAbelPayment
    {k c : Nat}
    (hpayment : -lowerSixRecoveryLinearDriftDebt k c ≤
      lowerSixRecoveryLinearScaleReserve k c) :
    (0 : Q') ≤ lowerSixFixedCenterDrop k c := by
  let R := lowerSixRecoveryLinearScaleReserve k c
  let D := lowerSixRecoveryLinearDriftDebt k c
  have hdiff : (0 : Q') ≤ R + -(-D) :=
    Q'.sub_nonneg_of_le hpayment
  have hsum : (0 : Q') ≤ R + D :=
    Q'.le_trans' _ _ _ hdiff
      (Q'.le_of_eqv
        (Q'.add_eqv_congr_left R (-(-D)) D (Q'.neg_neg_eqv D)))
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (lowerSixFixedCenterDrop_eqv_linearReserve_add_debt k c)))

/-! ## Exact cutoff fences for the scale-reserve claim -/

/-- Linear-preload carrier-drop positivity is not valid on the whole original
range: at the first physical scale it fails immediately after mode ten.  The
finite bootstrap is therefore logically necessary before using this route. -/
theorem lowerSixRecoveryLinearCarrierDrop_48_10_negative :
    lowerSixRecoveryLinearCarrierDrop 48 10 < (0 : Q') := by
  unfold lowerSixRecoveryLinearCarrierDrop lowerSixRecoveryLinearCarrier
    lowerSixRecoveryModeSlope thetaResidualCellSlope harmW harmU
    ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
  decide

/-- At the first scale beyond the current finite bootstrap, the remote edge
of the physical fixed-center block has the favorable carrier-drop sign. -/
theorem lowerSixRecoveryLinearCarrierDrop_648_71_nonnegative :
    (0 : Q') ≤ lowerSixRecoveryLinearCarrierDrop 648 71 := by
  unfold lowerSixRecoveryLinearCarrierDrop lowerSixRecoveryLinearCarrier
    lowerSixRecoveryModeSlope thetaResidualCellSlope harmW harmU
    ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
  decide

#print axioms lowerSixRecoveryLinearCarrier_mul_complementWeight
#print axioms lowerSixRecoveryComplementWeight_antitone
#print axioms lowerSixRecoveryComplementWeight_scale_mono
#print axioms lowerSixRecoveryComplementWeightDrop_nonpositive
#print axioms lowerSixRecoveryLinearCarrier_nonnegative_succ
#print axioms lowerSixRecoveryLinearCarrier_nonpositive_pred
#print axioms lowerSixRecoveryLinearCarrierDrop_factor
#print axioms lowerSixRecoveryLinearCarrierDrop_nonnegative_of_slopeCarrier
#print axioms lowerSixRecoveryLinearSlopeDropCarrier_nonnegative_of_carrierDrop
#print axioms lowerSixRecoverySparseModeDrop_eqv_linearAbelSplit
#print axioms lowerSixFixedCenterDrop_eqv_linearAbelSplit
#print axioms lowerSixFixedCenterDrop_eqv_linearReserve_add_debt
#print axioms lowerSixRecoveryLinearScaleReserve_nonnegative_of_carrierDrops
#print axioms lowerSixFixedCenterDrop_nonnegative_of_linearAbelPayment
#print axioms lowerSixRecoveryLinearCarrierDrop_48_10_negative
#print axioms lowerSixRecoveryLinearCarrierDrop_648_71_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
