/-
`EndpointCutoffTwoParameter` — an exact finite-cutoff continuity estimate
coupling the endpoint tail to the weak-coupling margin.

For the fundamental `p = 2` vacuum-normalized fused eigenvalue, this module
proves

  |vacNorm_N(w,1) - endpointRate(N)|
    <= vacLip(N) * (1-w),

where `vacLip(N)` is an explicit finite sum of SU(2) dimensions and Casimirs.
Combining it with the exact endpoint defect gives

  normEigShift_N(w,1)
    <= endpointTail(N) + (vacLip(N)+3/2) * (1-w).

The estimate is deliberately crude but completely derived: its constants are
finite character sums, not hypotheses or measured inputs.  It also exposes a
sharp scheduling diagnostic.  With the quadratic cutoff `Ncut(k)=(k+2)^2`,
the continuity coefficient is still bounded below by the positive `a=0`
adjacent-character contribution.  Hence pairing this Lipschitz estimate with
an asymptotic-freedom margin of order `1/(k+B)` leaves a harmonic lower
envelope.  `naiveContinuity_partial_unbounded` machine-checks that the partial
sums of the resulting *bound* are unbounded.  This refutes the naive pairing;
it does not assert a lower bound on the actual spectral defect.

Constructive contract: exact `Q'`/`Nat`, no `Classical`, `Real`,
`native_decide`, axioms, holes, or frontier carrier.
-/

import YMGap.Continuum.EndpointCutoffTailClose
import YMGap.Continuum.FusedAmplitudeDerivation
import YMGap.Continuum.LaplaceMarginDeep
import YMGap.Continuum.ContinuumYMStack
import YMGap.Continuum.EpsilonSummability
import YMGap.Continuum.FusionMarginMono
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Continuum.FusedEnvelope
import YMGap.Continuum.FusedRatioCorridor
import YMGap.Continuum.RenormalizedContinuumZ1

namespace YMGap.Continuum.EndpointCutoffTwoParameter

set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.EigenvalueShiftBridge
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.EndpointCutoffTailClose
open YMGap.Continuum.EndpointCutoffTailFormula
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.FusedEnvelope
open YMGap.Continuum.FusedRatioCorridor
open YMGap.Continuum.LaplaceMarginDeep
open YMGap.Continuum.RenormalizedContinuumZ1
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.EpsilonSummability
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-! ## 1. Derived finite-character Lipschitz constants -/

/-- Lipschitz coefficient for one product of character coefficients. -/
def pairLip (a b : Nat) : Q' :=
  (dimQ a * dimQ b) * Q'.ofNat (c4 a + c4 b)

/-- Finite-character Lipschitz coefficient for the adjacent correlation. -/
def adjLip (N : Nat) : Q' :=
  fsum (fun a => pairLip a (a + 1)) N

/-- Finite-character Lipschitz coefficient for the diagonal norm. -/
def diagLip (N : Nat) : Q' :=
  fsum (fun a => pairLip a a) (N + 1)

/-- Quotient Lipschitz coefficient.  The endpoint factors are themselves exact
finite character sums. -/
def vacLip (N : Nat) : Q' :=
  adjLip N * coordNormSq (1 : Q') N +
    adjCorr (1 : Q') N * diagLip N

theorem pairLip_nonneg (a b : Nat) : (0 : Q') ≤ pairLip a b := by
  unfold pairLip
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (dimQ_nonneg a) (dimQ_nonneg b))
    (zero_le_ofNat (c4 a + c4 b))

theorem adjLip_nonneg (N : Nat) : (0 : Q') ≤ adjLip N :=
  fsum_nonneg (fun a => pairLip_nonneg a (a + 1)) N

theorem diagLip_nonneg (N : Nat) : (0 : Q') ≤ diagLip N :=
  fsum_nonneg (fun a => pairLip_nonneg a a) (N + 1)

theorem vacLip_nonneg (N : Nat) : (0 : Q') ≤ vacLip N := by
  unfold vacLip
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (adjLip_nonneg N)
      (coordNormSq_nonneg (by decide) N))
    (Q'.mul_nonneg _ _ (adjCorr_nonneg (by decide) N)
      (diagLip_nonneg N))

/-- One finite character-product differs from its endpoint by at most the
derived dimension–Casimir coefficient times `1-w`. -/
theorem pair_deficit_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (a b : Nat) :
    dimQ a * dimQ b - coeffW w a * coeffW w b ≤
      pairLip a b * ((1 : Q') - w) := by
  let d := dimQ a * dimQ b
  let n := c4 a + c4 b
  have hp := oneSub_qpow_le hw0 hw1 n
  have hd : (0 : Q') ≤ d :=
    Q'.mul_nonneg _ _ (dimQ_nonneg a) (dimQ_nonneg b)
  have hscaled : d * ((1 : Q') - qpow w n) ≤
      d * (Q'.ofNat n * ((1 : Q') - w)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hp hd
  have hL :
      (dimQ a * dimQ b - coeffW w a * coeffW w b) ≈
        d * ((1 : Q') - qpow w n) := by
    have hc := coeffW_mul_split w a b
    unfold d n
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (dimQ a * dimQ b) _ _
        (Q'.neg_eqv_congr _ _ hc)) ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (dimQ a * dimQ b) 1
        (-(qpow w (c4 a + c4 b)))) ?_
    exact Q'.add_eqv_congr'
      (Q'.mul_one_eqv (dimQ a * dimQ b))
      (Q'.mul_neg_eqv (dimQ a * dimQ b)
        (qpow w (c4 a + c4 b)))
  have hR :
      d * (Q'.ofNat n * ((1 : Q') - w)) ≈
        pairLip a b * ((1 : Q') - w) := by
    unfold d n pairLip
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (dimQ a * dimQ b)
        (Q'.ofNat (c4 a + c4 b)) ((1 : Q') - w))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hR))

private theorem fsum_deficit_eqv (f g : Nat → Q') (n : Nat) :
    fsum f n - fsum g n ≈ fsum (fun i => f i - g i) n := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (fsum f n) _ _
      (Q'.eqv_symm (fsum_neg g n))) ?_
  exact Q'.eqv_symm (fsum_add f (fun i => -(g i)) n)

/-- Adjacent-correlation endpoint deficit, with an explicit finite-sum
Lipschitz coefficient. -/
theorem adjCorr_endpoint_deficit_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (N : Nat) :
    adjCorr (1 : Q') N - adjCorr w N ≤
      adjLip N * ((1 : Q') - w) := by
  have hterm : ∀ a,
      dimQ a * dimQ (a + 1) - coeffW w a * coeffW w (a + 1) ≤
        pairLip a (a + 1) * ((1 : Q') - w) :=
    fun a => pair_deficit_le hw0 hw1 a (a + 1)
  have hsum := fsum_mono_lt N (fun a _ => hterm a)
  have hL : adjCorr (1 : Q') N - adjCorr w N ≈
      fsum (fun a => dimQ a * dimQ (a + 1) -
        coeffW w a * coeffW w (a + 1)) N := by
    unfold adjCorr
    refine Q'.eqv_trans _ _ _
      (fsum_deficit_eqv
        (fun a => coeffW (1 : Q') a * coeffW (1 : Q') (a + 1))
        (fun a => coeffW w a * coeffW w (a + 1)) N) ?_
    exact fsum_eqv_congr _ _ (fun a =>
      Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (coeffW_at_one_eqv a))
          (Q'.mul_eqv_congr_left (dimQ a) _ _
            (coeffW_at_one_eqv (a + 1))))) N
  have hR :
      fsum (fun a => pairLip a (a + 1) * ((1 : Q') - w)) N ≈
        adjLip N * ((1 : Q') - w) := by
    unfold adjLip
    exact Q'.eqv_symm
      (fsum_mul_const (fun a => pairLip a (a + 1)) ((1 : Q') - w) N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hR))

/-- Diagonal-norm endpoint deficit, with an explicit finite-sum Lipschitz
coefficient. -/
theorem coordNormSq_endpoint_deficit_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (N : Nat) :
    coordNormSq (1 : Q') N - coordNormSq w N ≤
      diagLip N * ((1 : Q') - w) := by
  have hterm : ∀ a,
      dimQ a * dimQ a - coeffW w a * coeffW w a ≤
        pairLip a a * ((1 : Q') - w) :=
    fun a => pair_deficit_le hw0 hw1 a a
  have hsum := fsum_mono_lt (N + 1) (fun a _ => hterm a)
  have hL : coordNormSq (1 : Q') N - coordNormSq w N ≈
      fsum (fun a => dimQ a * dimQ a - coeffW w a * coeffW w a) (N + 1) := by
    unfold coordNormSq
    refine Q'.eqv_trans _ _ _
      (fsum_deficit_eqv
        (fun a => coeffW (1 : Q') a * coeffW (1 : Q') a)
        (fun a => coeffW w a * coeffW w a) (N + 1)) ?_
    exact fsum_eqv_congr _ _ (fun a =>
      Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (coeffW_at_one_eqv a))
          (Q'.mul_eqv_congr_left (dimQ a) _ _
            (coeffW_at_one_eqv a)))) (N + 1)
  have hR :
      fsum (fun a => pairLip a a * ((1 : Q') - w)) (N + 1) ≈
        diagLip N * ((1 : Q') - w) := by
    unfold diagLip
    exact Q'.eqv_symm
      (fsum_mul_const (fun a => pairLip a a) ((1 : Q') - w) (N + 1))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hR))

/-! ## 2. A constructive quotient-continuity lemma -/

private theorem divPos_add_const {num den B : Q'} (hden : (0 : Q') < den) :
    Q'.divPos (num + B * den) den hden ≈ Q'.divPos num den hden + B := by
  apply divPos_eqv_of_eqv_mul hden
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv (Q'.divPos num den hden) B den) ?_
  exact Q'.add_eqv_congr'
    (Q'.divPos_mul_eqv num den hden) (Q'.eqv_refl (B * den))

/-- If numerator and denominator both increase to endpoint values, their
positive quotient changes by at most the explicit cross-deficit budget. -/
theorem ratio_endpoint_continuity
    {a A d D eA eD : Q'}
    (ha0 : (0 : Q') ≤ a) (hA0 : (0 : Q') ≤ A)
    (hd1 : (1 : Q') ≤ d) (hD1 : (1 : Q') ≤ D)
    (haA : a ≤ A) (hdD : d ≤ D)
    (heA0 : (0 : Q') ≤ eA) (heD0 : (0 : Q') ≤ eD)
    (hAdef : A - a ≤ eA) (hDdef : D - d ≤ eD) :
    absQ (Q'.divPos a d (pos_of_one_le hd1) +
      -(Q'.divPos A D (pos_of_one_le hD1))) ≤ eA * D + A * eD := by
  let B := eA * D + A * eD
  have hd0 : (0 : Q') ≤ d := Q'.le_trans' _ _ _ (by decide) hd1
  have hD0 : (0 : Q') ≤ D := Q'.le_trans' _ _ _ (by decide) hD1
  have hB0 : (0 : Q') ≤ B := by
    unfold B
    exact Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ heA0 hD0) (Q'.mul_nonneg _ _ hA0 heD0)
  have hAle : A ≤ a + eA := ContinuumGapModulus.le_add_of_sub_le hAdef
  have hDle : D ≤ d + eD := ContinuumGapModulus.le_add_of_sub_le hDdef
  have hprod1 : (1 : Q') ≤ D * d := by
    have h := Q'.mul_le_mul_of_nonneg hD1 hd1 hD0 (by decide : (0 : Q') ≤ (1 : Q'))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv 1)) h
  have hBscale : B ≤ B * (D * d) := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ _ hprod1 hB0
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv B)) h
  have hup0 : a * D ≤ A * d + A * eD := by
    have h1 : a * D ≤ A * D :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ haA hD0
    have h2 : A * D ≤ A * (d + eD) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hDle hA0
    exact Q'.le_trans' _ _ _ h1
      (Q'.le_trans' _ _ _ h2
        (Q'.le_of_eqv (Q'.mul_add_eqv A d eD)))
  have hlo0 : A * d ≤ a * D + eA * D := by
    have h1 : A * d ≤ (a + eA) * d :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hAle hd0
    have h2 : (a + eA) * d ≤ (a + eA) * D := by
      have hsum0 : (0 : Q') ≤ a + eA := Q'.zero_le_add _ _ ha0 heA0
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ hdD hsum0
    refine Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 ?_)
    exact Q'.le_of_eqv (Q'.add_mul_eqv a eA D)
  have hupCross : a * D ≤ (A + B * D) * d := by
    have hBpart : A * d + A * eD ≤ A * d + B * (D * d) := by
      apply Q'.add_le_add_left
      have hAeD_B : A * eD ≤ B :=
        Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg (A * eD) (eA * D)
            (Q'.mul_nonneg _ _ heA0 hD0))
          (Q'.le_of_eqv (Q'.add_comm_eqv (A * eD) (eA * D)))
      exact Q'.le_trans' _ _ _ hAeD_B hBscale
    refine Q'.le_trans' _ _ _ hup0 (Q'.le_trans' _ _ _ hBpart ?_)
    exact Q'.le_of_eqv (by ring_qeqv :
      A * d + B * (D * d) ≈ (A + B * D) * d)
  have hloCross : A * d ≤ (a + B * d) * D := by
    have hBpart : a * D + eA * D ≤ a * D + B * (d * D) := by
      apply Q'.add_le_add_left
      have heAD_B : eA * D ≤ B :=
        Q'.add_le_self_of_nonneg (eA * D) (A * eD)
          (Q'.mul_nonneg _ _ hA0 heD0)
      have hscale' : B ≤ B * (d * D) :=
        Q'.le_trans' _ _ _ hBscale
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left B _ _ (Q'.mul_comm_eqv D d)))
      exact Q'.le_trans' _ _ _ heAD_B hscale'
    refine Q'.le_trans' _ _ _ hlo0 (Q'.le_trans' _ _ _ hBpart ?_)
    exact Q'.le_of_eqv (by ring_qeqv :
      a * D + B * (d * D) ≈ (a + B * d) * D)
  have hupRatio : Q'.divPos a d (pos_of_one_le hd1) ≤
      Q'.divPos A D (pos_of_one_le hD1) + B := by
    have hq := FusionMarginMono.divPos_le_divPos_of_cross
      a d (A + B * D) D (pos_of_one_le hd1) (pos_of_one_le hD1) hupCross
    exact Q'.le_trans' _ _ _ hq
      (Q'.le_of_eqv (divPos_add_const (pos_of_one_le hD1)))
  have hloRatio : Q'.divPos A D (pos_of_one_le hD1) ≤
      Q'.divPos a d (pos_of_one_le hd1) + B := by
    have hq := FusionMarginMono.divPos_le_divPos_of_cross
      A D (a + B * d) d (pos_of_one_le hD1) (pos_of_one_le hd1) hloCross
    exact Q'.le_trans' _ _ _ hq
      (Q'.le_of_eqv (divPos_add_const (pos_of_one_le hd1)))
  apply absQ_le
  · have hn := Q'.neg_le_neg hloRatio
    have h := Q'.add_le_add_left
      (Q'.divPos a d (pos_of_one_le hd1)) _ _ hn
    refine Q'.le_trans' _ _ _ ?_ h
    let x := Q'.divPos a d (pos_of_one_le hd1)
    have he : x + -(x + B) ≈ -B := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left x _ _ (Q'.neg_add_eqv x B)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv x (-x) (-B))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-B) (Q'.add_neg_self_eqv x)) ?_
      exact QPoly.q_zero_add_eqv (-B)
    exact Q'.le_of_eqv (Q'.eqv_symm he)
  · have h := Q'.add_le_add_right _ _
      (-(Q'.divPos A D (pos_of_one_le hD1))) hupRatio
    refine Q'.le_trans' _ _ _ h ?_
    let y := Q'.divPos A D (pos_of_one_le hD1)
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv y B (-y)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left y _ _ (Q'.add_comm_eqv B (-y))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv y (-y) B)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ B (Q'.add_neg_self_eqv y)) ?_
    exact QPoly.q_zero_add_eqv B

/-! ## 3. Fundamental spectral continuity and the two-parameter defect -/

theorem coordNormSq_ge_one {w : Q'} (hw0 : (0 : Q') ≤ w) (N : Nat) :
    (1 : Q') ≤ coordNormSq w N := by
  have hv : (1 : Q') ≤ boxSum w N 0 := vacuum_ge_one hw0 N
  have hb : bondMovedCoeff N w 2 0 ≈ boxSum w N 0 :=
    bondMovedCoeff_eq_boxSum N 0
  have hd : bondMovedCoeff N w 2 0 ≈ coordNormSq w N := g0_diag N
  exact Q'.le_trans' _ _ _ hv
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_symm hb) hd))

private theorem vacNorm_fundamental_eq_ratio {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    vacNorm N 2 (by decide) hw0 hw1 1 ≈
      Q'.divPos (adjCorr w N) (coordNormSq w N)
        (pos_of_one_le (coordNormSq_ge_one hw0 N)) := by
  let A := adjCorr w N
  let D := coordNormSq w N
  let r := Q'.divPos A D (pos_of_one_le (coordNormSq_ge_one hw0 N))
  have hnum : bondMovedCoeff N w 2 1 ≈ Q'.ofNat 2 * A :=
    Q'.eqv_trans _ _ _ (bondMovedCoeff_eq_boxSum N 1)
      (boxSum_one_eq_twice_adjCorr w N)
  have hden : dimQ 1 * bondMovedCoeff N w 2 0 ≈ Q'.ofNat 2 * D := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (dimQ 1) _ _ (g0_diag (w := w) N)) ?_
    exact Q'.mul_eqv_congr_right _ _ D (by decide)
  have hrD : r * D ≈ A := Q'.divPos_mul_eqv A D _
  apply divPos_eqv_of_eqv_mul
  refine Q'.eqv_trans _ _ _ hnum ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (Q'.eqv_symm hrD)) ?_
  refine Q'.eqv_trans _ _ _ (by ring_qeqv :
    Q'.ofNat 2 * (r * D) ≈ r * (Q'.ofNat 2 * D)) ?_
  exact Q'.mul_eqv_congr_left r _ _ (Q'.eqv_symm hden)

/-- **Finite-cutoff endpoint continuity of the fundamental fused
eigenvalue.**  The modulus is the explicit finite character sum `vacLip N`. -/
theorem vacNorm_fundamental_endpoint_continuity {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    absQ (vacNorm N 2 (by decide) hw0 hw1 1 + -(endpointRate N)) ≤
      vacLip N * ((1 : Q') - w) := by
  let a := adjCorr w N
  let A := adjCorr (1 : Q') N
  let d := coordNormSq w N
  let D := coordNormSq (1 : Q') N
  let u := (1 : Q') - w
  let eA := adjLip N * u
  let eD := diagLip N * u
  have hu0 : (0 : Q') ≤ u := Q'.sub_nonneg_of_le hw1
  have ha0 : (0 : Q') ≤ a := adjCorr_nonneg hw0 N
  have hA0 : (0 : Q') ≤ A := adjCorr_nonneg (by decide) N
  have hd1 : (1 : Q') ≤ d := coordNormSq_ge_one hw0 N
  have hD1 : (1 : Q') ≤ D := coordNormSq_ge_one (by decide) N
  have haA : a ≤ A := by
    unfold a A adjCorr
    exact FusedAmplitudeDerivation.fsum_le_fsum' (fun i =>
      Q'.mul_le_mul_of_nonneg
        (coeffW_mono_w hw0 hw1 i)
        (coeffW_mono_w hw0 hw1 (i + 1))
        (coeffW_nonneg (by decide) i)
        (coeffW_nonneg hw0 (i + 1))) N
  have hdD : d ≤ D := by
    unfold d D coordNormSq
    exact FusedAmplitudeDerivation.fsum_le_fsum' (fun i =>
      Q'.mul_le_mul_of_nonneg
        (coeffW_mono_w hw0 hw1 i)
        (coeffW_mono_w hw0 hw1 i)
        (coeffW_nonneg (by decide) i)
        (coeffW_nonneg hw0 i)) (N + 1)
  have heA0 : (0 : Q') ≤ eA := Q'.mul_nonneg _ _ (adjLip_nonneg N) hu0
  have heD0 : (0 : Q') ≤ eD := Q'.mul_nonneg _ _ (diagLip_nonneg N) hu0
  have hAdef : A - a ≤ eA := adjCorr_endpoint_deficit_le hw0 hw1 N
  have hDdef : D - d ≤ eD := coordNormSq_endpoint_deficit_le hw0 hw1 N
  have hratio := ratio_endpoint_continuity ha0 hA0 hd1 hD1 haA hdD
    heA0 heD0 hAdef hDdef
  have hv := vacNorm_fundamental_eq_ratio hw0 hw1 N
  have hV := vacNorm_endpoint_formula N
  have harg :
      vacNorm N 2 (by decide) hw0 hw1 1 + -(endpointRate N) ≈
        Q'.divPos a d (pos_of_one_le hd1) +
          -(Q'.divPos A D (pos_of_one_le hD1)) := by
    exact Q'.add_eqv_congr' hv
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm hV)
          (vacNorm_fundamental_eq_ratio (by decide) (by decide) N)))
  have hB : eA * D + A * eD ≈ vacLip N * u := by
    unfold eA eD u vacLip A D
    ring_qeqv
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (absQ_eqv_congr harg))
    (Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hB))

private def q32 : Q' := Q'.mkPos 3 2 (by decide)

/-- The retuned fundamental eigenvalue differs from its endpoint by at most
`(3/2)(1-w)`. -/
theorem retEig_fundamental_endpoint_deficit {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    absQ ((1 : Q') - retEig 2 (by decide) w 1) ≤
      q32 * ((1 : Q') - w) := by
  have hr0 : (0 : Q') ≤ renormWFix 2 (by decide) w := renormWFix_nonneg hw0 2 (by decide)
  have hr1 : renormWFix 2 (by decide) w ≤ (1 : Q') := renormWFix_le_one hw1 2 (by decide)
  have hp := oneSub_qpow_le hr0 hr1 (c4 1)
  have hbase : (1 : Q') - renormWFix 2 (by decide) w ≈
      Q'.mkPos 1 2 (by decide) * ((1 : Q') - w) := by
    have hmargin : ((1 : Q') - renormWFix 2 (by decide) w) ≈
        renormTauFix 2 (by decide) w := by
      unfold renormWFix
      have ha : (-((1 : Q') + (-(renormTauFix 2 (by decide) w)))) ≈
          ((-1 : Q') + renormTauFix 2 (by decide) w) := by
        refine Q'.eqv_trans _ _ _
          (Q'.neg_add_eqv (1 : Q') (-(renormTauFix 2 (by decide) w))) ?_
        exact Q'.add_eqv_congr_left _ _ _
          (Q'.neg_neg_eqv (renormTauFix 2 (by decide) w))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 1 _ _ ha) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-1)
          (renormTauFix 2 (by decide) w))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv (1 : Q'))) ?_
      exact QPoly.q_zero_add_eqv _
    refine Q'.eqv_trans _ _ _ hmargin ?_
    unfold renormTauFix
    exact Q'.mul_comm_eqv ((1 : Q') - w) (Q'.mkPos 1 2 (by decide))
  have hlin : Q'.ofNat (c4 1) * ((1 : Q') - renormWFix 2 (by decide) w) ≈
      q32 * ((1 : Q') - w) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (c4 1)) _ _ hbase) ?_
    unfold q32
    ring_qeqv
  have hnon : (0 : Q') ≤ (1 : Q') - retEig 2 (by decide) w 1 := by
    exact Q'.sub_nonneg_of_le (qpow_le_one hr0 hr1 (c4 1))
  have habs : absQ ((1 : Q') - retEig 2 (by decide) w 1) ≈
      ((1 : Q') - retEig 2 (by decide) w 1) := by
    unfold absQ
    rw [if_pos ((Q'.zero_le_iff_num_nonneg _).mp hnon)]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv habs)
    (Q'.le_trans' _ _ _ hp (Q'.le_of_eqv hlin))

/-- **Two-parameter finite-cutoff defect bound.**  The exact endpoint tail and
the exact finite-character continuity coefficient appear separately. -/
theorem normEigShift_fundamental_two_parameter {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    normEigShift N 2 (by decide) hw0 hw1 1 ≤
      endpointTail N + (vacLip N + q32) * ((1 : Q') - w) := by
  let v := vacNorm N 2 (by decide) hw0 hw1 1
  let e := endpointRate N
  let r := retEig 2 (by decide) w 1
  have hdecomp : v + (-r) ≈ (v + (-e)) + ((e + (-1)) + ((1 : Q') + (-r))) := by
    refine Q'.eqv_symm ?_
    have hinner : (v + (-e)) + (e + (-1)) ≈ v + (-1) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv v (-e) (e + (-1))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left v _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (-e) e (-1)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left v _ _
          (Q'.add_eqv_congr_right _ _ (-1) (Q'.neg_add_self_eqv e))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left v _ _ (QPoly.q_zero_add_eqv (-1))) ?_
      exact Q'.eqv_refl _
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (v + (-e)) (e + (-1))
        ((1 : Q') + (-r)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ ((1 : Q') + (-r)) hinner) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv v (-1) ((1 : Q') + (-r))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left v _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (-1) 1 (-r)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left v _ _
        (Q'.add_eqv_congr_right _ _ (-r) (Q'.neg_add_self_eqv 1))) ?_
    exact Q'.add_eqv_congr_left v _ _ (QPoly.q_zero_add_eqv (-r))
  have htri1 := absQ_add_le (v + (-e)) ((e + (-1)) + ((1 : Q') + (-r)))
  have htri2 := absQ_add_le (e + (-1)) ((1 : Q') + (-r))
  have hcont := vacNorm_fundamental_endpoint_continuity hw0 hw1 N
  have hend : absQ (e + (-1)) ≈ endpointTail N := by
    unfold e
    have h := one_sub_endpointRate N
    have hneg : endpointRate N + (-1) ≈ -(endpointTail N) := by
      refine Q'.eqv_trans _ _ _ ?_ (Q'.neg_eqv_congr _ _ h)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _
        (Q'.neg_add_eqv (1 : Q') (-(endpointRate N))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (-1) _ _
          (Q'.neg_neg_eqv (endpointRate N))) ?_
      exact Q'.add_comm_eqv (-1) (endpointRate N)
    refine Q'.eqv_trans _ _ _ (absQ_eqv_congr hneg) ?_
    unfold absQ
    rw [if_neg]
    · exact Q'.neg_neg_eqv _
    · intro hz
      have hle0 : endpointTail N ≤ (0 : Q') := by
        have hn : (0 : Q') ≤ -(endpointTail N) := by
          rw [Q'.zero_le_iff_num_nonneg]
          exact hz
        exact Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (Q'.neg_neg_eqv _)) (Q'.neg_le_neg hn)
      exact (by decide : ¬ ((0 : Q') < (0 : Q')))
        (ClusteringImpliesGap.lt_of_lt_of_le (endpointTail_pos N) hle0)
  have hret := retEig_fundamental_endpoint_deficit hw0 hw1
  show absQ (v + (-r)) ≤ _
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (absQ_eqv_congr hdecomp)) ?_
  refine Q'.le_trans' _ _ _ htri1 ?_
  have hsum : absQ (v + (-e)) +
      (absQ (e + (-1)) + absQ ((1 : Q') + (-r))) ≤
      vacLip N * ((1 : Q') - w) +
        (endpointTail N + q32 * ((1 : Q') - w)) :=
    Q'.add_le_add hcont (Q'.add_le_add
      (Q'.le_of_eqv hend) hret)
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_left _ _ _ htri2) ?_
  refine Q'.le_trans' _ _ _ hsum ?_
  exact Q'.le_of_eqv (by ring_qeqv :
    vacLip N * ((1 : Q') - w) +
        (endpointTail N + q32 * ((1 : Q') - w)) ≈
      endpointTail N + (vacLip N + q32) * ((1 : Q') - w))

/-! ## 4. The quadratic-cutoff / harmonic-margin no-go for this crude bound -/

/-- The finite-character quotient Lipschitz coefficient retains a positive
endpoint contribution at every nonzero cutoff. -/
theorem vacLip_ge_six {N : Nat} (hN : 1 ≤ N) :
    Q'.ofNat 6 ≤ vacLip N := by
  have hpair : pairLip 0 1 ≈ Q'.ofNat 6 := by decide
  have hAdj : pairLip 0 1 ≤ adjLip N := by
    unfold adjLip
    rw [MovingCutoff.fsum_eq_finSum]
    exact ClusteringImpliesGap.finSum_ge_single
      (fun a => pairLip a (a + 1))
      (fun a => pairLip_nonneg a (a + 1)) N 0 hN
  have hD : (1 : Q') ≤ coordNormSq (1 : Q') N :=
    coordNormSq_ge_one (by decide) N
  have hprod : adjLip N ≤ adjLip N * coordNormSq (1 : Q') N := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ _ hD (adjLip_nonneg N)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv (adjLip N))) h
  have hsum : adjLip N * coordNormSq (1 : Q') N ≤ vacLip N := by
    unfold vacLip
    exact Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ (adjCorr_nonneg (by decide) N) (diagLip_nonneg N))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpair)
    (Q'.le_trans' _ _ _ hAdj (Q'.le_trans' _ _ _ hprod hsum))

/-- The naive continuity term obtained by plugging the quadratic moving cutoff
into an AF harmonic margin.  This is an upper-bound sequence, not the actual
defect. -/
def naiveContinuityTerm (afr : AFRateModulus) (k : Nat) : Q' :=
  vacLip (Ncut k) * harmTerm afr.B afr.B_pos k

/-- The scheduled continuity bound has a fixed positive harmonic lower
envelope. -/
theorem naiveContinuity_harmonic_lower (afr : AFRateModulus) (k : Nat) :
    Q'.ofNat 6 * harmTerm afr.B afr.B_pos k ≤
      naiveContinuityTerm afr k := by
  unfold naiveContinuityTerm
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (vacLip_ge_six (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Ncut_pos k))))
    (harmTerm_nonneg afr.B_pos k)

/-- **Machine-refuted naive pairing.**  For every candidate finite budget,
the partial sums of the continuity *bound* produced by combining
`Ncut(k)=(k+2)^2` with a harmonic AF margin exceed that budget.  Thus this
finite-cutoff Lipschitz estimate cannot itself supply a summable scale defect;
a sharper two-parameter/Edgeworth cancellation is necessary. -/
theorem naiveContinuity_partial_unbounded (afr : AFRateModulus) (R : Q') :
    ∃ M : Nat, R < fsum (naiveContinuityTerm afr) M :=
  harmonicLower_partial_unbounded afr (Q'.ofNat 6) (by decide)
    (naiveContinuityTerm afr) (naiveContinuity_harmonic_lower afr) R

end YMGap.Continuum.EndpointCutoffTwoParameter

#print axioms YMGap.Continuum.EndpointCutoffTwoParameter.pair_deficit_le
#print axioms YMGap.Continuum.EndpointCutoffTwoParameter.adjCorr_endpoint_deficit_le
#print axioms YMGap.Continuum.EndpointCutoffTwoParameter.coordNormSq_endpoint_deficit_le
#print axioms YMGap.Continuum.EndpointCutoffTwoParameter.ratio_endpoint_continuity
#print axioms YMGap.Continuum.EndpointCutoffTwoParameter.vacNorm_fundamental_endpoint_continuity
#print axioms YMGap.Continuum.EndpointCutoffTwoParameter.normEigShift_fundamental_two_parameter
#print axioms YMGap.Continuum.EndpointCutoffTwoParameter.vacLip_ge_six
#print axioms YMGap.Continuum.EndpointCutoffTwoParameter.naiveContinuity_partial_unbounded
