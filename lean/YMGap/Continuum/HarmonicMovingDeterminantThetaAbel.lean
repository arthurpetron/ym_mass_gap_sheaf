/-
Weighted Abel attack on the growing-head theta residual upper.

This successor leaves `HarmonicMovingDeterminantThetaCross` frozen.  It
connects that module's exact one-crossing cell slope to the physical residual
sum and records the sharp seven-unit cumulative target.  Pointwise allocation
is deliberately fenced off: the cancellation is genuinely cumulative.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaCross

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaAbel

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicMovingDeterminantAllTail
open YMGap.Continuum.HarmonicMovingDeterminantDirect
open YMGap.Continuum.HarmonicMovingDeterminantGrowingTail
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.HarmonicThetaLinearCarrier
open YMGap.Continuum.HarmonicThetaPascalClosure
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem abel_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "abel_ring" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Q'.neg_den, abel_neg_num_cast,
               Int.natCast_mul,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

/-! ## 1. Exact cell factorization -/

private theorem squared_base_edge_split (w : Q') (n : Nat) :
    w * qpow (w * w) (n * (n + 1)) ≈
      qpow (w * w) (n * n) * qpow w (2 * n + 1) := by
  have hexp : n * (n + 1) = n * n + n := by
    simp only [Nat.mul_add, Nat.mul_one]
  have hq : qpow (w * w) (n * (n + 1)) ≈
      qpow (w * w) (n * n) * qpow (w * w) n := by
    rw [hexp]
    exact HeatKernelRGStep.qpow_add (w * w) (n * n) n
  have hsquare : qpow (w * w) n ≈ qpow w n * qpow w n :=
    FusionQuotientCollapse.qpow_mul_self w n
  have hdouble : qpow (w * w) n ≈ qpow w (2 * n) := by
    refine Q'.eqv_trans _ _ _ hsquare ?_
    have hadd := HeatKernelRGStep.qpow_add w n n
    have he : n + n = 2 * n := by omega
    rw [he] at hadd
    exact Q'.eqv_symm hadd
  have hsucc : w * qpow w (2 * n) ≈ qpow w (2 * n + 1) := by
    change w * qpow w (2 * n) ≈ qpow w (2 * n) * w
    exact Q'.mul_comm_eqv _ _
  refine Q'.eqv_trans _
    (w * (qpow (w * w) (n * n) * qpow (w * w) n)) _
    (Q'.mul_eqv_congr_left w _ _ hq) ?_
  refine Q'.eqv_trans _
    (w * (qpow (w * w) (n * n) * qpow w (2 * n))) _
    (Q'.mul_eqv_congr_left w _ _
      (Q'.mul_eqv_congr_left (qpow (w * w) (n * n)) _ _ hdouble)) ?_
  refine Q'.eqv_trans _
    (qpow (w * w) (n * n) * (w * qpow w (2 * n))) _
    (by abel_ring) ?_
  exact Q'.mul_eqv_congr_left (qpow (w * w) (n * n)) _ _ hsucc

/-- Multiplying one residual cell by its positive index exposes the exact
integer-theta weight times the cleared monotone slope. -/
theorem thetaResidualCell_factor (w : Q') (n : Nat) :
    Q'.ofNat n * growingThetaResidualCell w n ≈
      integerThetaTerm w n * thetaResidualCellSlope w n := by
  have hp := squared_base_edge_split w n
  have hp' :
      w * (Q'.ofNat (n * (n + 1)) *
          qpow (w * w) (n * (n + 1))) ≈
        Q'.ofNat (n * (n + 1)) *
          (qpow (w * w) (n * n) * qpow w (2 * n + 1)) := by
    refine Q'.eqv_trans _
      (Q'.ofNat (n * (n + 1)) *
        (w * qpow (w * w) (n * (n + 1)))) _ (by abel_ring) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat (n * (n + 1))) _ _ hp
  unfold growingThetaResidualCell thetaResidualCellSlope
    integerThetaTerm halfThetaTerm
  refine Q'.eqv_trans _
    (Q'.ofNat n *
      (qpow ((1 : Q') + w) 3 *
          (Q'.ofNat (n * n) * qpow (w * w) (n * n)) +
        -(Q'.ofNat 8 *
          (Q'.ofNat (n * (n + 1)) *
            (qpow (w * w) (n * n) * qpow w (2 * n + 1)))))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (Q'.ofNat n) _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat 8) _ _
            hp')))
  · show _ ≈
      (Q'.ofNat (n * n) * qpow (w * w) (n * n)) *
        (Q'.ofNat n * qpow ((1 : Q') + w) 3 +
          -(Q'.ofNat 8 *
            (Q'.ofNat (n + 1) * qpow w (2 * n + 1))))
    abel_ring

/-- Exact finite distribution of the common theta factors over the cell
sum.  This is the cumulative identity needed before any Abel rearrangement. -/
theorem finSum_residualCell_eqv (w : Q') : ∀ N : Nat,
    finSum (fun j => growingThetaResidualCell w (j + 1)) N ≈
      qpow ((1 : Q') + w) 3 *
          finSum (fun j => integerThetaTerm w (j + 1)) N +
        -(Q'.ofNat 8 *
          (w * finSum (fun j => halfThetaTerm w (j + 1)) N))
  | 0 => by
      simp only [finSum_zero]
      abel_ring
  | N + 1 => by
      simp only [finSum_succ]
      refine Q'.eqv_trans _
        ((qpow ((1 : Q') + w) 3 *
              finSum (fun j => integerThetaTerm w (j + 1)) N +
            -(Q'.ofNat 8 *
              (w * finSum (fun j => halfThetaTerm w (j + 1)) N))) +
          growingThetaResidualCell w (N + 1)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ (finSum_residualCell_eqv w N)
      · unfold growingThetaResidualCell
        abel_ring

/-- The physical growing Pascal remainder is exactly the finite sum of the
signed residual cells `n=1,...,growingAnchor k+1`. -/
theorem growingPascalResidual_eqv_cellSum (k : Nat) :
    growingPascalResidual k ≈
      finSum (fun j =>
        growingThetaResidualCell (harmW k) (j + 1))
        (growingAnchor k + 1) := by
  have h := finSum_residualCell_eqv (harmW k) (growingAnchor k + 1)
  unfold growingPascalResidual growingHeadScaledThetaResidual
    integerThetaSum halfThetaSum
  exact Q'.eqv_symm h

/-! ## 2. Exact cumulative target and pointwise fence -/

/-- The stronger seven-unit cumulative gap.  Proving it for every harmonic
scale would immediately discharge the eight-unit premise because the demand
coefficient is at most one. -/
def sevenUnitResidualGap (k : Nat) : Q' :=
  Q'.ofNat 7 * (harmU k * harmU k) *
      integerThetaSum (harmW k) (growingAnchor k) +
    -growingPascalResidual k

/-- Per-cell contribution to the stronger seven-unit cumulative gap. -/
def sevenUnitCellGap (k n : Nat) : Q' :=
  Q'.ofNat 7 * (harmU k * harmU k) *
      integerThetaTerm (harmW k) n +
    -growingThetaResidualCell (harmW k) n

/-- Cleared per-cell gap slope.  Division by the positive index `n` gives
`7u² - residualSlope(n)/n`, hence a one-crossing decreasing profile. -/
def sevenUnitCellSlopeGap (k n : Nat) : Q' :=
  Q'.ofNat 7 * (harmU k * harmU k) * Q'.ofNat n +
    -thetaResidualCellSlope (harmW k) n

/-- Exact compatibility between the physical cell gap and its cleared slope. -/
theorem sevenUnitCellGap_factor (k n : Nat) :
    Q'.ofNat n * sevenUnitCellGap k n ≈
      integerThetaTerm (harmW k) n * sevenUnitCellSlopeGap k n := by
  have hcell := thetaResidualCell_factor (harmW k) n
  unfold sevenUnitCellGap sevenUnitCellSlopeGap
  refine Q'.eqv_trans _
    (Q'.ofNat n *
        (Q'.ofNat 7 * (harmU k * harmU k) *
          integerThetaTerm (harmW k) n) +
      -(Q'.ofNat n *
        growingThetaResidualCell (harmW k) n)) _ ?_ ?_
  · abel_ring
  · refine Q'.eqv_trans _
      (Q'.ofNat n *
          (Q'.ofNat 7 * (harmU k * harmU k) *
            integerThetaTerm (harmW k) n) +
        -(integerThetaTerm (harmW k) n *
          thetaResidualCellSlope (harmW k) n)) _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hcell)) ?_
    abel_ring

/-- The normalized cleared gap is antitone.  This is the exact reverse-sign
counterpart of `thetaResidualCellSlope_cross_mono`. -/
theorem sevenUnitCellSlopeGap_cross_antitone (k n : Nat) :
    Q'.ofNat n * sevenUnitCellSlopeGap k (n + 1) ≤
      Q'.ofNat (n + 1) * sevenUnitCellSlopeGap k n := by
  have hs := thetaResidualCellSlope_cross_mono
    (harmW_nonneg k) (harmW_le_one k) n
  have hneg := Q'.neg_le_neg hs
  have hadd := Q'.add_le_add_left
    ((Q'.ofNat n * Q'.ofNat (n + 1)) *
      (Q'.ofNat 7 * (harmU k * harmU k)))
    (-(Q'.ofNat n * thetaResidualCellSlope (harmW k) (n + 1)))
    (-(Q'.ofNat (n + 1) * thetaResidualCellSlope (harmW k) n)) hneg
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by
      unfold sevenUnitCellSlopeGap
      abel_ring))
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (by
        unfold sevenUnitCellSlopeGap
        abel_ring)))

/-- Distribution of the seven-unit cell gap over a finite prefix. -/
theorem finSum_sevenUnitCellGap_eqv (k : Nat) : ∀ N : Nat,
    finSum (fun j => sevenUnitCellGap k (j + 1)) N ≈
      Q'.ofNat 7 * (harmU k * harmU k) *
          finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N +
        -finSum (fun j =>
          growingThetaResidualCell (harmW k) (j + 1)) N
  | 0 => by
      simp only [finSum_zero]
      abel_ring
  | N + 1 => by
      simp only [finSum_succ]
      refine Q'.eqv_trans _
        ((Q'.ofNat 7 * (harmU k * harmU k) *
              finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N +
            -finSum (fun j =>
              growingThetaResidualCell (harmW k) (j + 1)) N) +
          sevenUnitCellGap k (N + 1)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (finSum_sevenUnitCellGap_eqv k N)
      · unfold sevenUnitCellGap
        abel_ring

/-- The scalar gap is exactly the terminal weighted Abel prefix. -/
theorem sevenUnitResidualGap_eqv_cellSum (k : Nat) :
    sevenUnitResidualGap k ≈
      finSum (fun j => sevenUnitCellGap k (j + 1))
        (growingAnchor k + 1) := by
  have hsum := finSum_sevenUnitCellGap_eqv k (growingAnchor k + 1)
  have hres := growingPascalResidual_eqv_cellSum k
  unfold sevenUnitResidualGap integerThetaSum
  refine Q'.eqv_trans _
    (Q'.ofNat 7 * (harmU k * harmU k) *
        finSum (fun j => integerThetaTerm (harmW k) (j + 1))
          (growingAnchor k + 1) +
      -finSum (fun j =>
        growingThetaResidualCell (harmW k) (j + 1))
        (growingAnchor k + 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ hres)
  · exact Q'.eqv_symm hsum

/-- The seven-unit gap directly implies the exact eight-unit premise consumed
by the frozen theta-cross theorem.  No renamed frontier is introduced. -/
theorem old_pascal_eight_budget_of_seven_gap {k : Nat} (hk : 38 ≤ k)
    (hseven : (0 : Q') ≤ sevenUnitResidualGap k) :
    normalizedDemandCoeff k * growingPascalResidual k ≤
      Q'.ofNat 8 * (harmU k * harmU k) *
        integerThetaSum (harmW k) (growingAnchor k) := by
  let R := growingPascalResidual k
  let I := integerThetaSum (harmW k) (growingAnchor k)
  let u2 := harmU k * harmU k
  let c := normalizedDemandCoeff k
  have hR0 : (0 : Q') ≤ R := by
    dsimp only [R, growingPascalResidual]
    exact harmonic_growing_head_scaled_theta_residual_nonnegative k
  have hc0 : (0 : Q') ≤ c := by
    dsimp only [c]
    exact HarmonicMovingDeterminantGrowingTail.normalizedDemandCoeff_nonneg hk
  have hc1 : c ≤ (1 : Q') := by
    have hs := HarmonicMovingDeterminantGrowingTail.normalizedDemandCoeff_le_shell k
    exact Q'.le_trans' _ _ _ hs (by unfold shellDropFraction; decide)
  have hcR : c * R ≤ R := by
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ R hc1 hR0
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv R))
  have hR7 : R ≤ Q'.ofNat 7 * u2 * I := by
    apply Q'.le_of_sub_nonneg
    exact hseven
  have hu20 : (0 : Q') ≤ u2 := by
    dsimp only [u2]
    exact Q'.mul_nonneg _ _ (harmU_nonneg k) (harmU_nonneg k)
  have hI0 : (0 : Q') ≤ I := by
    dsimp only [I]
    exact HarmonicThetaLinearCarrier.harmonic_integerThetaSum_nonnegative
      k (growingAnchor k)
  have h78 : Q'.ofNat 7 * u2 * I ≤ Q'.ofNat 8 * u2 * I := by
    have hc78 : Q'.ofNat 7 ≤ Q'.ofNat 8 := by decide
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ (u2 * I) hc78
      (Q'.mul_nonneg _ _ hu20 hI0)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by abel_ring))
      (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (by abel_ring)))
  exact Q'.le_trans' _ _ _ hcR (Q'.le_trans' _ _ _ hR7 h78)

/-! ## 3. Prefix Abel payment and the maximal-linear fence -/

private theorem abel_fsum_nonnegative_upto (f : Nat → Q') : ∀ N,
    (∀ i, i < N → (0 : Q') ≤ f i) → (0 : Q') ≤ fsum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, hf => by
      rw [fsum_succ]
      exact Q'.zero_le_add _ _
        (abel_fsum_nonnegative_upto f N
          (fun i hi => hf i (Nat.lt_trans hi (Nat.lt_succ_self N))))
        (hf N (Nat.lt_succ_self N))

/-- Constructive prefix-payment form of finite Abel summation.  Nonnegative
prefix carriers paired with a nonnegative decreasing weight give a
nonnegative weighted total. -/
theorem finite_abel_nonnegative_of_prefix
    (c x : Nat → Q') (n : Nat)
    (hprefix : ∀ p, p ≤ n → (0 : Q') ≤ abelPrefix c p)
    (hx : ∀ p, p ≤ n → (0 : Q') ≤ x p)
    (hdec : ∀ p, p < n → x (p + 1) ≤ x p) :
    (0 : Q') ≤ finSum (fun i => c i * x i) (n + 1) := by
  have hterm : (0 : Q') ≤ abelPrefix c n * x n :=
    Q'.mul_nonneg _ _ (hprefix n (Nat.le_refl _)) (hx n (Nat.le_refl _))
  have hinc : (0 : Q') ≤ abelIncrementSum c x n := by
    unfold abelIncrementSum
    apply abel_fsum_nonnegative_upto
    intro p hp
    exact Q'.mul_nonneg _ _ (hprefix p (Nat.le_of_lt hp))
      (Q'.sub_nonneg_of_le (hdec p hp))
  have hsum : (0 : Q') ≤
      abelPrefix c n * x n + abelIncrementSum c x n :=
    Q'.zero_le_add _ _ hterm hinc
  rw [← MovingCutoff.fsum_eq_finSum]
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (finite_abel c x n))

/-- The largest linear preload `6j` for which the complementary exponent is
globally nondecreasing from the first cell onward. -/
def maximalLinearAbelCarrier (k j : Nat) : Q' :=
  let n := j + 1
  Q'.ofNat n * qpow (harmW k) (6 * j) *
    sevenUnitCellSlopeGap k n

def maximalLinearAbelWeight (k j : Nat) : Q' :=
  qpow (harmW k) (2 * j * (j - 1) + 2)

theorem maximalLinearAbelExponent_succ (j : Nat) :
    2 * j * (j - 1) + 2 ≤
      2 * (j + 1) * ((j + 1) - 1) + 2 := by
  apply Nat.add_le_add_right _ 2
  simp only [Nat.mul_assoc]
  exact Nat.mul_le_mul_left 2
    (Nat.mul_le_mul (Nat.le_succ j) (by
      simpa only [Nat.add_sub_cancel] using Nat.sub_le j 1))

theorem maximalLinearAbelExponent_total (j : Nat) :
    6 * j + (2 * j * (j - 1) + 2) =
      2 * (j + 1) * (j + 1) := by
  cases j with
  | zero => decide
  | succ j =>
      simp only [Nat.succ_sub_one]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
      omega

private theorem squared_base_power_linear (w : Q') (n : Nat) :
    qpow (w * w) (n * n) ≈ qpow w (2 * n * n) := by
  have hs := FusionQuotientCollapse.qpow_mul_self w (n * n)
  have ha := HeatKernelRGStep.qpow_add w (n * n) (n * n)
  have he : n * n + n * n = 2 * n * n := by
    rw [Nat.two_mul]
    exact (Nat.add_mul n n n).symm
  rw [he] at ha
  exact Q'.eqv_trans _ _ _ hs (Q'.eqv_symm ha)

/-- The maximal-linear carrier and its decreasing complementary weight are
not merely a comparison device: their product is exactly the physical
seven-unit cell gap. -/
theorem maximalLinearAbelCarrier_mul_weight (k j : Nat) :
    maximalLinearAbelCarrier k j * maximalLinearAbelWeight k j ≈
      sevenUnitCellGap k (j + 1) := by
  let n := j + 1
  let r := 2 * j * (j - 1) + 2
  have hadd := HeatKernelRGStep.qpow_add (harmW k) (6 * j) r
  have hexp : 6 * j + r = 2 * n * n := by
    dsimp only [r, n]
    exact maximalLinearAbelExponent_total j
  rw [hexp] at hadd
  have hbase := squared_base_power_linear (harmW k) n
  have hp : qpow (harmW k) (6 * j) * qpow (harmW k) r ≈
      qpow (harmW k * harmW k) (n * n) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hadd) (Q'.eqv_symm hbase)
  dsimp only [r, n] at hp
  have hscaled :
      Q'.ofNat n *
          (maximalLinearAbelCarrier k j * maximalLinearAbelWeight k j) ≈
        integerThetaTerm (harmW k) n * sevenUnitCellSlopeGap k n := by
    unfold maximalLinearAbelCarrier maximalLinearAbelWeight integerThetaTerm
    dsimp only [n, r]
    refine Q'.eqv_trans _
      ((Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) *
        ((qpow (harmW k) (6 * j) *
          qpow (harmW k) (2 * j * (j - 1) + 2)) *
        sevenUnitCellSlopeGap k (j + 1))) _ (by abel_ring) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) *
        (qpow (harmW k * harmW k) ((j + 1) * (j + 1)) *
        sevenUnitCellSlopeGap k (j + 1))) _ ?_ (by abel_ring)
    exact Q'.mul_eqv_congr_left
      (Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) _ _
      (Q'.mul_eqv_congr_right _ _
        (sevenUnitCellSlopeGap k (j + 1)) hp)
  have hfactor := sevenUnitCellGap_factor k n
  have hcancel :
      Q'.ofNat n *
          (maximalLinearAbelCarrier k j * maximalLinearAbelWeight k j) ≈
        Q'.ofNat n * sevenUnitCellGap k n :=
    Q'.eqv_trans _ _ _ hscaled (Q'.eqv_symm hfactor)
  dsimp only [n] at hcancel ⊢
  exact Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos j) hcancel

theorem maximalLinearAbelWeight_antitone (k j : Nat) :
    maximalLinearAbelWeight k (j + 1) ≤ maximalLinearAbelWeight k j := by
  unfold maximalLinearAbelWeight
  exact HeatKernelRGStep.qpow_antitone (harmW_nonneg k) (harmW_le_one k)
    _ _ (maximalLinearAbelExponent_succ j)

/-! ## 4. Exact Dirichlet form behind crossing compensation -/

/-- Literal square root of an integer-theta cell inside the rational power
substrate.  No analytic square-root operation is used. -/
def thetaRootTerm (w : Q') (n : Nat) : Q' :=
  Q'.ofNat n * qpow w (n * n)

def thetaDirichletCell (w : Q') (n : Nat) : Q' :=
  (thetaRootTerm w n + -thetaRootTerm w (n + 1)) *
    (thetaRootTerm w n + -thetaRootTerm w (n + 1))

theorem thetaRootTerm_sq (w : Q') (n : Nat) :
    thetaRootTerm w n * thetaRootTerm w n ≈ integerThetaTerm w n := by
  have hs := FusionQuotientCollapse.qpow_mul_self w (n * n)
  unfold thetaRootTerm integerThetaTerm
  refine Q'.eqv_trans _
    ((Q'.ofNat n * Q'.ofNat n) *
      (qpow w (n * n) * qpow w (n * n))) _ (by abel_ring) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat n * Q'.ofNat n) * qpow (w * w) (n * n)) _
    (Q'.mul_eqv_congr_left (Q'.ofNat n * Q'.ofNat n) _ _
      (Q'.eqv_symm hs)) (by abel_ring)

private theorem squared_base_edge_as_root_product (w : Q') (n : Nat) :
    w * qpow (w * w) (n * (n + 1)) ≈
      qpow w (n * n) * qpow w ((n + 1) * (n + 1)) := by
  have hp := squared_base_edge_split w n
  have hb := squared_base_power_linear w n
  have ha := HeatKernelRGStep.qpow_add w (2 * n * n) (2 * n + 1)
  have he : 2 * n * n + (2 * n + 1) =
      n * n + (n + 1) * (n + 1) := by
    have htwo : 2 * n * n = n * n + n * n := by
      rw [Nat.two_mul]
      exact Nat.add_mul n n n
    have hsucc : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
      omega
    rw [htwo, hsucc]
    omega
  rw [he] at ha
  have hright :
      qpow (w * w) (n * n) * qpow w (2 * n + 1) ≈
        qpow w (n * n + (n + 1) * (n + 1)) := by
    refine Q'.eqv_trans _
      (qpow w (2 * n * n) * qpow w (2 * n + 1)) _
      (Q'.mul_eqv_congr_right _ _ _ hb) ?_
    exact Q'.eqv_symm ha
  have hadd := HeatKernelRGStep.qpow_add w (n * n) ((n + 1) * (n + 1))
  exact Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _ _ _ hright hadd)

theorem thetaRootTerm_adj_mul (w : Q') (n : Nat) :
    thetaRootTerm w n * thetaRootTerm w (n + 1) ≈
      w * halfThetaTerm w n := by
  have hp := squared_base_edge_as_root_product w n
  unfold thetaRootTerm halfThetaTerm
  refine Q'.eqv_trans _
    (Q'.ofNat (n * (n + 1)) *
      (qpow w (n * n) * qpow w ((n + 1) * (n + 1)))) _
    (by abel_ring) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (n * (n + 1)) *
      (w * qpow (w * w) (n * (n + 1)))) _
    (Q'.mul_eqv_congr_left (Q'.ofNat (n * (n + 1))) _ _
      (Q'.eqv_symm hp)) (by abel_ring)

private def dirichletPolyL : RingNormaliser.PolyExpr :=
  .mul (.const 8) (.mul (.var 0) (.var 1))

private def dirichletPolyR : RingNormaliser.PolyExpr :=
  let a := RingNormaliser.PolyExpr.var 0
  let b := RingNormaliser.PolyExpr.var 1
  .add
    (.mul (.const 4) (.add (.mul a a) (.mul b b)))
    (.neg (.mul (.const 4)
      (.mul (.add a (.neg b)) (.add a (.neg b)))))

private theorem dirichletPoly_normal :
    RingNormaliser.normalize dirichletPolyL =
      RingNormaliser.normalize dirichletPolyR := by
  decide

private theorem eight_ab_dirichlet (a b : Q') :
    Q'.ofNat 8 * (a * b) ≈
      Q'.ofNat 4 * (a * a + b * b) +
        -(Q'.ofNat 4 * ((a + -b) * (a + -b))) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    dirichletPolyL dirichletPolyR dirichletPoly_normal
    (fun
      | 0 => a
      | _ => b)
  simpa [dirichletPolyL, dirichletPolyR,
    RingNormaliser.eval] using h

/-- Adjacent half-theta mass is a trapezoid minus the exact discrete
Dirichlet square. -/
theorem halfTheta_trapezoid_dirichlet (w : Q') (n : Nat) :
    Q'.ofNat 8 * (w * halfThetaTerm w n) ≈
      Q'.ofNat 4 *
          (integerThetaTerm w n + integerThetaTerm w (n + 1)) +
        -(Q'.ofNat 4 * thetaDirichletCell w n) := by
  let a := thetaRootTerm w n
  let b := thetaRootTerm w (n + 1)
  have hab : a * b ≈ w * halfThetaTerm w n :=
    thetaRootTerm_adj_mul w n
  have haa : a * a ≈ integerThetaTerm w n := thetaRootTerm_sq w n
  have hbb : b * b ≈ integerThetaTerm w (n + 1) :=
    thetaRootTerm_sq w (n + 1)
  refine Q'.eqv_trans _ (Q'.ofNat 8 * (a * b)) _
    (Q'.mul_eqv_congr_left (Q'.ofNat 8) _ _ (Q'.eqv_symm hab)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * (a * a + b * b) +
      -(Q'.ofNat 4 * thetaDirichletCell w n)) _ ?_ ?_
  · dsimp only [a, b]
    unfold thetaDirichletCell
    exact eight_ab_dirichlet _ _
  have hs : a * a + b * b ≈
      integerThetaTerm w n + integerThetaTerm w (n + 1) :=
    Q'.add_eqv_congr' haa hbb
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hs)

/-- Exact fence: even the maximal globally monotone linear preload has a
negative terminal carrier at the first all-tail scale.  Therefore the plain
prefix Abel lemma above cannot close the seven-unit target without a
crossing-adapted compensation. -/
theorem maximal_linear_abel_terminal_prefix_fails_k38 :
    ¬ ((0 : Q') ≤ abelPrefix (maximalLinearAbelCarrier 38)
      (growingAnchor 38)) := by
  unfold abelPrefix maximalLinearAbelCarrier sevenUnitCellSlopeGap
    thetaResidualCellSlope growingAnchor harmW harmU
    ReciprocalBernoulliUpper.oneSub unit fsum qpow
  decide

/-- Exact threshold audit: the cumulative seven-unit inequality already holds
at the first all-tail scale. -/
theorem seven_unit_residual_gap_k38 :
    (0 : Q') ≤ sevenUnitResidualGap 38 := by
  unfold sevenUnitResidualGap growingPascalResidual
    growingHeadScaledThetaResidual integerThetaSum halfThetaSum
    integerThetaTerm halfThetaTerm growingAnchor harmW harmU
    ReciprocalBernoulliUpper.oneSub unit finSum qpow
  decide

/-- The corresponding pointwise strengthening is false already at cell five.
Any valid proof of the seven-unit bound must retain prefix/tail cancellation. -/
theorem seven_unit_pointwise_fails_k38_n5 :
    ¬ (growingThetaResidualCell (harmW 38) 5 ≤
      Q'.ofNat 7 * (harmU 38 * harmU 38) *
        integerThetaTerm (harmW 38) 5) := by
  unfold growingThetaResidualCell integerThetaTerm halfThetaTerm
    harmW harmU ReciprocalBernoulliUpper.oneSub unit qpow
  decide

#print axioms thetaResidualCell_factor
#print axioms finSum_residualCell_eqv
#print axioms growingPascalResidual_eqv_cellSum
#print axioms sevenUnitResidualGap
#print axioms sevenUnitCellGap
#print axioms sevenUnitCellSlopeGap
#print axioms sevenUnitCellGap_factor
#print axioms sevenUnitCellSlopeGap_cross_antitone
#print axioms finSum_sevenUnitCellGap_eqv
#print axioms sevenUnitResidualGap_eqv_cellSum
#print axioms old_pascal_eight_budget_of_seven_gap
#print axioms seven_unit_residual_gap_k38
#print axioms seven_unit_pointwise_fails_k38_n5
#print axioms finite_abel_nonnegative_of_prefix
#print axioms maximalLinearAbelCarrier
#print axioms maximalLinearAbelWeight
#print axioms maximalLinearAbelExponent_succ
#print axioms maximalLinearAbelExponent_total
#print axioms maximalLinearAbelCarrier_mul_weight
#print axioms maximalLinearAbelWeight_antitone
#print axioms thetaRootTerm
#print axioms thetaDirichletCell
#print axioms thetaRootTerm_sq
#print axioms thetaRootTerm_adj_mul
#print axioms halfTheta_trapezoid_dirichlet
#print axioms maximal_linear_abel_terminal_prefix_fails_k38

end YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
