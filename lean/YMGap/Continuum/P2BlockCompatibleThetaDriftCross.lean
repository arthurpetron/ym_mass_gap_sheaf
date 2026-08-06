/-
Track 11.7-fusion / R3k -- cancellation-preserving fixed-cutoff drift cross.

# Result

The normalized coarse theta slope is rewritten without division as the exact
fixed-cutoff covariance

    A(w0,N) D(w4,N) - A(w4,N) D(w0,N).

This covariance is then opened as one rectangular double sum of explicit
mode-pair kernels.  The scale-free `16/75` budget from
`P2BlockCompatibleThetaScaleInvariant` compiles the covariance inequality,
together with the independent fine dyadic reserve, directly to the existing
`BlockCompatibleP2CoefficientSandwichFromSeven` consumer.

The new structure is an honest analytic frontier.  No inhabitant is asserted.

# Constructivity

Primitive finite sums, exact `Q'` setoid algebra, and reflected polynomial
normalization only.  No `Classical`, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
import YMGap.Continuum.FusionCoreStep

namespace YMGap.Continuum.P2BlockCompatibleThetaDriftCross

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- One diagonal coefficient-square summand. -/
def fixedCutoffDiagTerm (w : Q') (s : Nat) : Q' :=
  coeffW w s * coeffW w s

/-- One adjacent-correlation summand. -/
def fixedCutoffAdjTerm (w : Q') (s : Nat) : Q' :=
  coeffW w s * coeffW w (s + 1)

/-- Mode-pair kernel for the adverse normalized-deficit change from `low` to
`high` at a common cutoff. -/
def fixedCutoffDriftKernel
    (low high : Q') (i j : Nat) : Q' :=
  fixedCutoffAdjTerm low i * fixedCutoffDiagTerm high j +
    -(fixedCutoffAdjTerm high i * fixedCutoffDiagTerm low j)

/-- Casimir exponent carried by one adjacent product. -/
def fixedCutoffAdjExponent (i : Nat) : Nat := c4 i + c4 (i + 1)

/-- Casimir exponent carried by one diagonal square. -/
def fixedCutoffDiagExponent (j : Nat) : Nat := c4 j + c4 j

/-- Common positive dimension coefficient of a mode-pair kernel. -/
def fixedCutoffKernelDim (i j : Nat) : Q' :=
  Q'.ofNat (((i + 1) * (i + 2)) * ((j + 1) * (j + 1)))

/-- The two-base power cross left after the common dimension coefficient is
removed. -/
def fixedCutoffPowerCross
    (low high : Q') (leftExponent rightExponent : Nat) : Q' :=
  qpow low leftExponent * qpow high rightExponent +
    -(qpow high leftExponent * qpow low rightExponent)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem coeffW_product_monomial_local
    (w : Q') (left right : Nat) :
    coeffW w left * coeffW w right ≈
      Q'.ofNat ((left + 1) * (right + 1)) *
        qpow w (c4 left + c4 right) := by
  unfold coeffW dimQ
  refine Q'.eqv_trans _ _ _
    (FusionResidualBound.mul_four_regroup
      (Q'.ofNat (left + 1)) (qpow w (c4 left))
      (Q'.ofNat (right + 1)) (qpow w (c4 right))) ?_
  exact mul_eqv_both_local
    (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv _ _))
    (Q'.eqv_symm (HeatKernelRGStep.qpow_add w _ _))

private theorem product_monomial_cross_local
    (low high : Q') (i j : Nat) :
    fixedCutoffAdjTerm low i * fixedCutoffDiagTerm high j ≈
      fixedCutoffKernelDim i j *
        (qpow low (fixedCutoffAdjExponent i) *
          qpow high (fixedCutoffDiagExponent j)) := by
  have ha := coeffW_product_monomial_local low i (i + 1)
  have hd := coeffW_product_monomial_local high j j
  unfold fixedCutoffAdjTerm fixedCutoffDiagTerm
  refine Q'.eqv_trans _ _ _ (mul_eqv_both_local ha hd) ?_
  refine Q'.eqv_trans _ _ _
    (FusionResidualBound.mul_four_regroup
      (Q'.ofNat ((i + 1) * (i + 1 + 1)))
      (qpow low (c4 i + c4 (i + 1)))
      (Q'.ofNat ((j + 1) * (j + 1)))
      (qpow high (c4 j + c4 j))) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv _ _))

private def factorCrossL : RingNormaliser.PolyExpr :=
  .add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2)))

private def factorCrossR : RingNormaliser.PolyExpr :=
  .mul (.var 0) (.add (.var 1) (.neg (.var 2)))

private theorem factorCross_normal :
    RingNormaliser.normalize factorCrossL =
      RingNormaliser.normalize factorCrossR := by decide

private theorem factor_cross_local (C X Y : Q') :
    C * X + -(C * Y) ≈ C * (X + -Y) := by
  simpa [factorCrossL, factorCrossR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      factorCrossL factorCrossR factorCross_normal
      (fun | 0 => C | 1 => X | _ => Y))

/-- Exact monomial form of each covariance cell.  The sign depends only on
the ordering of the adjacent and diagonal Casimir exponents; all dimension
factors have been removed as one nonnegative scalar. -/
theorem fixedCutoffDriftKernel_eq_dim_mul_powerCross
    (low high : Q') (i j : Nat) :
    fixedCutoffDriftKernel low high i j ≈
      fixedCutoffKernelDim i j *
        fixedCutoffPowerCross low high
          (fixedCutoffAdjExponent i) (fixedCutoffDiagExponent j) := by
  have hlow := product_monomial_cross_local low high i j
  have hhigh := product_monomial_cross_local high low i j
  unfold fixedCutoffDriftKernel fixedCutoffPowerCross
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hlow (Q'.neg_eqv_congr _ _ hhigh)) ?_
  exact factor_cross_local _ _ _

private theorem mul_swap_last_local (A B C : Q') :
    (A * C) * B ≈ (A * B) * C := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A C B) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left A _ _ (Q'.mul_comm_eqv C B)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv A B C)

private theorem fixedCutoffPowerCross_nonpos_of_rightExponent_le
    {low high : Q'} (hlow : (0 : Q') <= low) (hlh : low <= high)
    {leftExponent rightExponent : Nat}
    (hexp : rightExponent <= leftExponent) :
    fixedCutoffPowerCross low high leftExponent rightExponent <= (0 : Q') := by
  let delta := leftExponent - rightExponent
  let C := qpow low rightExponent * qpow high rightExponent
  have hsum : rightExponent + delta = leftExponent :=
    Nat.add_sub_of_le hexp
  have hlowSplit : qpow low leftExponent ≈
      qpow low rightExponent * qpow low delta := by
    rw [← hsum]
    exact HeatKernelRGStep.qpow_add low rightExponent delta
  have hhighSplit : qpow high leftExponent ≈
      qpow high rightExponent * qpow high delta := by
    rw [← hsum]
    exact HeatKernelRGStep.qpow_add high rightExponent delta
  have hleft : qpow low leftExponent * qpow high rightExponent ≈
      C * qpow low delta := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hlowSplit) ?_
    exact mul_swap_last_local _ _ _
  have hright : qpow high leftExponent * qpow low rightExponent ≈
      C * qpow high delta := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hhighSplit) ?_
    refine Q'.eqv_trans _ _ _ (mul_swap_last_local _ _ _) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv (qpow high rightExponent)
        (qpow low rightExponent))
  have hpow : qpow low delta <= qpow high delta :=
    HeatKernelGap.qpow_mono hlow hlh delta
  have hC : (0 : Q') <= C :=
    Q'.mul_nonneg _ _
      (qpow_nonneg low hlow rightExponent)
      (qpow_nonneg high
        (Q'.le_trans' _ _ _ hlow hlh) rightExponent)
  have hscaled : C * qpow low delta <= C * qpow high delta :=
    Q'.mul_le_mul_of_nonneg_left _ _ C hpow hC
  have hterms :
      qpow low leftExponent * qpow high rightExponent <=
        qpow high leftExponent * qpow low rightExponent :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))
  have hadd := Q'.add_le_add_right _ _
    (-(qpow high leftExponent * qpow low rightExponent)) hterms
  unfold fixedCutoffPowerCross
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (Q'.add_neg_self_eqv
        (qpow high leftExponent * qpow low rightExponent)))

private theorem fixedCutoffPowerCross_nonneg_of_leftExponent_le
    {low high : Q'} (hlow : (0 : Q') <= low) (hlh : low <= high)
    {leftExponent rightExponent : Nat}
    (hexp : leftExponent <= rightExponent) :
    (0 : Q') <= fixedCutoffPowerCross low high leftExponent rightExponent := by
  let delta := rightExponent - leftExponent
  let C := qpow low leftExponent * qpow high leftExponent
  have hsum : leftExponent + delta = rightExponent :=
    Nat.add_sub_of_le hexp
  have hlowSplit : qpow low rightExponent ≈
      qpow low leftExponent * qpow low delta := by
    rw [← hsum]
    exact HeatKernelRGStep.qpow_add low leftExponent delta
  have hhighSplit : qpow high rightExponent ≈
      qpow high leftExponent * qpow high delta := by
    rw [← hsum]
    exact HeatKernelRGStep.qpow_add high leftExponent delta
  have hleft : qpow low leftExponent * qpow high rightExponent ≈
      C * qpow high delta := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hhighSplit) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hright : qpow high leftExponent * qpow low rightExponent ≈
      C * qpow low delta := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hlowSplit) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv (qpow high leftExponent)
        (qpow low leftExponent))
  have hpow : qpow low delta <= qpow high delta :=
    HeatKernelGap.qpow_mono hlow hlh delta
  have hC : (0 : Q') <= C :=
    Q'.mul_nonneg _ _
      (qpow_nonneg low hlow leftExponent)
      (qpow_nonneg high
        (Q'.le_trans' _ _ _ hlow hlh) leftExponent)
  have hscaled : C * qpow low delta <= C * qpow high delta :=
    Q'.mul_le_mul_of_nonneg_left _ _ C hpow hC
  have hterms :
      qpow high leftExponent * qpow low rightExponent <=
        qpow low leftExponent * qpow high rightExponent :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hright)
      (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hleft))
  unfold fixedCutoffPowerCross
  exact Q'.sub_nonneg_of_le hterms

private theorem c4_mono_local {a b : Nat} (hab : a <= b) : c4 a <= c4 b := by
  unfold c4
  exact Nat.mul_le_mul hab (Nat.add_le_add_right hab 2)

theorem fixedCutoffDiagExponent_le_adjExponent_of_le
    {i j : Nat} (hji : j <= i) :
    fixedCutoffDiagExponent j <= fixedCutoffAdjExponent i := by
  have h0 := c4_mono_local hji
  have h1 := c4_mono_local (show j <= i + 1 by omega)
  unfold fixedCutoffDiagExponent fixedCutoffAdjExponent
  omega

theorem fixedCutoffAdjExponent_le_diagExponent_of_lt
    {i j : Nat} (hij : i < j) :
    fixedCutoffAdjExponent i <= fixedCutoffDiagExponent j := by
  have h0 := c4_mono_local (show i <= j by omega)
  have h1 := c4_mono_local (show i + 1 <= j by omega)
  unfold fixedCutoffDiagExponent fixedCutoffAdjExponent
  omega

/-- Lower-triangular cells are favorable: when `j <= i`, increasing the heat
weight makes the adjacent exponent drift at least as fast as the diagonal
exponent, so the adverse covariance cell is nonpositive. -/
theorem fixedCutoffDriftKernel_nonpos_of_diag_le_adj
    {low high : Q'} (hlow : (0 : Q') <= low) (hlh : low <= high)
    {i j : Nat} (hji : j <= i) :
    fixedCutoffDriftKernel low high i j <= (0 : Q') := by
  have hpow := fixedCutoffPowerCross_nonpos_of_rightExponent_le
    hlow hlh (fixedCutoffDiagExponent_le_adjExponent_of_le hji)
  have hdim : (0 : Q') <= fixedCutoffKernelDim i j := by
    unfold fixedCutoffKernelDim
    exact HeatKernelRGStep.zero_le_ofNat _
  have hprod := Q'.mul_nonpos_of_nonneg_nonpos hdim hpow
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (fixedCutoffDriftKernel_eq_dim_mul_powerCross low high i j)) hprod

/-- Strictly upper-triangular cells are adverse: when `i < j`, their sign is
nonnegative.  Together with the previous theorem this gives an exact index
partition for every cutoff, with no evaluation of the growing sums. -/
theorem fixedCutoffDriftKernel_nonneg_of_adj_lt_diag
    {low high : Q'} (hlow : (0 : Q') <= low) (hlh : low <= high)
    {i j : Nat} (hij : i < j) :
    (0 : Q') <= fixedCutoffDriftKernel low high i j := by
  have hpow := fixedCutoffPowerCross_nonneg_of_leftExponent_le
    hlow hlh (fixedCutoffAdjExponent_le_diagExponent_of_lt hij)
  have hdim : (0 : Q') <= fixedCutoffKernelDim i j := by
    unfold fixedCutoffKernelDim
    exact HeatKernelRGStep.zero_le_ofNat _
  have hprod := Q'.mul_nonneg _ _ hdim hpow
  exact Q'.le_trans' _ _ _ hprod
    (Q'.ge_of_eqv
      (fixedCutoffDriftKernel_eq_dim_mul_powerCross low high i j))

/-- Division-free covariance numerator for the common-cutoff normalized
deficit drift. -/
def fixedCutoffDeficitDriftCross
    (low high : Q') (N : Nat) : Q' :=
  adjCorr low N * coordNormSq high N +
    -(adjCorr high N * coordNormSq low N)

private theorem rect_sub_eq
    (F G : Nat → Nat → Q') (m n : Nat) :
    fsum (fun i => fsum (F i) n) m +
        -(fsum (fun i => fsum (G i) n) m) ≈
      fsum (fun i => fsum (fun j => F i j + -(G i j)) n) m := by
  have hneg : -(fsum (fun i => fsum (G i) n) m) ≈
      fsum (fun i => fsum (fun j => -(G i j)) n) m := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (CubeRatioBounds.fsum_neg (fun i => fsum (G i) n) m)) ?_
    exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
      Q'.eqv_symm (CubeRatioBounds.fsum_neg (G i) n)) m
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hneg) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (CubeRatioBounds.fsum_add
      (fun i => fsum (F i) n)
      (fun i => fsum (fun j => -(G i j)) n) m)) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
    Q'.eqv_symm (CubeRatioBounds.fsum_add
      (F i) (fun j => -(G i j)) n)) m

/-- Proof-about-computation expansion of the fixed-cutoff covariance.  The
growing quotient is replaced by a structurally recursive rectangular sum. -/
theorem fixedCutoffDeficitDriftCross_eq_kernelSum
    (low high : Q') (N : Nat) :
    fixedCutoffDeficitDriftCross low high N ≈
      fsum (fun i =>
        fsum (fun j => fixedCutoffDriftKernel low high i j) (N + 1)) N := by
  let AL := fun i => fixedCutoffAdjTerm low i
  let AH := fun i => fixedCutoffAdjTerm high i
  let DL := fun j => fixedCutoffDiagTerm low j
  let DH := fun j => fixedCutoffDiagTerm high j
  have hleft := FusionCoreStepRoundB.fsum_mul_fsum AL DH N (N + 1)
  have hright := FusionCoreStepRoundB.fsum_mul_fsum AH DL N (N + 1)
  have hAL : adjCorr low N = fsum AL N := rfl
  have hAH : adjCorr high N = fsum AH N := rfl
  have hDL : coordNormSq low N = fsum DL (N + 1) := rfl
  have hDH : coordNormSq high N = fsum DH (N + 1) := rfl
  unfold fixedCutoffDeficitDriftCross
  rw [hAL, hAH, hDL, hDH]
  refine Q'.eqv_trans _
    (fsum (fun i => fsum (fun j => AL i * DH j) (N + 1)) N +
      -(fsum (fun i => fsum (fun j => AH i * DL j) (N + 1)) N)) _
    (Q'.add_eqv_congr' hleft (Q'.neg_eqv_congr _ _ hright)) ?_
  refine Q'.eqv_trans _ _ _
    (rect_sub_eq
      (fun i j => AL i * DH j)
      (fun i j => AH i * DL j) N (N + 1)) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
    CubeRatioBounds.fsum_eqv_congr _ _ (fun j => by
      unfold fixedCutoffDriftKernel AL AH DL DH
      exact Q'.eqv_refl _) (N + 1)) N

/-! ## Square core, terminal column, and paired cancellation -/

/-- The square part of the rectangular covariance.  Both indices range over
the adjacent-edge carrier `0,...,N-1`. -/
def fixedCutoffDriftCore (low high : Q') (N : Nat) : Q' :=
  fsum (fun i =>
    fsum (fun j => fixedCutoffDriftKernel low high i j) N) N

/-- The unmatched diagonal mode `j=N` in the rectangular covariance.  This
is the only term not available to square-core index exchange. -/
def fixedCutoffDriftBoundary (low high : Q') (N : Nat) : Q' :=
  fsum (fun i => fixedCutoffDriftKernel low high i N) N

/-- Exact core/boundary decomposition.  In particular, any sharp common-cutoff
bound can spend its analytic budget independently on a cancellative square
core and on one explicit terminal column. -/
theorem fixedCutoffDeficitDriftCross_eq_core_add_boundary
    (low high : Q') (N : Nat) :
    fixedCutoffDeficitDriftCross low high N ≈
      fixedCutoffDriftCore low high N +
        fixedCutoffDriftBoundary low high N := by
  refine Q'.eqv_trans _ _ _
    (fixedCutoffDeficitDriftCross_eq_kernelSum low high N) ?_
  have hsplit :
      fsum (fun i =>
        fsum (fun j => fixedCutoffDriftKernel low high i j) (N + 1)) N ≈
      fsum (fun i =>
        fsum (fun j => fixedCutoffDriftKernel low high i j) N +
          fixedCutoffDriftKernel low high i N) N := by
    exact CubeRatioBounds.fsum_eqv_congr _ _
      (fun _ => Q'.eqv_refl _) N
  refine Q'.eqv_trans _ _ _ hsplit ?_
  exact Q'.eqv_trans _ _ _
    (CubeRatioBounds.fsum_add
      (fun i => fsum (fun j => fixedCutoffDriftKernel low high i j) N)
      (fun i => fixedCutoffDriftKernel low high i N) N)
    (Q'.eqv_refl _)

/-- The square-core kernel paired with its transposed index. -/
def fixedCutoffDriftPairKernel
    (low high : Q') (i j : Nat) : Q' :=
  fixedCutoffDriftKernel low high i j +
    fixedCutoffDriftKernel low high j i

private theorem rect_add_eq
    (F G : Nat → Nat → Q') (n : Nat) :
    fsum (fun i => fsum (F i) n) n +
        fsum (fun i => fsum (G i) n) n ≈
      fsum (fun i => fsum (fun j => F i j + G i j) n) n := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (CubeRatioBounds.fsum_add
      (fun i => fsum (F i) n)
      (fun i => fsum (G i) n) n)) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
    Q'.eqv_symm (CubeRatioBounds.fsum_add (F i) (G i) n)) n

/-- Twice the square core is exactly the finite sum of paired kernels.  This
is the proof-about-computation reduction that exposes all cancellation before
any inequality is applied. -/
theorem fixedCutoffDriftCore_twice_eq_pairSum
    (low high : Q') (N : Nat) :
    fixedCutoffDriftCore low high N +
        fixedCutoffDriftCore low high N ≈
      fsum (fun i =>
        fsum (fun j => fixedCutoffDriftPairKernel low high i j) N) N := by
  have hswap := CubeRatioBounds.fsum_swap
    (fun i j => fixedCutoffDriftKernel low high i j) N N
  unfold fixedCutoffDriftCore
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hswap) ?_
  exact rect_add_eq
    (fun i j => fixedCutoffDriftKernel low high i j)
    (fun i j => fixedCutoffDriftKernel low high j i) N

/-- Honest all-tail covariance target.  The coarse field is now a rectangular
kernel budget with a fixed dimensionless constant.  The fine field remains
the independent coefficient-space even/odd reserve. -/
structure BlockCompatibleP2DimensionlessDriftCrossTailFromSeven : Type where
  coarseCross : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let D0 := coordNormSq w0 (blockNcut k)
    let D4 := coordNormSq w4 (blockNcut k)
    fixedCutoffDeficitDriftCross w0 w4 (blockNcut k) <=
      (blockNormalizedSlopeCoeff *
        (blockQuadraticDrift k * blockLength k)) * (D0 * D4)
  fineReserve : forall k, 7 <= k ->
    let w1 := blockWeight (k + 1)
    let w4 := qpow w1 4
    let D1 := coordNormSq w1 (blockNcut (k + 1))
    let D4 := coordNormSq w4 (blockNcut k)
    let T1 := coefficientDeficit w1 (blockNcut (k + 1))
    let T4 := coefficientDeficit w4 (blockNcut k)
    Q'.ofNat 2 * (D4 * T1) +
        blockParityDebt k * (D1 * D4) <=
      D1 * T4

private def deficitCrossShiftL : RingNormaliser.PolyExpr :=
  let D0 := RingNormaliser.PolyExpr.var 0
  let A0 := RingNormaliser.PolyExpr.var 1
  let D4 := RingNormaliser.PolyExpr.var 2
  let A4 := RingNormaliser.PolyExpr.var 3
  .add
    (.mul (.add D0 (.neg A0)) D4)
    (.add (.mul A0 D4) (.neg (.mul A4 D0)))

private def deficitCrossShiftR : RingNormaliser.PolyExpr :=
  let D0 := RingNormaliser.PolyExpr.var 0
  let D4 := RingNormaliser.PolyExpr.var 2
  let A4 := RingNormaliser.PolyExpr.var 3
  .mul D0 (.add D4 (.neg A4))

private theorem deficitCrossShift_normal :
    RingNormaliser.normalize deficitCrossShiftL =
      RingNormaliser.normalize deficitCrossShiftR := by decide

private theorem deficit_cross_shift
    (D0 A0 D4 A4 : Q') :
    (D0 + -A0) * D4 + (A0 * D4 + -(A4 * D0)) ≈
      D0 * (D4 + -A4) := by
  simpa [deficitCrossShiftL, deficitCrossShiftR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      deficitCrossShiftL deficitCrossShiftR deficitCrossShift_normal
      (fun | 0 => D0 | 1 => A0 | 2 => D4 | _ => A4))

/-- The covariance and fine reserve compile directly to the exact
division-free coefficient sandwich consumed by the three checked prefix
cells. -/
def BlockCompatibleP2DimensionlessDriftCrossTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2DimensionlessDriftCrossTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven where
  cell := fun k hk => by
    let w0 := blockWeight k
    let w1 := blockWeight (k + 1)
    let w4 := qpow w1 4
    let D0 := coordNormSq w0 (blockNcut k)
    let D1 := coordNormSq w1 (blockNcut (k + 1))
    let D4 := coordNormSq w4 (blockNcut k)
    let A0 := adjCorr w0 (blockNcut k)
    let A4 := adjCorr w4 (blockNcut k)
    let T0 := coefficientDeficit w0 (blockNcut k)
    let T1 := coefficientDeficit w1 (blockNcut (k + 1))
    let T4 := coefficientDeficit w4 (blockNcut k)
    let B := (blockNormalizedSlopeCoeff *
      (blockQuadraticDrift k * blockLength k)) * (D0 * D4)
    let E := blockParityDebt k * (D0 * D4)
    have hcross : fixedCutoffDeficitDriftCross w0 w4 (blockNcut k) <= B := by
      simpa only [w0, w4, D0, D4, B] using T.coarseCross k hk
    have hbudget : B ≈ E := by
      dsimp only [B, E]
      exact Q'.mul_eqv_congr_right _ _ (D0 * D4)
        (normalizedSlopeBudget_eqv_debt k)
    have hcrossDebt : fixedCutoffDeficitDriftCross w0 w4 (blockNcut k) <= E :=
      Q'.le_trans' _ _ _ hcross (Q'.le_of_eqv hbudget)
    have hadd := Q'.add_le_add_left (T0 * D4)
      (fixedCutoffDeficitDriftCross w0 w4 (blockNcut k)) E hcrossDebt
    have hleft : T0 * D4 +
        fixedCutoffDeficitDriftCross w0 w4 (blockNcut k) ≈ D0 * T4 := by
      dsimp only [T0, T4, D0, D4, A0, A4]
      unfold coefficientDeficit fixedCutoffDeficitDriftCross
      exact deficit_cross_shift _ _ _ _
    have hcoarse : D0 * T4 <= T0 * D4 + E :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hadd
    exact {
      coarse := by
        simpa only [w0, w4, D0, D4, T0, T4, E] using hcoarse
      fine := by
        simpa only [w1, w4, D1, D4, T1, T4] using T.fineReserve k hk
    }

#print axioms fixedCutoffDeficitDriftCross_eq_kernelSum
#print axioms fixedCutoffDriftKernel_eq_dim_mul_powerCross
#print axioms fixedCutoffDriftKernel_nonpos_of_diag_le_adj
#print axioms fixedCutoffDriftKernel_nonneg_of_adj_lt_diag
#print axioms fixedCutoffDeficitDriftCross_eq_core_add_boundary
#print axioms fixedCutoffDriftCore_twice_eq_pairSum
#print axioms BlockCompatibleP2DimensionlessDriftCrossTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaDriftCross
