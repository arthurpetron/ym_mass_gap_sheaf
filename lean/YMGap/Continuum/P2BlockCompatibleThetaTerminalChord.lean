/-
Track 11.7-fusion / R3k -- exact terminal heat-chord reduction.

# Result

The unmatched terminal column from the common-cutoff theta covariance is
factored by the *actual* heat-weight increment.  For every `i < N`, the
Casimir exponent gap is positive, so the difference of powers is exactly

    (high - low) * mixedPowSum low high (gap - 1).

After summing, the complete terminal cross is

    (high - low) * terminalChordMass.

On the block-compatible physical schedule, the checked quadratic heat-drift
bound therefore reduces the terminal budget to the scale-free finite-sum
inequality

    terminalChordMass <= 2 * (16/75) * L * D_low * D_high.

The new tail structure is honest: no inhabitant of that inequality, the
trapezoid exchange, or the independent fine reserve is asserted.

# Constructivity

Primitive finite sums, exact `Q'` setoid algebra, the constructive mixed-power
factorization, and reflected polynomial normalization only.  No `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
import YMGap.Continuum.SemicircleAtanEndpointMonomialRiemann
import YMGap.Continuum.BondMovingScaledNorm

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalChord

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.P2BlockCompatibleHeatPower
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaDriftCross
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SemicircleAtanEndpointMonomialRiemann

local infix:50 " ≈ " => Q'.eqv

/-- Positive Casimir gap between a terminal diagonal mode and an adjacent
mode strictly below the terminal cutoff. -/
def fixedCutoffTerminalExponentGap (i N : Nat) : Nat :=
  fixedCutoffDiagExponent N - fixedCutoffAdjExponent i

private theorem c4_mono_local {a b : Nat} (hab : a <= b) : c4 a <= c4 b := by
  unfold c4
  exact Nat.mul_le_mul hab (Nat.add_le_add_right hab 2)

theorem fixedCutoffTerminalExponentGap_pos
    {i N : Nat} (hiN : i < N) :
    0 < fixedCutoffTerminalExponentGap i N := by
  have hstep : c4 i < c4 (i + 1) := by
    rw [BondMovingScaledNorm.c4_succ]
    omega
  have hnext : c4 (i + 1) <= c4 N :=
    c4_mono_local (show i + 1 <= N by omega)
  have hleft : c4 i < c4 N := Nat.lt_of_lt_of_le hstep hnext
  have hright : c4 (i + 1) <= c4 N := hnext
  have hexp : fixedCutoffAdjExponent i < fixedCutoffDiagExponent N := by
    unfold fixedCutoffAdjExponent fixedCutoffDiagExponent
    omega
  unfold fixedCutoffTerminalExponentGap
  omega

private def terminalPowerFactorL : RingNormaliser.PolyExpr :=
  let la := RingNormaliser.PolyExpr.var 0
  let ha := RingNormaliser.PolyExpr.var 1
  let lg := RingNormaliser.PolyExpr.var 2
  let hg := RingNormaliser.PolyExpr.var 3
  .add (.mul la (.mul ha hg)) (.neg (.mul ha (.mul la lg)))

private def terminalPowerFactorR : RingNormaliser.PolyExpr :=
  let la := RingNormaliser.PolyExpr.var 0
  let ha := RingNormaliser.PolyExpr.var 1
  let lg := RingNormaliser.PolyExpr.var 2
  let hg := RingNormaliser.PolyExpr.var 3
  .mul (.mul la ha) (.add hg (.neg lg))

private theorem terminalPowerFactor_normal :
    RingNormaliser.normalize terminalPowerFactorL =
      RingNormaliser.normalize terminalPowerFactorR := by decide

private theorem terminal_power_factor_algebra
    (la ha lg hg : Q') :
    la * (ha * hg) + -(ha * (la * lg)) ≈
      (la * ha) * (hg + -lg) := by
  simpa [terminalPowerFactorL, terminalPowerFactorR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      terminalPowerFactorL terminalPowerFactorR terminalPowerFactor_normal
      (fun | 0 => la | 1 => ha | 2 => lg | _ => hg))

private theorem common_chord_algebra (C d M : Q') :
    C * (d * M) ≈ d * (C * M) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv C d M)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ M (Q'.mul_comm_eqv C d)) ?_
  exact Q'.mul_assoc_eqv d C M

private theorem fixedCutoffPowerCross_terminal_factor
    (low high : Q') {i N : Nat} (hiN : i < N) :
    fixedCutoffPowerCross low high
        (fixedCutoffAdjExponent i) (fixedCutoffDiagExponent N) ≈
      (high + -low) *
        ((qpow low (fixedCutoffAdjExponent i) *
            qpow high (fixedCutoffAdjExponent i)) *
          mixedPowSum low high
            (fixedCutoffTerminalExponentGap i N - 1)) := by
  let a := fixedCutoffAdjExponent i
  let d := fixedCutoffDiagExponent N
  let g := fixedCutoffTerminalExponentGap i N
  let M := mixedPowSum low high (g - 1)
  have had : a <= d := fixedCutoffAdjExponent_le_diagExponent_of_lt hiN
  have hag : a + g = d := by
    unfold g fixedCutoffTerminalExponentGap
    exact Nat.add_sub_of_le had
  have hgpos : 0 < g := by
    simpa only [g] using fixedCutoffTerminalExponentGap_pos hiN
  have hpred : g - 1 + 1 = g := by omega
  have hlow : qpow low d ≈ qpow low a * qpow low g := by
    rw [← hag]
    exact HeatKernelRGStep.qpow_add low a g
  have hhigh : qpow high d ≈ qpow high a * qpow high g := by
    rw [← hag]
    exact HeatKernelRGStep.qpow_add high a g
  have hmix0 := mixedPowSum_factor low high (g - 1)
  have hmix : (high + -low) * M ≈
      qpow high g + -qpow low g := by
    dsimp only [M]
    rw [hpred] at hmix0
    exact hmix0
  unfold fixedCutoffPowerCross
  change qpow low a * qpow high d +
      -(qpow high a * qpow low d) ≈ _
  refine Q'.eqv_trans _
    (qpow low a * (qpow high a * qpow high g) +
      -(qpow high a * (qpow low a * qpow low g))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (qpow low a) _ _ hhigh)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (qpow high a) _ _ hlow))
  · refine Q'.eqv_trans _
      ((qpow low a * qpow high a) *
        (qpow high g + -qpow low g)) _
      (terminal_power_factor_algebra _ _ _ _) ?_
    refine Q'.eqv_trans _
      ((qpow low a * qpow high a) *
        ((high + -low) * M)) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hmix)) ?_
    exact common_chord_algebra _ _ _

/-- Nonnegative mixed-power carrier left after the actual heat increment is
factored out of one terminal covariance cell. -/
def fixedCutoffTerminalChordKernel
    (low high : Q') (i N : Nat) : Q' :=
  fixedCutoffKernelDim i N *
    ((qpow low (fixedCutoffAdjExponent i) *
        qpow high (fixedCutoffAdjExponent i)) *
      mixedPowSum low high (fixedCutoffTerminalExponentGap i N - 1))

theorem fixedCutoffDriftKernel_terminal_eq_increment_mul_chord
    (low high : Q') {i N : Nat} (hiN : i < N) :
    fixedCutoffDriftKernel low high i N ≈
      (high + -low) * fixedCutoffTerminalChordKernel low high i N := by
  refine Q'.eqv_trans _ _ _
    (fixedCutoffDriftKernel_eq_dim_mul_powerCross low high i N) ?_
  refine Q'.eqv_trans _
    (fixedCutoffKernelDim i N *
      ((high + -low) *
        ((qpow low (fixedCutoffAdjExponent i) *
            qpow high (fixedCutoffAdjExponent i)) *
          mixedPowSum low high
            (fixedCutoffTerminalExponentGap i N - 1)))) _
    (Q'.mul_eqv_congr_left _ _ _
      (fixedCutoffPowerCross_terminal_factor low high hiN)) ?_
  unfold fixedCutoffTerminalChordKernel
  exact common_chord_algebra _ _ _

theorem fixedCutoffTerminalChordKernel_nonneg
    {low high : Q'} (hlow : (0 : Q') <= low)
    (hhigh : (0 : Q') <= high) (i N : Nat) :
    (0 : Q') <= fixedCutoffTerminalChordKernel low high i N := by
  have hdim : (0 : Q') <= fixedCutoffKernelDim i N := by
    unfold fixedCutoffKernelDim
    exact HeatKernelRGStep.zero_le_ofNat _
  have hpows : (0 : Q') <=
      qpow low (fixedCutoffAdjExponent i) *
        qpow high (fixedCutoffAdjExponent i) :=
    Q'.mul_nonneg _ _
      (qpow_nonneg low hlow _) (qpow_nonneg high hhigh _)
  have hmixed : (0 : Q') <=
      mixedPowSum low high (fixedCutoffTerminalExponentGap i N - 1) :=
    mixedPowSum_nonnegative hlow hhigh _
  unfold fixedCutoffTerminalChordKernel
  exact Q'.mul_nonneg _ _ hdim (Q'.mul_nonneg _ _ hpows hmixed)

/-- Complete terminal mixed-power mass. -/
def fixedCutoffTerminalChordMass (low high : Q') (N : Nat) : Q' :=
  fsum (fun i => fixedCutoffTerminalChordKernel low high i N) N

theorem fixedCutoffTerminalChordMass_nonneg
    {low high : Q'} (hlow : (0 : Q') <= low)
    (hhigh : (0 : Q') <= high) (N : Nat) :
    (0 : Q') <= fixedCutoffTerminalChordMass low high N := by
  unfold fixedCutoffTerminalChordMass
  exact fsum_nonneg
    (fun i => fixedCutoffTerminalChordKernel_nonneg hlow hhigh i N) N

/-- Exact proof-about-computation terminal factorization: the growing column
shares one scalar heat increment and one nonnegative finite chord mass. -/
theorem fixedCutoffTerminalCross_eq_increment_mul_chordMass
    (low high : Q') (N : Nat) :
    fixedCutoffTerminalCross low high N ≈
      (high + -low) * fixedCutoffTerminalChordMass low high N := by
  have hboundary : fixedCutoffDriftBoundary low high N ≈
      (high + -low) * fixedCutoffTerminalChordMass low high N := by
    unfold fixedCutoffDriftBoundary fixedCutoffTerminalChordMass
    refine Q'.eqv_trans _
      (fsum (fun i =>
        (high + -low) * fixedCutoffTerminalChordKernel low high i N) N) _
      (CubeRatioBounds.fsum_eqv_congr_lt _ _ N
        (fun i hi =>
          fixedCutoffDriftKernel_terminal_eq_increment_mul_chord
            low high hi)) ?_
    exact Q'.eqv_symm
      (CubeRatioBounds.fsum_const_mul (high + -low)
        (fun i => fixedCutoffTerminalChordKernel low high i N) N)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (fixedCutoffDriftBoundary_eq_terminalCross low high N))
    hboundary

private def terminalBudgetScaleL : RingNormaliser.PolyExpr :=
  let C := RingNormaliser.PolyExpr.var 0
  let q := RingNormaliser.PolyExpr.var 1
  let L := RingNormaliser.PolyExpr.var 2
  let D := RingNormaliser.PolyExpr.var 3
  .mul q (.mul (.mul (.const 2) C) (.mul L D))

private def terminalBudgetScaleR : RingNormaliser.PolyExpr :=
  let C := RingNormaliser.PolyExpr.var 0
  let q := RingNormaliser.PolyExpr.var 1
  let L := RingNormaliser.PolyExpr.var 2
  let D := RingNormaliser.PolyExpr.var 3
  .mul (.const 2) (.mul (.mul C (.mul q L)) D)

private theorem terminalBudgetScale_normal :
    RingNormaliser.normalize terminalBudgetScaleL =
      RingNormaliser.normalize terminalBudgetScaleR := by decide

private theorem terminal_budget_scale_algebra (C q L D : Q') :
    q * ((Q'.ofNat 2 * C) * (L * D)) ≈
      Q'.ofNat 2 * ((C * (q * L)) * D) := by
  simpa [terminalBudgetScaleL, terminalBudgetScaleR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      terminalBudgetScaleL terminalBudgetScaleR terminalBudgetScale_normal
      (fun | 0 => C | 1 => q | 2 => L | _ => D))

/-- Honest all-tail frontier after removing the scale-dependent heat drift
from the terminal column. -/
structure BlockCompatibleP2TerminalChordTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalChordMass : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let D0 := coordNormSq w0 (blockNcut k)
    let D4 := coordNormSq w4 (blockNcut k)
    fixedCutoffTerminalChordMass w0 w4 (blockNcut k) <=
      (Q'.ofNat 2 * blockNormalizedSlopeCoeff) *
        (blockLength k * (D0 * D4))
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

/-- The quadratic schedule bound supplies the factored heat increment; the
scale-free chord-mass field then pays exactly twice the normalized budget. -/
def BlockCompatibleP2TerminalChordTailFromSeven.toTrapezoidExchangeTail
    (T : BlockCompatibleP2TerminalChordTailFromSeven) :
    BlockCompatibleP2TrapezoidExchangeTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalBudget := fun k hk => by
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let N := blockNcut k
    let D0 := coordNormSq w0 N
    let D4 := coordNormSq w4 N
    let M := fixedCutoffTerminalChordMass w0 w4 N
    let q := blockQuadraticDrift k
    let L := blockLength k
    have hfactor : fixedCutoffTerminalCross w0 w4 N ≈
        (w4 + -w0) * M := by
      simpa only [M] using
        fixedCutoffTerminalCross_eq_increment_mul_chordMass w0 w4 N
    have hM0 : (0 : Q') <= M := by
      apply fixedCutoffTerminalChordMass_nonneg
      · simpa only [w0] using blockWeight_nonneg k
      · simpa only [w4] using
          qpow_nonneg (blockWeight (k + 1))
            (blockWeight_nonneg (k + 1)) 4
    have hheatUpper : w4 <= w0 + q := by
      simpa only [w0, w4, q] using fineFourth_le_coarse_add_quadratic k
    have hheat : w4 + -w0 <= q := Q'.sub_le_of_le_add hheatUpper
    have hfirst : (w4 + -w0) * M <= q * M :=
      Q'.mul_le_mul_of_nonneg_right _ _ M hheat hM0
    have hq0 : (0 : Q') <= q := by
      unfold q blockQuadraticDrift
      exact Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _
          (blockMargin_nonneg k) (blockMargin_nonneg k))
    have hmass : M <=
        (Q'.ofNat 2 * blockNormalizedSlopeCoeff) *
          (L * (D0 * D4)) := by
      simpa only [w0, w4, N, D0, D4, M, L] using
        T.terminalChordMass k hk
    have hsecond : q * M <=
        q * ((Q'.ofNat 2 * blockNormalizedSlopeCoeff) *
          (L * (D0 * D4))) :=
      Q'.mul_le_mul_of_nonneg_left _ _ q hmass hq0
    have hbudget :
        q * ((Q'.ofNat 2 * blockNormalizedSlopeCoeff) *
            (L * (D0 * D4))) ≈
          Q'.ofNat 2 * blockDriftCrossBudget k := by
      refine Q'.eqv_trans _
        (Q'.ofNat 2 *
          ((blockNormalizedSlopeCoeff * (q * L)) * (D0 * D4))) _
        (terminal_budget_scale_algebra
          blockNormalizedSlopeCoeff q L (D0 * D4)) ?_
      unfold blockDriftCrossBudget
      dsimp only [q, L, D0, D4, w0, w4, N]
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.le_trans' _ _ _ hfirst
        (Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv hbudget)))
  fineReserve := T.fineReserve

/-- Direct landing in the division-free coefficient sandwich and the checked
physical `BlockingStep.Phi` consumer. -/
def BlockCompatibleP2TerminalChordTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalChordTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toTrapezoidExchangeTail.toCoefficientSandwich

/-! ## Right-rectangle removal of the mixed power cofactor -/

/-- Explicit right-rectangle majorant for one mixed terminal chord. -/
def fixedCutoffTerminalRightKernel
    (low high : Q') (i N : Nat) : Q' :=
  fixedCutoffKernelDim i N *
    ((qpow low (fixedCutoffAdjExponent i) *
        qpow high (fixedCutoffAdjExponent i)) *
      (Q'.ofNat (fixedCutoffTerminalExponentGap i N) *
        qpow high (fixedCutoffTerminalExponentGap i N - 1)))

theorem fixedCutoffTerminalChordKernel_le_right
    {low high : Q'} (hlow : (0 : Q') <= low) (hlh : low <= high)
    {i N : Nat} (hiN : i < N) :
    fixedCutoffTerminalChordKernel low high i N <=
      fixedCutoffTerminalRightKernel low high i N := by
  let g := fixedCutoffTerminalExponentGap i N
  let C := fixedCutoffKernelDim i N *
    (qpow low (fixedCutoffAdjExponent i) *
      qpow high (fixedCutoffAdjExponent i))
  have hgpos : 0 < g := by
    simpa only [g] using fixedCutoffTerminalExponentGap_pos hiN
  have hpred : g - 1 + 1 = g := by omega
  have hmixed := mixedPowSum_upper hlow hlh (g - 1)
  rw [hpred] at hmixed
  have hhigh : (0 : Q') <= high := Q'.le_trans' _ _ _ hlow hlh
  have hC0 : (0 : Q') <= C := by
    unfold C
    exact Q'.mul_nonneg _ _
      (by
        unfold fixedCutoffKernelDim
        exact HeatKernelRGStep.zero_le_ofNat _)
      (Q'.mul_nonneg _ _
        (qpow_nonneg low hlow _)
        (qpow_nonneg high hhigh _))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ C hmixed hC0
  unfold fixedCutoffTerminalChordKernel fixedCutoffTerminalRightKernel
  dsimp only [g, C] at hscaled
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_assoc_eqv
      (fixedCutoffKernelDim i N)
      (qpow low (fixedCutoffAdjExponent i) *
        qpow high (fixedCutoffAdjExponent i))
      (mixedPowSum low high (fixedCutoffTerminalExponentGap i N - 1))))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_assoc_eqv
        (fixedCutoffKernelDim i N)
        (qpow low (fixedCutoffAdjExponent i) *
          qpow high (fixedCutoffAdjExponent i))
        (Q'.ofNat (fixedCutoffTerminalExponentGap i N) *
          qpow high (fixedCutoffTerminalExponentGap i N - 1)))))

/-- Sum of the explicit terminal right-rectangle kernels. -/
def fixedCutoffTerminalRightMass (low high : Q') (N : Nat) : Q' :=
  fsum (fun i => fixedCutoffTerminalRightKernel low high i N) N

private theorem fsum_le_termwise_local (f g : Nat -> Q') : forall n,
    (forall i, i < n -> f i <= g i) -> fsum f n <= fsum g n
  | 0, _ => Q'.le_refl' 0
  | n + 1, h => by
      have hprev := fsum_le_termwise_local f g n
        (fun i hi => h i (by omega))
      exact Q'.add_le_add hprev (h n (by omega))

theorem fixedCutoffTerminalChordMass_le_rightMass
    {low high : Q'} (hlow : (0 : Q') <= low) (hlh : low <= high)
    (N : Nat) :
    fixedCutoffTerminalChordMass low high N <=
      fixedCutoffTerminalRightMass low high N := by
  unfold fixedCutoffTerminalChordMass fixedCutoffTerminalRightMass
  exact fsum_le_termwise_local _ _ N
    (fun i hi => fixedCutoffTerminalChordKernel_le_right hlow hlh hi)

/-- Still sharper honest tail: the terminal field contains only the explicit
right-rectangle Casimir-gap moment. -/
structure BlockCompatibleP2TerminalRectangleTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalRightMass : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let D0 := coordNormSq w0 (blockNcut k)
    let D4 := coordNormSq w4 (blockNcut k)
    fixedCutoffTerminalRightMass w0 w4 (blockNcut k) <=
      (Q'.ofNat 2 * blockNormalizedSlopeCoeff) *
        (blockLength k * (D0 * D4))
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

def BlockCompatibleP2TerminalRectangleTailFromSeven.toTerminalChordTail
    (T : BlockCompatibleP2TerminalRectangleTailFromSeven) :
    BlockCompatibleP2TerminalChordTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalChordMass := fun k hk => by
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let N := blockNcut k
    let D0 := coordNormSq w0 N
    let D4 := coordNormSq w4 N
    have hrect : fixedCutoffTerminalChordMass w0 w4 N <=
        fixedCutoffTerminalRightMass w0 w4 N := by
      apply fixedCutoffTerminalChordMass_le_rightMass
      · simpa only [w0] using blockWeight_nonneg k
      · simpa only [w0, w4] using blockWeight_le_fine_fourth k
    have hbudget : fixedCutoffTerminalRightMass w0 w4 N <=
        (Q'.ofNat 2 * blockNormalizedSlopeCoeff) *
          (blockLength k * (D0 * D4)) := by
      simpa only [w0, w4, N, D0, D4] using T.terminalRightMass k hk
    exact Q'.le_trans' _ _ _ hrect hbudget
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalRectangleTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalRectangleTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toTerminalChordTail.toCoefficientSandwich

/-! ## Separation into one endpoint factor and one low-weight moment -/

/-- Constant terminal endpoint factor in the right-rectangle mass. -/
def fixedCutoffTerminalOuterFactor (high : Q') (N : Nat) : Q' :=
  Q'.ofNat ((N + 1) * (N + 1)) *
    qpow high (fixedCutoffDiagExponent N - 1)

/-- Low-weight Casimir-gap moment term after the terminal endpoint factor is
removed. -/
def fixedCutoffTerminalLowMomentTerm (low : Q') (i N : Nat) : Q' :=
  Q'.ofNat ((i + 1) * (i + 2)) *
    (Q'.ofNat (fixedCutoffTerminalExponentGap i N) *
      qpow low (fixedCutoffAdjExponent i))

def fixedCutoffTerminalLowMoment (low : Q') (N : Nat) : Q' :=
  fsum (fun i => fixedCutoffTerminalLowMomentTerm low i N) N

private def terminalRightSeparateL : RingNormaliser.PolyExpr :=
  let idim := RingNormaliser.PolyExpr.var 0
  let odim := RingNormaliser.PolyExpr.var 1
  let lowA := RingNormaliser.PolyExpr.var 2
  let highA := RingNormaliser.PolyExpr.var 3
  let gap := RingNormaliser.PolyExpr.var 4
  let highG := RingNormaliser.PolyExpr.var 5
  .mul (.mul idim odim)
    (.mul (.mul lowA highA) (.mul gap highG))

private def terminalRightSeparateR : RingNormaliser.PolyExpr :=
  let idim := RingNormaliser.PolyExpr.var 0
  let odim := RingNormaliser.PolyExpr.var 1
  let lowA := RingNormaliser.PolyExpr.var 2
  let highA := RingNormaliser.PolyExpr.var 3
  let gap := RingNormaliser.PolyExpr.var 4
  let highG := RingNormaliser.PolyExpr.var 5
  .mul (.mul odim (.mul highA highG))
    (.mul idim (.mul gap lowA))

private theorem terminalRightSeparate_normal :
    RingNormaliser.normalize terminalRightSeparateL =
      RingNormaliser.normalize terminalRightSeparateR := by decide

private theorem terminal_right_separate_algebra
    (idim odim lowA highA gap highG : Q') :
    (idim * odim) * ((lowA * highA) * (gap * highG)) ≈
      (odim * (highA * highG)) * (idim * (gap * lowA)) := by
  simpa [terminalRightSeparateL, terminalRightSeparateR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      terminalRightSeparateL terminalRightSeparateR
      terminalRightSeparate_normal
      (fun | 0 => idim | 1 => odim | 2 => lowA | 3 => highA |
        4 => gap | _ => highG))

theorem fixedCutoffTerminalRightKernel_eq_outer_mul_lowMomentTerm
    (low high : Q') {i N : Nat} (hiN : i < N) :
    fixedCutoffTerminalRightKernel low high i N ≈
      fixedCutoffTerminalOuterFactor high N *
        fixedCutoffTerminalLowMomentTerm low i N := by
  let a := fixedCutoffAdjExponent i
  let d := fixedCutoffDiagExponent N
  let g := fixedCutoffTerminalExponentGap i N
  let idim := Q'.ofNat ((i + 1) * (i + 2))
  let odim := Q'.ofNat ((N + 1) * (N + 1))
  have had : a <= d := fixedCutoffAdjExponent_le_diagExponent_of_lt hiN
  have hag : a + g = d := by
    unfold g fixedCutoffTerminalExponentGap
    exact Nat.add_sub_of_le had
  have hgpos : 0 < g := by
    simpa only [g] using fixedCutoffTerminalExponentGap_pos hiN
  have hexp : a + (g - 1) = d - 1 := by omega
  have hpow : qpow high (d - 1) ≈
      qpow high a * qpow high (g - 1) := by
    rw [← hexp]
    exact HeatKernelRGStep.qpow_add high a (g - 1)
  have hdim : fixedCutoffKernelDim i N ≈ idim * odim := by
    unfold fixedCutoffKernelDim idim odim
    exact HeatKernelRGStep.ofNat_mul_eqv _ _
  unfold fixedCutoffTerminalRightKernel
  change fixedCutoffKernelDim i N *
      ((qpow low a * qpow high a) *
        (Q'.ofNat g * qpow high (g - 1))) ≈ _
  refine Q'.eqv_trans _
    ((idim * odim) *
      ((qpow low a * qpow high a) *
        (Q'.ofNat g * qpow high (g - 1)))) _
    (Q'.mul_eqv_congr_right _ _ _ hdim) ?_
  refine Q'.eqv_trans _
    ((odim * (qpow high a * qpow high (g - 1))) *
      (idim * (Q'.ofNat g * qpow low a))) _
    (terminal_right_separate_algebra _ _ _ _ _ _) ?_
  unfold fixedCutoffTerminalOuterFactor fixedCutoffTerminalLowMomentTerm
  dsimp only [a, d, g, idim, odim]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_left odim _ _ (Q'.eqv_symm hpow))

/-- The right-rectangle terminal mass is exactly one endpoint factor times a
single low-weight Casimir-gap moment. -/
theorem fixedCutoffTerminalRightMass_eq_outer_mul_lowMoment
    (low high : Q') (N : Nat) :
    fixedCutoffTerminalRightMass low high N ≈
      fixedCutoffTerminalOuterFactor high N *
        fixedCutoffTerminalLowMoment low N := by
  unfold fixedCutoffTerminalRightMass fixedCutoffTerminalLowMoment
  refine Q'.eqv_trans _
    (fsum (fun i => fixedCutoffTerminalOuterFactor high N *
      fixedCutoffTerminalLowMomentTerm low i N) N) _
    (CubeRatioBounds.fsum_eqv_congr_lt _ _ N
      (fun i hi =>
        fixedCutoffTerminalRightKernel_eq_outer_mul_lowMomentTerm
          low high hi)) ?_
  exact Q'.eqv_symm
    (CubeRatioBounds.fsum_const_mul
      (fixedCutoffTerminalOuterFactor high N)
      (fun i => fixedCutoffTerminalLowMomentTerm low i N) N)

/-- Fully separated honest terminal frontier.  The only terminal analytic
field is now a product of one endpoint monomial and one low-weight moment. -/
structure BlockCompatibleP2TerminalSeparatedTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalSeparated : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let D0 := coordNormSq w0 (blockNcut k)
    let D4 := coordNormSq w4 (blockNcut k)
    fixedCutoffTerminalOuterFactor w4 (blockNcut k) *
        fixedCutoffTerminalLowMoment w0 (blockNcut k) <=
      (Q'.ofNat 2 * blockNormalizedSlopeCoeff) *
        (blockLength k * (D0 * D4))
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

def BlockCompatibleP2TerminalSeparatedTailFromSeven.toTerminalRectangleTail
    (T : BlockCompatibleP2TerminalSeparatedTailFromSeven) :
    BlockCompatibleP2TerminalRectangleTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalRightMass := fun k hk => by
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let N := blockNcut k
    let D0 := coordNormSq w0 N
    let D4 := coordNormSq w4 N
    have heq : fixedCutoffTerminalRightMass w0 w4 N ≈
        fixedCutoffTerminalOuterFactor w4 N *
          fixedCutoffTerminalLowMoment w0 N :=
      fixedCutoffTerminalRightMass_eq_outer_mul_lowMoment w0 w4 N
    have hbound : fixedCutoffTerminalOuterFactor w4 N *
          fixedCutoffTerminalLowMoment w0 N <=
        (Q'.ofNat 2 * blockNormalizedSlopeCoeff) *
          (blockLength k * (D0 * D4)) := by
      simpa only [w0, w4, N, D0, D4] using T.terminalSeparated k hk
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hbound
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalSeparatedTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalSeparatedTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toTerminalRectangleTail.toCoefficientSandwich

#print axioms fixedCutoffTerminalExponentGap_pos
#print axioms fixedCutoffDriftKernel_terminal_eq_increment_mul_chord
#print axioms fixedCutoffTerminalChordMass_nonneg
#print axioms fixedCutoffTerminalCross_eq_increment_mul_chordMass
#print axioms fixedCutoffTerminalChordKernel_le_right
#print axioms fixedCutoffTerminalChordMass_le_rightMass
#print axioms fixedCutoffTerminalRightKernel_eq_outer_mul_lowMomentTerm
#print axioms fixedCutoffTerminalRightMass_eq_outer_mul_lowMoment
#print axioms BlockCompatibleP2TerminalChordTailFromSeven.toTrapezoidExchangeTail
#print axioms BlockCompatibleP2TerminalChordTailFromSeven.toCoefficientSandwich
#print axioms BlockCompatibleP2TerminalRectangleTailFromSeven.toTerminalChordTail
#print axioms BlockCompatibleP2TerminalRectangleTailFromSeven.toCoefficientSandwich
#print axioms BlockCompatibleP2TerminalSeparatedTailFromSeven.toTerminalRectangleTail
#print axioms BlockCompatibleP2TerminalSeparatedTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaTerminalChord
