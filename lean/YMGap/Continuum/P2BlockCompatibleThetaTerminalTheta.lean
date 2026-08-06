/-
Track 11.7-fusion / R3m -- Weyl-to-theta conversion of the terminal endpoint.

# Result

The endpoint inequality is converted exactly to a finite weighted-Gaussian
lower bound.  At every positive cutoff,

    w^3 * terminalOuterFactor(w,N) = integerThetaTerm(w,N+1),

while the existing theta representation gives

    w^2 * coordNormSq(w,N) = integerThetaSum(w,N).

Positive cancellation therefore replaces `L*outer <= (5/16)*D` by

    L * terminalThetaTerm <= (5/16) * w * integerThetaSum.

No Gaussian lower bound or all-scale inhabitant is asserted in this module.

# Constructivity

Exact finite powers, reflected commutative-semiring normalization, and
positive-factor cancellation.  No `Classical`, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.HarmonicThetaRepresentation
import YMGap.Continuum.P2BlockCompatibleThetaTerminalRadial

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalTheta

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaDriftCross
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.P2BlockCompatibleThetaTerminalChord
open YMGap.Continuum.P2BlockCompatibleThetaTerminalRadial
open YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem c4_charge_sq_local (s : Nat) :
    c4 s + 1 = (s + 1) * (s + 1) := by
  show s * (s + 2) + 1 = (s + 1) * (s + 1)
  have e1 : (s + 1) * (s + 1) = s * s + (2 * s + 1) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  have e2 : s * (s + 2) = s * s + 2 * s := by
    rw [Nat.mul_add]
    omega
  rw [e1, e2]
  omega

private def outerReorderL : RingNormaliser.PolyExpr :=
  let p := RingNormaliser.PolyExpr.var 0
  let d := RingNormaliser.PolyExpr.var 1
  let q := RingNormaliser.PolyExpr.var 2
  .mul p (.mul d q)

private def outerReorderR : RingNormaliser.PolyExpr :=
  let p := RingNormaliser.PolyExpr.var 0
  let d := RingNormaliser.PolyExpr.var 1
  let q := RingNormaliser.PolyExpr.var 2
  .mul d (.mul p q)

private theorem outerReorder_normal :
    RingNormaliser.normalize outerReorderL =
      RingNormaliser.normalize outerReorderR := by decide

private theorem outer_reorder (p d q : Q') :
    p * (d * q) ≈ d * (p * q) := by
  simpa [outerReorderL, outerReorderR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      outerReorderL outerReorderR outerReorder_normal
      (fun | 0 => p | 1 => d | _ => q))

/-- Exact Weyl-to-theta identity for the terminal outer factor. -/
theorem fixedCutoffTerminalOuterFactor_theta_eqv
    (w : Q') {N : Nat} (hN : 0 < N) :
    qpow w 3 * fixedCutoffTerminalOuterFactor w N ≈
      integerThetaTerm w (N + 1) := by
  let L2 := (N + 1) * (N + 1)
  let E := fixedCutoffDiagExponent N
  have hc4pos : 0 < c4 N := by
    unfold c4
    exact Nat.mul_pos hN (by omega)
  have hEpos : 0 < E := by
    unfold E fixedCutoffDiagExponent
    omega
  have hsq := c4_charge_sq_local N
  have hexp : 3 + (E - 1) = L2 + L2 := by
    unfold E L2 fixedCutoffDiagExponent
    omega
  have hleftPow : qpow w 3 * qpow w (E - 1) ≈
      qpow w (L2 + L2) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (HeatKernelRGStep.qpow_add w 3 (E - 1))) ?_
    rw [hexp]
    exact Q'.eqv_refl _
  have hrightPow : qpow (w * w) L2 ≈ qpow w (L2 + L2) := by
    refine Q'.eqv_trans _ _ _
      (FusionQuotientCollapse.qpow_mul_self w L2) ?_
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_add w L2 L2)
  unfold fixedCutoffTerminalOuterFactor integerThetaTerm
  change qpow w 3 * (Q'.ofNat L2 * qpow w (E - 1)) ≈
    Q'.ofNat L2 * qpow (w * w) L2
  refine Q'.eqv_trans _ _ _ (outer_reorder _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat L2) _ _ hleftPow) ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat L2) _ _
    (Q'.eqv_symm hrightPow)

private def normScaleL : RingNormaliser.PolyExpr :=
  let w := RingNormaliser.PolyExpr.var 0
  let q2 := RingNormaliser.PolyExpr.var 1
  let c := RingNormaliser.PolyExpr.var 2
  let D := RingNormaliser.PolyExpr.var 3
  .mul (.mul w q2) (.mul c D)

private def normScaleR : RingNormaliser.PolyExpr :=
  let w := RingNormaliser.PolyExpr.var 0
  let q2 := RingNormaliser.PolyExpr.var 1
  let c := RingNormaliser.PolyExpr.var 2
  let D := RingNormaliser.PolyExpr.var 3
  .mul c (.mul w (.mul q2 D))

private theorem normScale_normal :
    RingNormaliser.normalize normScaleL =
      RingNormaliser.normalize normScaleR := by decide

private theorem norm_scale_reorder (w q2 c D : Q') :
    (w * q2) * (c * D) ≈ c * (w * (q2 * D)) := by
  simpa [normScaleL, normScaleR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      normScaleL normScaleR normScale_normal
      (fun | 0 => w | 1 => q2 | 2 => c | _ => D))

private theorem qpow_three_eq_one_mul_two (w : Q') :
    qpow w 3 ≈ w * qpow w 2 := by
  have h := HeatKernelRGStep.qpow_add w 1 2
  have h1 : qpow w 1 ≈ w := by
    change (1 : Q') * w ≈ w
    exact Q'.one_mul_eqv w
  refine Q'.eqv_trans _ _ _ h ?_
  exact Q'.mul_eqv_congr_right _ _ _ h1

/-- A weighted finite-theta endpoint inequality implies the original endpoint
factor bound after cancellation of the positive factor `w^3`. -/
theorem fixedCutoffTerminalOuterFactor_le_of_theta
    {w c : Q'} (hw : (0 : Q') < w) {N : Nat} (hN : 0 < N)
    (hTheta :
      Q'.ofNat (N + 1) * integerThetaTerm w (N + 1) <=
        c * (w * integerThetaSum w N)) :
    Q'.ofNat (N + 1) * fixedCutoffTerminalOuterFactor w N <=
      c * coordNormSq w N := by
  let q3 := qpow w 3
  have hq3 : (0 : Q') < q3 :=
    BondMovingScaledNorm.qpow_pos hw 3
  have houter := fixedCutoffTerminalOuterFactor_theta_eqv w hN
  have hnorm := coordNormSq_theta_eqv w N
  have hleft : q3 *
        (Q'.ofNat (N + 1) * fixedCutoffTerminalOuterFactor w N) ≈
      Q'.ofNat (N + 1) * integerThetaTerm w (N + 1) := by
    refine Q'.eqv_trans _ _ _ (outer_reorder _ _ _) ?_
    exact Q'.mul_eqv_congr_left _ _ _ houter
  have hq3split := qpow_three_eq_one_mul_two w
  have hright : q3 * (c * coordNormSq w N) ≈
      c * (w * integerThetaSum w N) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hq3split) ?_
    refine Q'.eqv_trans _ _ _ (norm_scale_reorder _ _ _ _) ?_
    exact Q'.mul_eqv_congr_left c _ _
      (Q'.mul_eqv_congr_left w _ _ hnorm)
  have hscaled : q3 *
        (Q'.ofNat (N + 1) * fixedCutoffTerminalOuterFactor w N) <=
      q3 * (c * coordNormSq w N) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hTheta (Q'.ge_of_eqv hright))
  exact Q'.le_of_mul_le_mul_left hscaled hq3

/-- Honest terminal carrier after exact conversion of its endpoint field to a
weighted finite-theta inequality. -/
structure BlockCompatibleP2TerminalThetaFactorizedTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalTheta : forall k, 7 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    let N := blockNcut k
    blockLength k * integerThetaTerm w4 (N + 1) <=
      terminalOuterSplitCoeff * (w4 * integerThetaSum w4 N)
  terminalRadial : forall k, 7 <= k ->
    let w0 := blockWeight k
    fixedCutoffTerminalRadialDiagEnvelope w0 (blockNcut k) <=
      terminalRadialSplitCoeff *
        ((blockLength k * blockLength k) *
          coordNormSq w0 (blockNcut k))
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

def BlockCompatibleP2TerminalThetaFactorizedTailFromSeven.toFactorizedTail
    (T : BlockCompatibleP2TerminalThetaFactorizedTailFromSeven) :
    BlockCompatibleP2TerminalFactorizedTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalOuter := fun k hk => by
    let w4 := qpow (blockWeight (k + 1)) 4
    let N := blockNcut k
    have hw4 : (0 : Q') < w4 := by
      unfold w4
      exact BondMovingScaledNorm.qpow_pos (blockWeight_pos (k + 1)) 4
    have htheta : Q'.ofNat (N + 1) * integerThetaTerm w4 (N + 1) <=
        terminalOuterSplitCoeff * (w4 * integerThetaSum w4 N) := by
      simpa only [w4, N, blockLength] using T.terminalTheta k hk
    simpa only [w4, N, blockLength] using
      fixedCutoffTerminalOuterFactor_le_of_theta
        hw4 (blockNcut_pos k) htheta
  terminalRadial := T.terminalRadial
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalThetaFactorizedTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalThetaFactorizedTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toFactorizedTail.toCoefficientSandwich

#print axioms fixedCutoffTerminalOuterFactor_theta_eqv
#print axioms fixedCutoffTerminalOuterFactor_le_of_theta
#print axioms BlockCompatibleP2TerminalThetaFactorizedTailFromSeven.toFactorizedTail
#print axioms BlockCompatibleP2TerminalThetaFactorizedTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaTerminalTheta
