/-
Track 11.7-fusion / R3k -- diagonal moment reduction for the terminal chord.

# Result

The separated low-weight Casimir-gap moment is an adjacent-product sum.  The
constructive inequality `2*x*y <= x^2+y^2`, applied before summation and with
the exact exponent gap retained, proves

    2 * terminalLowMoment <= terminalDiagGapEnvelope.

A positive-factor compiler therefore replaces the terminal endpoint--moment
field by a purely diagonal weighted-moment inequality.  No inhabitant of that
inequality, the trapezoid exchange, or the fine reserve is asserted.

# Constructivity

Primitive finite sums, exact `Q'` setoid algebra, AM--GM as a square, and
reflected polynomial normalization only.  No `Classical`, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaTerminalChord

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalMoment

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaDriftCross
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.P2BlockCompatibleThetaTerminalChord
open YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

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

private theorem rotate_three_factors (A B C : Q') :
    A * (B * C) ≈ B * (A * C) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv A B C)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ C (Q'.mul_comm_eqv A B)) ?_
  exact Q'.mul_assoc_eqv B A C

theorem fixedCutoffTerminalLowMomentTerm_eq_gap_mul_adj
    (low : Q') (i N : Nat) :
    fixedCutoffTerminalLowMomentTerm low i N ≈
      Q'.ofNat (fixedCutoffTerminalExponentGap i N) *
        fixedCutoffAdjTerm low i := by
  let G := Q'.ofNat (fixedCutoffTerminalExponentGap i N)
  have hadj : fixedCutoffAdjTerm low i ≈
      Q'.ofNat ((i + 1) * (i + 2)) *
        qpow low (fixedCutoffAdjExponent i) := by
    unfold fixedCutoffAdjTerm fixedCutoffAdjExponent
    simpa only [Nat.add_assoc] using
      coeffW_product_monomial_local low i (i + 1)
  unfold fixedCutoffTerminalLowMomentTerm
  refine Q'.eqv_trans _
    (G * (Q'.ofNat ((i + 1) * (i + 2)) *
      qpow low (fixedCutoffAdjExponent i))) _
    (rotate_three_factors _ _ _) ?_
  exact Q'.mul_eqv_congr_left G _ _ (Q'.eqv_symm hadj)

/-- Purely diagonal weighted envelope produced by AM--GM. -/
def fixedCutoffTerminalDiagGapEnvelope (low : Q') (N : Nat) : Q' :=
  fsum (fun i =>
    Q'.ofNat (fixedCutoffTerminalExponentGap i N) *
      (fixedCutoffDiagTerm low i + fixedCutoffDiagTerm low (i + 1))) N

private theorem lowMomentTerm_twice_le_diagGapTerm
    (low : Q') (i N : Nat) :
    fixedCutoffTerminalLowMomentTerm low i N +
        fixedCutoffTerminalLowMomentTerm low i N <=
      Q'.ofNat (fixedCutoffTerminalExponentGap i N) *
        (fixedCutoffDiagTerm low i + fixedCutoffDiagTerm low (i + 1)) := by
  let G := Q'.ofNat (fixedCutoffTerminalExponentGap i N)
  let x := coeffW low i
  let y := coeffW low (i + 1)
  have hterm := fixedCutoffTerminalLowMomentTerm_eq_gap_mul_adj low i N
  have hleft : fixedCutoffTerminalLowMomentTerm low i N +
        fixedCutoffTerminalLowMomentTerm low i N ≈
      G * (x * y + x * y) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hterm hterm) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv G (x * y) (x * y))
  have hG0 : (0 : Q') <= G := by
    unfold G
    exact HeatKernelRGStep.zero_le_ofNat _
  have hamgm := CRealAlg.amgm_two x y
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ G hamgm hG0
  dsimp only [G, x, y] at hleft hscaled
  unfold fixedCutoffDiagTerm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hscaled

private theorem fsum_le_termwise_local (f g : Nat -> Q') : forall n,
    (forall i, i < n -> f i <= g i) -> fsum f n <= fsum g n
  | 0, _ => Q'.le_refl' 0
  | n + 1, h => by
      have hprev := fsum_le_termwise_local f g n
        (fun i hi => h i (by omega))
      exact Q'.add_le_add hprev (h n (by omega))

/-- Twice the adjacent Casimir-gap moment is paid by a purely diagonal
weighted moment. -/
theorem fixedCutoffTerminalLowMoment_twice_le_diagGapEnvelope
    (low : Q') (N : Nat) :
    fixedCutoffTerminalLowMoment low N +
        fixedCutoffTerminalLowMoment low N <=
      fixedCutoffTerminalDiagGapEnvelope low N := by
  let t := fun i => fixedCutoffTerminalLowMomentTerm low i N
  let e := fun i =>
    Q'.ofNat (fixedCutoffTerminalExponentGap i N) *
      (fixedCutoffDiagTerm low i + fixedCutoffDiagTerm low (i + 1))
  have hsum : fsum (fun i => t i + t i) N <= fsum e N :=
    fsum_le_termwise_local _ _ N
      (fun i _ => lowMomentTerm_twice_le_diagGapTerm low i N)
  have hsplit : fsum (fun i => t i + t i) N ≈
      fixedCutoffTerminalLowMoment low N +
        fixedCutoffTerminalLowMoment low N := by
    unfold fixedCutoffTerminalLowMoment t
    exact CubeRatioBounds.fsum_add _ _ N
  unfold fixedCutoffTerminalDiagGapEnvelope
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsplit) hsum

private def twiceBudgetL : RingNormaliser.PolyExpr :=
  let C := RingNormaliser.PolyExpr.var 0
  let L := RingNormaliser.PolyExpr.var 1
  let D := RingNormaliser.PolyExpr.var 2
  .mul (.mul (.const 4) C) (.mul L D)

private def twiceBudgetR : RingNormaliser.PolyExpr :=
  let C := RingNormaliser.PolyExpr.var 0
  let L := RingNormaliser.PolyExpr.var 1
  let D := RingNormaliser.PolyExpr.var 2
  let B := .mul (.mul (.const 2) C) (.mul L D)
  .add B B

private theorem twiceBudget_normal :
    RingNormaliser.normalize twiceBudgetL =
      RingNormaliser.normalize twiceBudgetR := by decide

private theorem four_budget_eq_two_copies (C L D : Q') :
    (Q'.ofNat 4 * C) * (L * D) ≈
      ((Q'.ofNat 2 * C) * (L * D)) +
        ((Q'.ofNat 2 * C) * (L * D)) := by
  simpa [twiceBudgetL, twiceBudgetR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      twiceBudgetL twiceBudgetR twiceBudget_normal
      (fun | 0 => C | 1 => L | _ => D))

/-- Honest diagonal-moment terminal frontier. -/
structure BlockCompatibleP2TerminalDiagEnvelopeTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalDiagEnvelope : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let D0 := coordNormSq w0 (blockNcut k)
    let D4 := coordNormSq w4 (blockNcut k)
    fixedCutoffTerminalOuterFactor w4 (blockNcut k) *
        fixedCutoffTerminalDiagGapEnvelope w0 (blockNcut k) <=
      (Q'.ofNat 4 * blockNormalizedSlopeCoeff) *
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

def BlockCompatibleP2TerminalDiagEnvelopeTailFromSeven.toTerminalSeparatedTail
    (T : BlockCompatibleP2TerminalDiagEnvelopeTailFromSeven) :
    BlockCompatibleP2TerminalSeparatedTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalSeparated := fun k hk => by
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let N := blockNcut k
    let O := fixedCutoffTerminalOuterFactor w4 N
    let M := fixedCutoffTerminalLowMoment w0 N
    let E := fixedCutoffTerminalDiagGapEnvelope w0 N
    let L := blockLength k
    let D0 := coordNormSq w0 N
    let D4 := coordNormSq w4 N
    let B := (Q'.ofNat 2 * blockNormalizedSlopeCoeff) *
      (L * (D0 * D4))
    have hM : M + M <= E := by
      simpa only [M, E] using
        fixedCutoffTerminalLowMoment_twice_le_diagGapEnvelope w0 N
    have hO0 : (0 : Q') <= O := by
      unfold O fixedCutoffTerminalOuterFactor
      exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
        (qpow_nonneg w4
          (qpow_nonneg (blockWeight (k + 1))
            (blockWeight_nonneg (k + 1)) 4) _)
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ O hM hO0
    have hdiag : O * E <=
        (Q'.ofNat 4 * blockNormalizedSlopeCoeff) *
          (L * (D0 * D4)) := by
      simpa only [w0, w4, N, O, E, L, D0, D4] using
        T.terminalDiagEnvelope k hk
    have hleft : (O * M) + (O * M) ≈ O * (M + M) :=
      Q'.eqv_symm (Q'.mul_add_eqv O M M)
    have hright :
        (Q'.ofNat 4 * blockNormalizedSlopeCoeff) *
            (L * (D0 * D4)) ≈ B + B := by
      simpa only [B] using
        four_budget_eq_two_copies blockNormalizedSlopeCoeff L (D0 * D4)
    have hdouble : (O * M) + (O * M) <= B + B :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _ hscaled
          (Q'.le_trans' _ _ _ hdiag (Q'.le_of_eqv hright)))
    have htwo : Q'.ofNat 2 * (O * M) <= Q'.ofNat 2 * B :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv (O * M)))
        (Q'.le_trans' _ _ _ hdouble
          (Q'.ge_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv B)))
    exact Q'.le_of_mul_le_mul_left htwo (by decide)
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalDiagEnvelopeTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalDiagEnvelopeTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toTerminalSeparatedTail.toCoefficientSandwich

#print axioms fixedCutoffTerminalLowMomentTerm_eq_gap_mul_adj
#print axioms fixedCutoffTerminalLowMoment_twice_le_diagGapEnvelope
#print axioms BlockCompatibleP2TerminalDiagEnvelopeTailFromSeven.toTerminalSeparatedTail
#print axioms BlockCompatibleP2TerminalDiagEnvelopeTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaTerminalMoment
