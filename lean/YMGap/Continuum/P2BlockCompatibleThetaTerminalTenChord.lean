/-
Track 11.7-fusion / R3n -- ten-block weighted Gaussian chord compiler.

# Result

A generic structural recursion flattens `B` adjacent blocks of length `H` and
applies the convex chord of `n^2` on each block.  Specializing to the physical
cutoff length `L_k=10*2^(k-1)` for `k>=1` yields a ten-block geometric
minorant of the exact integer-theta sum.  Hence the terminal endpoint field is
reduced to one fixed-ten-block inequality rather than a growing raw theta sum.

No inhabitant of that final geometric inequality is asserted here.

# Constructivity

Primitive finite-sum recursion, the proved Nat chord inequality, power
antitonicity on `[0,1]`, and exact schedule arithmetic.  No `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.JacobiModularCReal
import YMGap.Continuum.P2BlockCompatibleThetaTerminalTheta

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalTenChord

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.P2BlockCompatibleThetaTerminalChord
open YMGap.Continuum.P2BlockCompatibleThetaTerminalRadial
open YMGap.Continuum.P2BlockCompatibleThetaTerminalTheta
open YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Weighted Gaussian summand at charge `n`. -/
def weightedThetaQTerm (q : Q') (n : Nat) : Q' :=
  Q'.ofNat (n * n) * qpow q (n * n)

/-- Chord exponent for the `(b+1)`-st cell inside block `b`. -/
def weightedChordExponent (H b r : Nat) : Nat :=
  (b * H) * (b * H) +
    (((b + 1) * H) + b * H) * (r + 1)

def weightedChordBlock (q : Q') (H b : Nat) : Q' :=
  fsum (fun r =>
    Q'.ofNat ((b * H + r + 1) * (b * H + r + 1)) *
      qpow q (weightedChordExponent H b r)) H

def weightedChordBlocks (q : Q') (H B : Nat) : Q' :=
  fsum (fun b => weightedChordBlock q H b) B

/-- Flatten `B` consecutive length-`H` blocks without enumerating `B*H`. -/
private theorem fsum_blocks_eq (f : Nat -> Q') (H : Nat) : forall B,
    fsum f (B * H) ≈
      fsum (fun b => fsum (fun r => f (b * H + r)) H) B
  | 0 => by
      simp only [Nat.zero_mul, fsum_zero]
      exact Q'.eqv_refl 0
  | B + 1 => by
      have ih := fsum_blocks_eq f H B
      rw [Nat.succ_mul]
      change fsum f (B * H + H) ≈
        fsum (fun b => fsum (fun r => f (b * H + r)) H) B +
          fsum (fun r => f (B * H + r)) H
      refine Q'.eqv_trans _ _ _
        (FusionCoreStepRoundH.fsum_split_at f (B * H) H) ?_
      exact Q'.add_eqv_congr' ih (Q'.eqv_refl _)

private theorem chord_exponent_le_square
    {H b r : Nat} (hr : r < H) :
    (b * H + r + 1) * (b * H + r + 1) <=
      weightedChordExponent H b r := by
  let lo := b * H
  let hi := (b + 1) * H
  let n := b * H + r + 1
  have hlo : lo <= n := by
    dsimp only [lo, n]
    omega
  have hhi : n <= hi := by
    dsimp only [n, hi]
    rw [Nat.add_mul]
    omega
  have hch := JacobiModularCReal.chord_nat hlo hhi
  have hsub : n - lo = r + 1 := by
    dsimp only [n, lo]
    omega
  rw [hsub] at hch
  simpa only [lo, hi, n, weightedChordExponent] using hch

private theorem weightedChordBlock_le_actual
    {q : Q'} (hq0 : (0 : Q') <= q) (hq1 : q <= (1 : Q'))
    (H b : Nat) :
    weightedChordBlock q H b <=
      fsum (fun r => weightedThetaQTerm q (b * H + r + 1)) H := by
  unfold weightedChordBlock
  apply CubeRatioBounds.fsum_mono_lt
  intro r hr
  have hp := HeatKernelRGStep.qpow_antitone hq0 hq1
    ((b * H + r + 1) * (b * H + r + 1))
    (weightedChordExponent H b r)
    (chord_exponent_le_square (H := H) (b := b) hr)
  exact Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat ((b * H + r + 1) * (b * H + r + 1))) hp
    (HeatKernelRGStep.zero_le_ofNat _)

/-- The `B`-block chord sum is a lower bound for the first `B*H` weighted
Gaussian charges. -/
theorem weightedChordBlocks_le_prefix
    {q : Q'} (hq0 : (0 : Q') <= q) (hq1 : q <= (1 : Q'))
    (H B : Nat) :
    weightedChordBlocks q H B <=
      fsum (fun j => weightedThetaQTerm q (j + 1)) (B * H) := by
  have hblocks : weightedChordBlocks q H B <=
      fsum (fun b =>
        fsum (fun r => weightedThetaQTerm q (b * H + r + 1)) H) B := by
    unfold weightedChordBlocks
    apply CubeRatioBounds.fsum_mono_lt
    intro b _
    exact weightedChordBlock_le_actual hq0 hq1 H b
  have hflat := fsum_blocks_eq
    (fun j => weightedThetaQTerm q (j + 1)) H B
  exact Q'.le_trans' _ _ _ hblocks (Q'.ge_of_eqv hflat)

/-- Chord minorant in the existing `integerThetaSum` coordinates. -/
theorem weightedChordBlocks_le_integerThetaSum
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {H B : Nat} (hBH : 0 < B * H) :
    weightedChordBlocks (w * w) H B <=
      integerThetaSum w (B * H - 1) := by
  have hq0 : (0 : Q') <= w * w := Q'.mul_nonneg _ _ hw0 hw0
  have hq1 : w * w <= (1 : Q') := by
    have hm := Q'.mul_le_mul_of_nonneg hw1 hw1 (by decide) hw0
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have hp := weightedChordBlocks_le_prefix hq0 hq1 H B
  have hlen : B * H - 1 + 1 = B * H := Nat.sub_add_cancel hBH
  unfold integerThetaSum
  rw [← MovingCutoff.fsum_eq_finSum, hlen]
  simpa only [weightedThetaQTerm, integerThetaTerm] using hp

/-- Physical tenth-length, with the harmless `k=0` value separated. -/
def blockTenth : Nat -> Nat
  | 0 => 1
  | k + 1 => 2 ^ k

theorem blockCutoffLength_closed (k : Nat) :
    blockNcut k + 1 = 5 * 2 ^ k :=
  blockNcut_closed k

theorem blockCutoffLength_eq_ten_tenths
    {k : Nat} (hk : 1 <= k) :
    blockNcut k + 1 = 10 * blockTenth k := by
  cases k with
  | zero => omega
  | succ k =>
      change blockNcut (k + 1) + 1 = 10 * 2 ^ k
      have h := blockCutoffLength_closed (k + 1)
      rw [Nat.pow_succ] at h
      omega

/-- Honest endpoint carrier after replacement of the full theta sum by a
fixed ten-block geometric chord minorant. -/
structure BlockCompatibleP2TerminalTenChordTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalTenChord : forall k, 7 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    let H := blockTenth k
    blockLength k * integerThetaTerm w4 (blockNcut k + 1) <=
      terminalOuterSplitCoeff *
        (w4 * weightedChordBlocks (w4 * w4) H 10)
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

def BlockCompatibleP2TerminalTenChordTailFromSeven.toThetaFactorizedTail
    (T : BlockCompatibleP2TerminalTenChordTailFromSeven) :
    BlockCompatibleP2TerminalThetaFactorizedTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalTheta := fun k hk => by
    let w4 := qpow (blockWeight (k + 1)) 4
    let H := blockTenth k
    let N := blockNcut k
    have hw40 : (0 : Q') <= w4 := by
      unfold w4
      exact qpow_nonneg (blockWeight (k + 1))
        (blockWeight_nonneg (k + 1)) 4
    have hw41 : w4 <= (1 : Q') := by
      unfold w4
      exact HeatKernelGap.qpow_le_one
        (blockWeight_nonneg (k + 1)) (blockWeight_le_one (k + 1)) 4
    have hlen : N + 1 = 10 * H := by
      simpa only [N, H] using
        blockCutoffLength_eq_ten_tenths (show 1 <= k by omega)
    have hH : 0 < H := by
      have hten : 0 < 10 * H := by
        rw [← hlen]
        omega
      omega
    have hminor : weightedChordBlocks (w4 * w4) H 10 <=
        integerThetaSum w4 N := by
      have h := weightedChordBlocks_le_integerThetaSum hw40 hw41
        (H := H) (B := 10) (show 0 < 10 * H by omega)
      have hN : 10 * H - 1 = N := by omega
      rw [hN] at h
      exact h
    have hscale0 : (0 : Q') <= terminalOuterSplitCoeff * w4 :=
      Q'.mul_nonneg _ _ (by unfold terminalOuterSplitCoeff; decide) hw40
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      (terminalOuterSplitCoeff * w4) hminor hscale0
    have hchord : blockLength k * integerThetaTerm w4 (N + 1) <=
        terminalOuterSplitCoeff *
          (w4 * weightedChordBlocks (w4 * w4) H 10) := by
      simpa only [w4, H, N] using T.terminalTenChord k hk
    have hright : terminalOuterSplitCoeff *
          (w4 * weightedChordBlocks (w4 * w4) H 10) ≈
        (terminalOuterSplitCoeff * w4) *
          weightedChordBlocks (w4 * w4) H 10 :=
      Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    have htarget : (terminalOuterSplitCoeff * w4) *
          integerThetaSum w4 N ≈
        terminalOuterSplitCoeff * (w4 * integerThetaSum w4 N) :=
      Q'.mul_assoc_eqv _ _ _
    exact Q'.le_trans' _ _ _ hchord
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright)
        (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv htarget)))
  terminalRadial := T.terminalRadial
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalTenChordTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalTenChordTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toThetaFactorizedTail.toCoefficientSandwich

#print axioms weightedChordBlocks_le_prefix
#print axioms weightedChordBlocks_le_integerThetaSum
#print axioms blockCutoffLength_eq_ten_tenths
#print axioms BlockCompatibleP2TerminalTenChordTailFromSeven.toThetaFactorizedTail
#print axioms BlockCompatibleP2TerminalTenChordTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaTerminalTenChord
