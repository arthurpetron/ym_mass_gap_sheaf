/-
Downstream budget consumer for the signed harmonic chord envelope.

The old chord consumer required every terminal carrier gap to be
nonnegative, a premise refuted at larger scales.  The signed crossing theorem
constructs the correct split.  This file shows that a quantitative chord
budget at that split is exactly sufficient for the existing `24/25` reserve
and hence for the weighted trapezoid inequality.
-/

import YMGap.Continuum.HarmonicSignedChordAbsorption

namespace YMGap.Continuum.HarmonicSignedChordBudgetBridge

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicSignedChordAbsorption
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

private theorem fsum_nonneg_lt (f : Nat → Q') : ∀ n,
    (∀ i, i < n → (0 : Q') ≤ f i) → (0 : Q') ≤ fsum f n
  | 0, _ => Q'.le_refl' 0
  | n + 1, hf => by
      simp only [fsum_succ]
      exact Q'.zero_le_add _ _
        (fsum_nonneg_lt f n (fun i hi => hf i (by omega)))
        (hf n (by omega))

/-- At an admissible crossing, every retained signed-chord cell is
nonnegative.  Cells before the crossing are definitionally zero. -/
theorem signedChordSum_nonneg_of_crossing (k L s : Nat)
    (hsL : s ≤ L)
    (hboundary : (0 : Q') ≤ trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k s)) :
    (0 : Q') ≤ signedChordSum k L s := by
  unfold signedChordSum
  apply fsum_nonneg_lt
  intro p hpL
  unfold signedChordCell
  by_cases hsp : s ≤ p
  · rw [if_pos hsp]
    have hgap := terminal_carrier_gap_nonneg_from_split
      k L s hsL hboundary hsp (by omega)
    have hG : (0 : Q') ≤ driftSqFactor k p := by
      unfold driftSqFactor
      exact Q'.mul_nonneg _ _
        (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
        (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
    have hu : (0 : Q') ≤ unit (driftDen k) (driftDen_pos k) :=
      unit_nonneg _ _
    have hn : (0 : Q') ≤ Q'.ofNat ((4 * p + 5) + 1) :=
      ExpNeg.ofNat_nonneg' _
    have hpow : (0 : Q') ≤ qpow (driftRatio k) (4 * p + 5) :=
      qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _
    have hbr : (0 : Q') ≤ (1 : Q') +
        qpow (driftRatio k) (4 * p + 5) :=
      Q'.zero_le_add _ _ (by decide) hpow
    unfold compensatedChordCell
    exact Q'.mul_nonneg _ _ hgap
      (Q'.mul_nonneg _ _ hG
        (Q'.mul_nonneg _ _ hu (Q'.mul_nonneg _ _ hn hbr)))
  · rw [if_neg hsp]
    exact Q'.le_refl' 0

theorem trapezoidTerminalCorrection_nonneg (k : Nat) :
    (0 : Q') ≤ trapezoidTerminalCorrection k := by
  have hA : (0 : Q') ≤ oldAdj k (Ncut k - 1) := by
    unfold oldAdj
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) _)
      (coeffW_nonneg (harmW_nonneg k) _)
  have hG : (0 : Q') ≤ driftSqFactor k (Ncut k) := by
    unfold driftSqFactor
    exact Q'.mul_nonneg _ _
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
  unfold trapezoidTerminalCorrection
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (harmonicD_pos k)) hA) hG

/-- A quantitative signed-chord estimate at every admissible first crossing
implies the `24/25` compensated reserve.  The crossing itself is found by
exact rational comparison, so no choice principle or global carrier-sign
premise is needed. -/
theorem compensated_reserve_twentyFourTwentyFive_of_signed_crossing_budget
    (k : Nat)
    (hbudget : ∀ s, s ≤ Ncut k - 1 →
      (∀ p, p < s →
        trapezoidNodeCumulative k (Ncut k - 1) +
          -(trapezoidNodeCumulative k p) ≤ (0 : Q')) →
      (0 : Q') ≤ trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k s) →
      signedChordSum k (Ncut k - 1) s +
          (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) ≤
        (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative k (Ncut k - 1) *
              driftSqFactor k 0))) +
          (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative k (Ncut k - 1) *
              driftSqFactor k 0)))) :
    compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k)
          (Ncut k - 1) + trapezoidTerminalCorrection k ≤
      Q'.mkPos 24 25 (by decide) *
        (-(trapezoidNodeCumulative k (Ncut k - 1) * driftSqFactor k 0)) := by
  let L := Ncut k - 1
  obtain ⟨s, hsL, hs0, hsfirst⟩ :=
    exists_harmonic_terminal_carrier_crossing k L
  have hdef := compensatedAbelDefect_twice_le_signedChord_of_crossing
    k L s hsL (fun p _ hp => hsfirst p hp) hs0
  have hpay := hbudget s hsL hsfirst hs0
  let a := compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L +
    trapezoidTerminalCorrection k
  let b := Q'.mkPos 24 25 (by decide) *
    (-(trapezoidNodeCumulative k L * driftSqFactor k 0))
  have hadd := Q'.add_le_add hdef
    (Q'.le_refl' (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k))
  have hrearr :
      (compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L +
          compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L) +
        (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) ≈
      a + a := by
    unfold a
    ring_qeqv
  have haa : a + a ≤ b + b :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrearr)
      (Q'.le_trans' _ _ _ hadd hpay)
  have htwo : Q'.ofNat 2 * a ≤ Q'.ofNat 2 * b :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv a))
      (Q'.le_trans' _ _ _ haa
        (Q'.ge_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv b)))
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos
    (show (0 : Q') < Q'.ofNat 2 by decide) htwo

/-- The signed crossing budget also supplies the sign of its terminal reserve,
so the `24/25` estimate strengthens to the full compensated reserve and closes
the weighted trapezoid residual. -/
theorem weightedTrapezoidResidual_nonpos_of_signed_crossing_budget
    (k : Nat)
    (hbudget : ∀ s, s ≤ Ncut k - 1 →
      (∀ p, p < s →
        trapezoidNodeCumulative k (Ncut k - 1) +
          -(trapezoidNodeCumulative k p) ≤ (0 : Q')) →
      (0 : Q') ≤ trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k s) →
      signedChordSum k (Ncut k - 1) s +
          (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) ≤
        (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative k (Ncut k - 1) *
              driftSqFactor k 0))) +
          (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative k (Ncut k - 1) *
              driftSqFactor k 0)))) :
    weightedTrapezoidResidual k ≤ (0 : Q') := by
  let L := Ncut k - 1
  let z := -(trapezoidNodeCumulative k L * driftSqFactor k 0)
  let c := Q'.mkPos 24 25 (by decide)
  let b := c * z
  obtain ⟨s, hsL, hs0, hsfirst⟩ :=
    exists_harmonic_terminal_carrier_crossing k L
  have hpay := hbudget s hsL hsfirst hs0
  have hsum0 := signedChordSum_nonneg_of_crossing k L s hsL hs0
  have hterm0 := trapezoidTerminalCorrection_nonneg k
  have hleft0 : (0 : Q') ≤ signedChordSum k L s +
      (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) :=
    Q'.zero_le_add _ _ hsum0 (Q'.zero_le_add _ _ hterm0 hterm0)
  have hbb0 : (0 : Q') ≤ b + b :=
    Q'.le_trans' _ _ _ hleft0 hpay
  have h2b0 : (0 : Q') ≤ Q'.ofNat 2 * b :=
    Q'.le_trans' _ _ _ hbb0
      (Q'.ge_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv b))
  have hb0 : (0 : Q') ≤ b :=
    Q'.nonneg_of_mul_pos (show (0 : Q') < Q'.ofNat 2 by decide) h2b0
  have hcpos : (0 : Q') < c := by
    unfold c
    decide
  have hz0 : (0 : Q') ≤ z := Q'.nonneg_of_mul_pos hcpos hb0
  have hc1 : c ≤ (1 : Q') := by
    unfold c
    decide
  have hcz : c * z ≤ (1 : Q') * z :=
    Q'.mul_le_mul_of_nonneg_right _ _ z hc1 hz0
  have hfrac : c * z ≤ z :=
    Q'.le_trans' _ _ _ hcz (Q'.le_of_eqv (Q'.one_mul_eqv z))
  have h24 :=
    compensated_reserve_twentyFourTwentyFive_of_signed_crossing_budget k hbudget
  exact weightedTrapezoidResidual_nonpos_of_reserve k
    (Q'.le_trans' _ _ _ h24 hfrac)

#print axioms compensated_reserve_twentyFourTwentyFive_of_signed_crossing_budget
#print axioms signedChordSum_nonneg_of_crossing
#print axioms trapezoidTerminalCorrection_nonneg
#print axioms weightedTrapezoidResidual_nonpos_of_signed_crossing_budget

end YMGap.Continuum.HarmonicSignedChordBudgetBridge
