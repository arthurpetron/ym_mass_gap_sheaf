/-
Track 11.7-fusion / R4m -- exact terminal half-time shell.

At channel `s = 2*N-1`, the two Clebsch boxes contain only the endpoint
pair `(N,N)` and the two orientations of `(N-1,N)`.  The heat factor in the
target is exactly the heat factor in the coefficient successor identity

  N c_N = (N+1) w^(2N+1) c_(N-1).

Consequently the terminal half-time inequality is a dimension comparison,
not a growing convolution.  This module proves it for every positive cutoff
and then specializes it to every physical scale.  It removes the last
channel from the live integer-certificate family.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFenceTopShell
import YMGap.Continuum.FusionStrandExactReindex
import YMGap.Continuum.HarmonicSymbolicAnchorRatio
import YMGap.Continuum.P2BlockCompatibleSchedule

namespace YMGap.Continuum.P2HalfTimeTerminalShell

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2RetunedFenceTopShell
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem ofNat_le_ofNat {a b : Nat} (h : a <= b) :
    Q'.ofNat a <= Q'.ofNat b := by
  show (Int.ofNat a) * (1 : Int) <= (Int.ofNat b) * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr h

/-! ## 1. Endpoint coefficient algebra -/

/-- The terminal half-time scalar inequality after the two endpoint boxes
have collapsed. -/
theorem terminalHalfTimeScalar (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 1 <= N) :
    dimQ (2 * N - 1) * (coeffW w N * coeffW w N) <=
      qpow w (2 * N + 1) *
        (dimQ (2 * N) *
          ((coeffW w (N - 1) * coeffW w N) +
            (coeffW w (N - 1) * coeffW w N))) := by
  let n := Q'.ofNat N
  let np := Q'.ofNat (N + 1)
  let hi := Q'.ofNat (2 * N + 1)
  let q := qpow w (2 * N + 1)
  let B := coeffW w (N - 1)
  let C := coeffW w N
  let X := q * (B * C)
  have hrec : n * C ≈ (np * q) * B := by
    simpa only [n, np, q, B, C,
      show N - 1 + 1 = N by omega,
      show N - 1 + 2 = N + 1 by omega,
      show 2 * (N - 1) + 3 = 2 * N + 1 by omega] using
      coeffW_succ_cross_eqv w (N - 1)
  have edimLow : dimQ (2 * N - 1) ≈ n + n := by
    unfold dimQ
    have hadd := Q'.ofNat_add_eqv N N
    simpa only [n, show 2 * N - 1 + 1 = N + N by omega] using hadd
  have edimHigh : dimQ (2 * N) ≈ hi := by
    unfold dimQ
    exact Q'.eqv_refl _
  have eleft :
      dimQ (2 * N - 1) * (C * C) ≈
        (np * X) + (np * X) := by
    refine Q'.eqv_trans _ ((n + n) * (C * C)) _
      (Q'.mul_eqv_congr_right _ _ _ edimLow) ?_
    refine Q'.eqv_trans _ (((n * C) * C) + ((n * C) * C)) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      ((((np * q) * B) * C) + (((np * q) * B) * C)) _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ C hrec)
        (Q'.mul_eqv_congr_right _ _ C hrec)) ?_
    dsimp only [X]
    ring_qeqv
  have eright :
      q * (dimQ (2 * N) * ((B * C) + (B * C))) ≈
        (hi * X) + (hi * X) := by
    refine Q'.eqv_trans _ (q * (hi * ((B * C) + (B * C)))) _
      (Q'.mul_eqv_congr_left q _ _
        (Q'.mul_eqv_congr_right _ _ _ edimHigh)) ?_
    dsimp only [X]
    ring_qeqv
  have hdim : np <= hi := by
    exact ofNat_le_ofNat (by omega)
  have hq0 : (0 : Q') <= q := qpow_nonneg w hw0 (2 * N + 1)
  have hB0 : (0 : Q') <= B := coeffW_nonneg hw0 (N - 1)
  have hC0 : (0 : Q') <= C := coeffW_nonneg hw0 N
  have hX0 : (0 : Q') <= X :=
    Q'.mul_nonneg _ _ hq0 (Q'.mul_nonneg _ _ hB0 hC0)
  have hscaled : np * X <= hi * X :=
    Q'.mul_le_mul_of_nonneg_right _ _ X hdim hX0
  have hdouble : (np * X) + (np * X) <= (hi * X) + (hi * X) :=
    Q'.add_le_add hscaled hscaled
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hdouble (Q'.ge_of_eqv eright))

/-! ## 2. Clebsch box and line-sum terminal cells -/

/-- The last supported half-time Clebsch-box cell is automatic for every
nonnegative heat weight and positive cutoff. -/
theorem halfTimeBox_terminal (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 1 <= N) :
    dimQ (2 * N - 1) * boxSum w N (2 * N) <=
      qpow w (2 * N + 1) *
        (dimQ (2 * N) * boxSum w N (2 * N - 1)) := by
  let B := coeffW w (N - 1)
  let C := coeffW w N
  have hscalar := terminalHalfTimeScalar w N hw0 hN
  have eleft :
      dimQ (2 * N - 1) * boxSum w N (2 * N) ≈
        dimQ (2 * N - 1) * (C * C) :=
    Q'.mul_eqv_congr_left _ _ _ (by
      simpa only [C] using boxSum_top w N)
  have eright :
      qpow w (2 * N + 1) *
          (dimQ (2 * N) * boxSum w N (2 * N - 1)) ≈
        qpow w (2 * N + 1) *
          (dimQ (2 * N) * ((B * C) + (B * C))) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (by
        simpa only [B, C] using boxSum_top_odd w N hN))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hscalar (Q'.ge_of_eqv eright))

/-- Exact A1 transport of the terminal box cell. -/
theorem halfTimeLineSum_terminal (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 1 <= N) :
    dimQ (2 * N - 1) * lineSum (lagCorr w N) (2 * N) <=
      qpow w (2 * N + 1) *
        (dimQ (2 * N) * lineSum (lagCorr w N) (2 * N - 1)) := by
  have hbox := halfTimeBox_terminal w N hw0 hN
  have eleft :
      dimQ (2 * N - 1) * lineSum (lagCorr w N) (2 * N) ≈
        dimQ (2 * N - 1) * boxSum w N (2 * N) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (2 * N)))
  have eright :
      qpow w (2 * N + 1) *
          (dimQ (2 * N) * boxSum w N (2 * N - 1)) ≈
        qpow w (2 * N + 1) *
          (dimQ (2 * N) * lineSum (lagCorr w N) (2 * N - 1)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N (2 * N - 1)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hbox (Q'.le_of_eqv eright))

/-- Every physical scale inherits the constant-cost terminal proof. -/
theorem physical_halfTime_lineSum_terminal (k : Nat) :
    dimQ (2 * blockNcut k - 1) *
        lineSum (lagCorr (blockWeight k) (blockNcut k)) (2 * blockNcut k) <=
      qpow (blockWeight k) (2 * blockNcut k + 1) *
        (dimQ (2 * blockNcut k) *
          lineSum (lagCorr (blockWeight k) (blockNcut k))
            (2 * blockNcut k - 1)) :=
  halfTimeLineSum_terminal (blockWeight k) (blockNcut k)
    (blockWeight_nonneg k) (blockNcut_pos k)

end YMGap.Continuum.P2HalfTimeTerminalShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeTerminalShell.terminalHalfTimeScalar
#print axioms YMGap.Continuum.P2HalfTimeTerminalShell.halfTimeBox_terminal
#print axioms YMGap.Continuum.P2HalfTimeTerminalShell.halfTimeLineSum_terminal
#print axioms YMGap.Continuum.P2HalfTimeTerminalShell.physical_halfTime_lineSum_terminal
