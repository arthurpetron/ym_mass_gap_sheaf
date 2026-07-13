/-
Weighted Abel reserve for the harmonic trapezoid carrier.

This downstream file keeps false reverse-Abel routes as exact kernel fences
and develops compensated carriers without changing the shared import graph.
-/

import YMGap.Continuum.HarmonicHalfEdgeDominance

namespace YMGap.Continuum.HarmonicWeightedAbelReserve

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicWeightDriftFence
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

/-- Reverse/suffix Abel cannot close by uniform suffix signs.  At the smallest
scale, the proper suffix beginning at node one (including the terminal half
edge at node `Ncut 0`) is strictly positive. -/
theorem reverse_suffix_nonpos_fails_k0_p1 :
    not (
      (trapezoidNodeCoeff 0 1 + trapezoidNodeCoeff 0 2) +
          (trapezoidNodeCoeff 0 3 + harmonicD 0 * oldAdj 0 3) ≤
        (0 : Q')) := by
  unfold trapezoidNodeCoeff harmonicD harmonicA twoInvSq oldAdj oldDiag
    coordNormSq adjCorr harmW harmU
    ReciprocalBernoulliUpper.oneSub unit invSqTerm coeffW dimQ c4
    qpow Ncut fsum
  decide

/-- A two-cell `U_p=(-T_p)G_p` telescope also fails at the first possible
block.  This is the exact local condition left after comparing two successive
`U` increments with the two Abel increments. -/
theorem twoCell_telescope_fails_k0_p0 :
    not (
      (trapezoidNodeCumulative 0 1 +
          -(trapezoidNodeCumulative 0 0)) * driftSqFactor 0 1 +
        (trapezoidNodeCumulative 0 2 +
          -(trapezoidNodeCumulative 0 1)) * driftSqFactor 0 2 ≤
      (0 : Q')) := by
  unfold trapezoidNodeCumulative harmonicD harmonicA twoInvSq oldAdj
    coordNormSq adjCorr driftSqFactor driftRatio harmW harmU
    ReciprocalBernoulliUpper.oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

/-! ## Exact compensated Abel form -/

def forwardIncrementSum (x : Nat → Q') (n : Nat) : Q' :=
  fsum (fun p => x (p + 1) + -(x p)) n

def compensatedAbelDefect (c x : Nat → Q') (n : Nat) : Q' :=
  fsum (fun p =>
    (abelPrefix c n + -(abelPrefix c p)) * (x (p + 1) + -(x p))) n

theorem driftSqFactor_pow_eqv (k p : Nat) :
    driftSqFactor k p ≈ qpow (driftRatio k) (driftSqExp p) := by
  unfold driftSqFactor driftSqExp
  exact Q'.eqv_symm
    (HeatKernelRGStep.qpow_add (driftRatio k) (c4 p) (c4 p))

theorem driftSqExp_succ_gap (p : Nat) :
    driftSqExp p + (4 * p + 6) = driftSqExp (p + 1) := by
  unfold driftSqExp c4
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- Exact increasing-weight cell factor. -/
theorem driftSqFactor_succ_eqv (k p : Nat) :
    driftSqFactor k (p + 1) ≈
      driftSqFactor k p * qpow (driftRatio k) (4 * p + 6) := by
  refine Q'.eqv_trans _ _ _ (driftSqFactor_pow_eqv k (p + 1)) ?_
  rw [← driftSqExp_succ_gap p]
  refine Q'.eqv_trans _ _ _
    (HeatKernelRGStep.qpow_add (driftRatio k) (driftSqExp p) (4 * p + 6)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (driftSqFactor_pow_eqv k p))

theorem driftSqFactor_increment_eqv (k p : Nat) :
    driftSqFactor k (p + 1) + -(driftSqFactor k p) ≈
      driftSqFactor k p *
        (qpow (driftRatio k) (4 * p + 6) + -(1 : Q')) := by
  let G := driftSqFactor k p
  let q := qpow (driftRatio k) (4 * p + 6)
  have hs : driftSqFactor k (p + 1) ≈ G * q := driftSqFactor_succ_eqv k p
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hs) ?_
  have hone : -(driftSqFactor k p) ≈ -(G * (1 : Q')) :=
    Q'.neg_eqv_congr _ _ (Q'.eqv_symm (Q'.mul_one_eqv G))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (G * q) _ _ hone) ?_
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv G q (-(1 : Q'))) ?_)
  exact Q'.add_eqv_congr_left (G * q) _ _ (Q'.mul_neg_eqv G (1 : Q'))

theorem driftSqFactor_zero_eqv (k : Nat) :
    driftSqFactor k 0 ≈ (1 : Q') := by
  unfold driftSqFactor c4 qpow
  exact Q'.one_mul_eqv (1 : Q')

/-- At `k=0`, the least constant envelope forced by the initial carrier,
`W=-T₀`, already overspends the terminal reserve.  Hence a monotone envelope
which never drops below its initial value cannot be the closing mechanism. -/
theorem constant_initial_envelope_fails_k0 :
    not (
      (-(trapezoidNodeCumulative 0 0)) *
          forwardIncrementSum (driftSqFactor 0) (Ncut 0 - 1) ≤
        (-(trapezoidNodeCumulative 0 (Ncut 0 - 1))) *
          driftSqFactor 0 (Ncut 0 - 1)) := by
  unfold forwardIncrementSum trapezoidNodeCumulative harmonicD harmonicA
    twoInvSq oldAdj coordNormSq adjCorr driftSqFactor driftRatio harmW harmU
    ReciprocalBernoulliUpper.oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

private theorem add_diff_cancel (a b : Q') : a + (b + (-a)) ≈ b := by
  have hr : a + (b + (-a)) ≈ b + (a + (-a)) := by ring_qeqv
  refine Q'.eqv_trans _ _ _ hr ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left b _ _ (Q'.add_neg_self_eqv a)) ?_
  exact q_add_zero_eqv b

theorem start_add_forwardIncrementSum (x : Nat → Q') : ∀ n,
    x 0 + forwardIncrementSum x n ≈ x n
  | 0 => q_add_zero_eqv _
  | n + 1 => by
      have ih := start_add_forwardIncrementSum x n
      unfold forwardIncrementSum
      simp only [fsum_succ]
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      exact add_diff_cancel _ _

private theorem compensatedAbelDefect_succ (c x : Nat → Q') (n : Nat) :
    compensatedAbelDefect c x (n + 1) ≈
      compensatedAbelDefect c x n +
        c (n + 1) * forwardIncrementSum x (n + 1) := by
  let C := abelPrefix c n
  let q := c (n + 1)
  let d := fun p => x (p + 1) + -(x p)
  have hCp : abelPrefix c (n + 1) ≈ C + q := Q'.eqv_refl _
  have hterm : ∀ p,
      (abelPrefix c (n + 1) + -(abelPrefix c p)) * d p ≈
        (C + -(abelPrefix c p)) * d p + q * d p := by
    intro p
    have hbase : abelPrefix c (n + 1) + -(abelPrefix c p) ≈
        (C + -(abelPrefix c p)) + q := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ hCp) ?_
      ring_qeqv
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hbase) ?_
    exact Q'.add_mul_eqv _ _ _
  unfold compensatedAbelDefect
  simp only [fsum_succ]
  have hsum := CubeRatioBounds.fsum_eqv_congr _ _ hterm n
  have hsplit := CubeRatioBounds.fsum_add
    (fun p => (C + -(abelPrefix c p)) * d p)
    (fun p => q * d p) n
  have hqsum : fsum (fun p => q * d p) n ≈
      q * forwardIncrementSum x n := by
    unfold forwardIncrementSum d
    exact Q'.eqv_symm
      (CubeRatioBounds.fsum_const_mul q
        (fun p => x (p + 1) + -(x p)) n)
  have hlast :
      (abelPrefix c (n + 1) + -(abelPrefix c n)) * d n ≈ q * d n := by
    have hc : abelPrefix c (n + 1) + -(abelPrefix c n) ≈ q := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ hCp) ?_
      unfold C
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
      exact add_diff_cancel _ _
    exact Q'.mul_eqv_congr_right _ _ _ hc
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ hsum hsplit) hlast) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left _ _ _ hqsum)) ?_
  unfold forwardIncrementSum d q C
  simp only [fsum_succ]
  ring_qeqv

/-- Exact finite Abel identity with the terminal carrier separated as a
constant baseline.  For increasing weights this exposes the genuine positive
defect `(C_n-C_p)·(x_{p+1}-x_p)` rather than hiding it behind prefix signs. -/
theorem finite_abel_compensated (c x : Nat → Q') : ∀ n,
    abelPrefix c n * x n + abelIncrementSum c x n ≈
      abelPrefix c n * x 0 + compensatedAbelDefect c x n
  | 0 => by
      simp only [abelPrefix, abelIncrementSum, compensatedAbelDefect,
        fsum_succ, fsum_zero, Q'.zero_add']
      exact Q'.eqv_refl _
  | n + 1 => by
      have hab := finite_abel c x (n + 1)
      have habn := finite_abel c x n
      have ih := finite_abel_compensated c x n
      have hstart :
          abelPrefix c (n + 1) * x (n + 1) +
              abelIncrementSum c x (n + 1) ≈
            (abelPrefix c n * x 0 + compensatedAbelDefect c x n) +
              c (n + 1) * x (n + 1) := by
        refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hab) ?_
        simp only [fsum_succ]
        exact Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_trans _ _ _ habn ih)
      have hdef := compensatedAbelDefect_succ c x n
      have hforward := start_add_forwardIncrementSum x (n + 1)
      have hfinish :
          (abelPrefix c n * x 0 + compensatedAbelDefect c x n) +
              c (n + 1) * x (n + 1) ≈
            abelPrefix c (n + 1) * x 0 +
              compensatedAbelDefect c x (n + 1) := by
        refine Q'.eqv_trans _
          ((abelPrefix c n * x 0 + compensatedAbelDefect c x n) +
            c (n + 1) * (x 0 + forwardIncrementSum x (n + 1))) _ ?_ ?_
        · exact Q'.add_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left (c (n + 1)) _ _
              (Q'.eqv_symm hforward))
        · refine Q'.eqv_trans _
            ((abelPrefix c n + c (n + 1)) * x 0 +
              (compensatedAbelDefect c x n +
                c (n + 1) * forwardIncrementSum x (n + 1))) _
            (by ring_qeqv) ?_
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (Q'.eqv_symm hdef)
      exact Q'.eqv_trans _ _ _ hstart hfinish

/-- Harmonic specialization of the compensated identity. -/
theorem trapezoidNode_finite_abel_compensated (k n : Nat) :
    fsum (fun i => trapezoidNodeCoeff k i * driftSqFactor k i) (n + 1) ≈
      trapezoidNodeCumulative k n * driftSqFactor k 0 +
        compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) n := by
  refine Q'.eqv_trans _ _ _ (trapezoidNode_finite_abel k n) ?_
  refine Q'.eqv_trans _
    (abelPrefix (trapezoidNodeCoeff k) n * driftSqFactor k n +
      abelIncrementSum (trapezoidNodeCoeff k) (driftSqFactor k) n) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm (abelPrefix_trapezoidNodeCoeff k n)))
  refine Q'.eqv_trans _ _ _
    (finite_abel_compensated (trapezoidNodeCoeff k) (driftSqFactor k) n) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (abelPrefix_trapezoidNodeCoeff k n))

/-! ## Exact terminal-corrected reserve -/

def trapezoidTerminalCorrection (k : Nat) : Q' :=
  harmonicD k * oldAdj k (Ncut k - 1) * driftSqFactor k (Ncut k)

def weightedTrapezoidResidual (k : Nat) : Q' :=
  fsum (fun i => trapezoidNodeCoeff k i * driftSqFactor k i) (Ncut k) +
    trapezoidTerminalCorrection k

private theorem weightedNode_terminal_eq (k : Nat) : ∀ n,
    fsum (fun i => trapezoidNodeCoeff k i * driftSqFactor k i) (n + 1) +
        (harmonicD k * oldAdj k n) * driftSqFactor k (n + 1) ≈
      harmonicD k * fsum (fun i =>
          oldAdj k i * (driftSqFactor k i + driftSqFactor k (i + 1))) (n + 1) +
        -(((harmonicA k + twoInvSq k * harmonicD k) +
              (harmonicA k + twoInvSq k * harmonicD k)) *
            fsum (fun i => oldDiag k i * driftSqFactor k i) (n + 1))
  | 0 => by
      simp only [fsum_succ, fsum_zero, Q'.zero_add', trapezoidNodeCoeff]
      ring_qeqv
  | n + 1 => by
      have ih := weightedNode_terminal_eq k n
      let B := (harmonicA k + twoInvSq k * harmonicD k) +
        (harmonicA k + twoInvSq k * harmonicD k)
      let S := fsum (fun i => trapezoidNodeCoeff k i * driftSqFactor k i) (n + 1)
      let E := fsum (fun i =>
        oldAdj k i * (driftSqFactor k i + driftSqFactor k (i + 1))) (n + 1)
      let Z := fsum (fun i => oldDiag k i * driftSqFactor k i) (n + 1)
      have hstart :
          fsum (fun i => trapezoidNodeCoeff k i * driftSqFactor k i) (n + 1 + 1) +
              (harmonicD k * oldAdj k (n + 1)) * driftSqFactor k (n + 1 + 1) ≈
            (S + (harmonicD k * oldAdj k n) * driftSqFactor k (n + 1)) +
              ((harmonicD k * oldAdj k (n + 1)) *
                  (driftSqFactor k (n + 1) + driftSqFactor k (n + 1 + 1)) +
                -(B * (oldDiag k (n + 1) * driftSqFactor k (n + 1)))) := by
        change (S + trapezoidNodeCoeff k (n + 1) * driftSqFactor k (n + 1)) +
            (harmonicD k * oldAdj k (n + 1)) * driftSqFactor k (n + 1 + 1) ≈ _
        simp only [trapezoidNodeCoeff]
        unfold B
        ring_qeqv
      refine Q'.eqv_trans _ _ _ hstart ?_
      have ih' : S + (harmonicD k * oldAdj k n) * driftSqFactor k (n + 1) ≈
          harmonicD k * E + -(B * Z) := by
        exact ih
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih') ?_
      unfold E Z B
      simp only [fsum_succ]
      ring_qeqv

/-- Expansion of the terminal-corrected node sum into the full trapezoid
energy minus twice the diagonal budget. -/
theorem weightedTrapezoidResidual_eq_energy (k : Nat) :
    weightedTrapezoidResidual k ≈
      harmonicD k * trapezoidDriftA k +
        -(((harmonicA k + twoInvSq k * harmonicD k) +
              (harmonicA k + twoInvSq k * harmonicD k)) * driftDiagPrefix k) := by
  let L := Ncut k - 1
  have hN : 1 ≤ Ncut k := by
    unfold Ncut
    exact Nat.mul_pos (by omega) (by omega)
  have hLN : L + 1 = Ncut k := Nat.sub_add_cancel hN
  have h := weightedNode_terminal_eq k L
  unfold weightedTrapezoidResidual trapezoidTerminalCorrection
  rw [← hLN]
  unfold trapezoidDriftA driftDiagPrefix
  exact h

/-- The full weighted trapezoid residual is exactly the compensated Abel
defect plus the terminal half-edge correction and the terminal carrier
evaluated at the harmless base weight `G₀`. -/
theorem weightedTrapezoidResidual_eq_compensated (k : Nat) :
    let L := Ncut k - 1
    weightedTrapezoidResidual k ≈
      trapezoidNodeCumulative k L * driftSqFactor k 0 +
        (compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L +
          trapezoidTerminalCorrection k) := by
  dsimp only
  let L := Ncut k - 1
  have hN : 1 ≤ Ncut k := by
    unfold Ncut
    exact Nat.mul_pos (by omega) (by omega)
  have hLN : L + 1 = Ncut k := Nat.sub_add_cancel hN
  unfold weightedTrapezoidResidual
  rw [← hLN]
  have h := trapezoidNode_finite_abel_compensated k L
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ h)
    (Q'.add_assoc_eqv _ _ _)

/-- Consumer for the precise quantitative reserve.  No sign inference from
prefixes is used: the hypothesis explicitly pays both the compensated
positive increments and the missing terminal half-edge. -/
theorem weightedTrapezoidResidual_nonpos_of_reserve (k : Nat)
    (hreserve :
      compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k)
            (Ncut k - 1) + trapezoidTerminalCorrection k ≤
        -(trapezoidNodeCumulative k (Ncut k - 1) * driftSqFactor k 0)) :
    weightedTrapezoidResidual k ≤ (0 : Q') := by
  let a := trapezoidNodeCumulative k (Ncut k - 1) * driftSqFactor k 0
  let b := compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k)
      (Ncut k - 1) + trapezoidTerminalCorrection k
  have hadd := Q'.add_le_add_left a b (-a) hreserve
  have hzero : a + (-a) ≈ (0 : Q') := Q'.add_neg_self_eqv a
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (weightedTrapezoidResidual_eq_compensated k))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hzero))

/-- Exact smallest-scale anchor for the compensated reserve.  This is a
closed rational derivation, not a measured constant. -/
theorem compensated_reserve_k0 :
    compensatedAbelDefect (trapezoidNodeCoeff 0) (driftSqFactor 0)
          (Ncut 0 - 1) + trapezoidTerminalCorrection 0 ≤
      -(trapezoidNodeCumulative 0 (Ncut 0 - 1) * driftSqFactor 0 0) := by
  unfold compensatedAbelDefect abelPrefix trapezoidNodeCoeff
    trapezoidTerminalCorrection trapezoidNodeCumulative harmonicD harmonicA
    twoInvSq oldAdj oldDiag coordNormSq adjCorr driftSqFactor driftRatio
    harmW harmU ReciprocalBernoulliUpper.oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

/-- The proposed uniform `24/25` reserve has genuine exact slack at the
sharp smallest scale. -/
theorem compensated_reserve_twentyFourTwentyFive_k0 :
    compensatedAbelDefect (trapezoidNodeCoeff 0) (driftSqFactor 0)
          (Ncut 0 - 1) + trapezoidTerminalCorrection 0 ≤
      Q'.mkPos 24 25 (by decide) *
        (-(trapezoidNodeCumulative 0 (Ncut 0 - 1) * driftSqFactor 0 0)) := by
  unfold compensatedAbelDefect abelPrefix trapezoidNodeCoeff
    trapezoidTerminalCorrection trapezoidNodeCumulative harmonicD harmonicA
    twoInvSq oldAdj oldDiag coordNormSq adjCorr driftSqFactor driftRatio
    harmW harmU ReciprocalBernoulliUpper.oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

theorem weightedTrapezoidResidual_nonpos_k0 :
    weightedTrapezoidResidual 0 ≤ (0 : Q') :=
  weightedTrapezoidResidual_nonpos_of_reserve 0 compensated_reserve_k0

end YMGap.Continuum.HarmonicWeightedAbelReserve

#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.reverse_suffix_nonpos_fails_k0_p1
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.twoCell_telescope_fails_k0_p0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.constant_initial_envelope_fails_k0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftSqFactor_pow_eqv
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftSqExp_succ_gap
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftSqFactor_succ_eqv
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftSqFactor_increment_eqv
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftSqFactor_zero_eqv
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.start_add_forwardIncrementSum
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.finite_abel_compensated
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.trapezoidNode_finite_abel_compensated
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.weightedTrapezoidResidual_eq_compensated
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.weightedTrapezoidResidual_nonpos_of_reserve
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.compensated_reserve_k0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.compensated_reserve_twentyFourTwentyFive_k0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.weightedTrapezoidResidual_nonpos_k0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.weightedTrapezoidResidual_eq_energy
