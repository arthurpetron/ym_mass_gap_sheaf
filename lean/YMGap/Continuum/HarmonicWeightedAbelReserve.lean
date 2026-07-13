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

/-- A drift-weighted old diagonal mode is exactly the next harmonic diagonal
mode. -/
theorem oldDiag_mul_driftSq_eqv_next (k p : Nat) :
    oldDiag k p * driftSqFactor k p ≈ oldDiag (k + 1) p := by
  unfold oldDiag driftSqFactor
  exact Q'.eqv_symm (coeffSq_harmonic_step k p)

/-- Likewise the geometric midpoint factor transports an old adjacent mode
exactly to the next harmonic adjacent mode. -/
theorem oldAdj_mul_driftAdj_eqv_next (k p : Nat) :
    oldAdj k p * driftAdjFactor k p ≈ oldAdj (k + 1) p := by
  have hi := coeffW_harmonic_step k p
  have hj := coeffW_harmonic_step k (p + 1)
  unfold oldAdj driftAdjFactor
  apply Q'.eqv_symm
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hi)
      (Q'.mul_eqv_congr_left _ _ _ hj)) ?_
  ring_qeqv

private theorem ofNat_pos_local {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Q'.ofNat_succ_pos m

private theorem ofNat_mul_unit_eqv_one (n : Nat) (hn : 0 < n) :
    Q'.ofNat n * unit n hn ≈ (1 : Q') := by
  unfold unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

/-- Cleared rational form of the harmonic drift ratio. -/
theorem driftRatio_mul_driftDen_eqv (k : Nat) :
    driftRatio k * Q'.ofNat (driftDen k) ≈
      Q'.ofNat ((k + 2) * (k + 2)) := by
  have hs := harmW_step_eqv k
  have hc := harmW_step_cleared k
  have hscaled :
      harmW k * (driftRatio k * Q'.ofNat (driftDen k)) ≈
        harmW k * Q'.ofNat ((k + 2) * (k + 2)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hs)) hc
  exact Q'.mul_left_cancel_of_pos (harmW_pos k) hscaled

/-- Exact unit-increment representation
`r_k = 1 + 1/((k+2)^2-1)`. -/
theorem driftRatio_eqv_one_add_unitDen (k : Nat) :
    driftRatio k ≈ (1 : Q') + unit (driftDen k) (driftDen_pos k) := by
  let d := driftDen k
  let u := unit d (driftDen_pos k)
  have hnat : d + 1 = (k + 2) * (k + 2) := by
    unfold d driftDen
    have h4 : 1 ≤ (k + 2) * (k + 2) :=
      Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by omega))
    exact Nat.sub_add_cancel h4
  have hdu : Q'.ofNat d * u ≈ (1 : Q') :=
    ofNat_mul_unit_eqv_one d (driftDen_pos k)
  have hone : Q'.ofNat 1 ≈ (1 : Q') := by decide
  have hright : Q'.ofNat d * ((1 : Q') + u) ≈
      Q'.ofNat ((k + 2) * (k + 2)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_one_eqv _) hdu) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (Q'.ofNat d) _ _ (Q'.eqv_symm hone)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.ofNat_add_eqv d 1)) ?_
    exact Q'.eqv_of_eq (congrArg Q'.ofNat hnat)
  have hleft : Q'.ofNat d * driftRatio k ≈
      Q'.ofNat ((k + 2) * (k + 2)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (driftRatio_mul_driftDen_eqv k)
  exact Q'.mul_left_cancel_of_pos (ofNat_pos_local (driftDen_pos k))
    (Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright))

private theorem one_le_qpow_local {q : Q'} (hq : (1 : Q') ≤ q) :
    ∀ n, (1 : Q') ≤ qpow q n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hq0 : (0 : Q') ≤ q := Q'.le_trans' _ _ _ (by decide) hq
      have hi0 : (0 : Q') ≤ qpow q n := qpow_nonneg q hq0 n
      have hs : qpow q n * (1 : Q') ≤ qpow q n * q :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hq hi0
      exact Q'.le_trans' _ _ _ (one_le_qpow_local hq n)
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) hs)

/-- Rational binomial envelope in a form adapted to a reciprocal harmonic
step: `(1+u)^n ≤ 1+n·u·(1+u)^n`. -/
theorem qpow_one_add_growth {r u : Q'}
    (hu0 : (0 : Q') ≤ u) (hr : r ≈ (1 : Q') + u) : ∀ n,
    qpow r n ≤
      (1 : Q') + Q'.ofNat n * u * qpow r n
  | 0 => by
      have hz : Q'.ofNat 0 * u * qpow r 0 ≈ (0 : Q') := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
              (Q'.zero_mul_eqv u))) ?_
        exact Q'.zero_mul_eqv _
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_refl _)
        (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (1 : Q') _ _ hz) (q_add_zero_eqv _))))
  | n + 1 => by
      have hrle : (1 : Q') ≤ r := by
        have h := Q'.add_le_self_of_nonneg (1 : Q') u hu0
        exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv hr)
      have hr0 : (0 : Q') ≤ r := Q'.le_trans' _ _ _ (by decide) hrle
      have hi := qpow_one_add_growth hu0 hr n
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ r hi hr0
      let P := qpow r n
      have hPr : (1 : Q') ≤ P * r := one_le_qpow_local hrle (n + 1)
      have hus := Q'.mul_le_mul_of_nonneg_left _ _ u hPr hu0
      have hu : u ≤ u * (P * r) :=
        Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv u)) hus
      have hcommon := Q'.add_le_add_left
        ((1 : Q') + Q'.ofNat n * u * (P * r)) _ _ hu
      have hn : Q'.ofNat (n + 1) ≈ Q'.ofNat n + (1 : Q') := by
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      have hL : ((1 : Q') + Q'.ofNat n * u * P) * r ≈
          ((1 : Q') + Q'.ofNat n * u * (P * r)) + u := by
        refine Q'.eqv_trans _
          (r + Q'.ofNat n * u * (P * r)) _ (by ring_qeqv) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _ hr) ?_
        ring_qeqv
      have hR : ((1 : Q') + Q'.ofNat n * u * (P * r)) + u * (P * r) ≈
          (1 : Q') + Q'.ofNat (n + 1) * u * (P * r) := by
        apply Q'.eqv_symm
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (1 : Q') _ _
            (Q'.mul_eqv_congr_right _ _ (P * r)
              (Q'.mul_eqv_congr_right _ _ u hn))) ?_
        ring_qeqv
      change P * r ≤ (1 : Q') + Q'.ofNat (n + 1) * u * (P * r)
      exact Q'.le_trans' _ _ _ hm
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
          (Q'.le_trans' _ _ _ hcommon (Q'.le_of_eqv hR)))

/-- All harmonic drift powers satisfy the exact unit-denominator growth
envelope, with no transcendental estimate. -/
theorem driftRatio_qpow_growth (k n : Nat) :
    qpow (driftRatio k) n ≤
      (1 : Q') + Q'.ofNat n * unit (driftDen k) (driftDen_pos k) *
        qpow (driftRatio k) n :=
  qpow_one_add_growth (unit_nonneg _ _) (driftRatio_eqv_one_add_unitDen k) n

theorem qpow_one_add_increment_le {r u : Q'}
    (hu0 : (0 : Q') ≤ u) (hr : r ≈ (1 : Q') + u) (n : Nat) :
    qpow r n + -(1 : Q') ≤
      Q'.ofNat n * u * qpow r n := by
  have h := qpow_one_add_growth hu0 hr n
  have hadd := Q'.add_le_add_right _ _ (-(1 : Q')) h
  have hR : ((1 : Q') + Q'.ofNat n * u * qpow r n) + -(1 : Q') ≈
      Q'.ofNat n * u * qpow r n := by
    have hc : (1 : Q') + (-(1 : Q')) ≈ (0 : Q') := Q'.add_neg_self_eqv _
    refine Q'.eqv_trans _
      (((1 : Q') + (-(1 : Q'))) + Q'.ofNat n * u * qpow r n) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hc) (q_zero_add_eqv _)
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hR)

/-- Explicit cellwise upper envelope for every increasing drift increment. -/
theorem driftSqFactor_increment_le (k p : Nat) :
    driftSqFactor k (p + 1) + -(driftSqFactor k p) ≤
      driftSqFactor k p *
        (Q'.ofNat (4 * p + 6) * unit (driftDen k) (driftDen_pos k) *
          qpow (driftRatio k) (4 * p + 6)) := by
  let G := driftSqFactor k p
  let q := qpow (driftRatio k) (4 * p + 6)
  let U := Q'.ofNat (4 * p + 6) * unit (driftDen k) (driftDen_pos k) * q
  have hq : q + -(1 : Q') ≤ U :=
    qpow_one_add_increment_le (unit_nonneg _ _)
      (driftRatio_eqv_one_add_unitDen k) (4 * p + 6)
  have hG0 : (0 : Q') ≤ G := by
    unfold G driftSqFactor
    exact Q'.mul_nonneg _ _
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ G hq hG0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (driftSqFactor_increment_eqv k p)) hm

private theorem neg_oneSub_eqv (x : Q') :
    -((1 : Q') + (-x)) ≈ x + (-(1 : Q')) := by
  refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (1 : Q') (-x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-(1 : Q')) _ _ (Q'.neg_neg_eqv x)) ?_
  exact Q'.add_comm_eqv _ _

private theorem oneSub_eqv_neg_sub (x : Q') :
    (1 : Q') + (-x) ≈ -(x + (-(1 : Q'))) := by
  apply Q'.eqv_symm
  refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv x (-(1 : Q'))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-x) _ _ (Q'.neg_neg_eqv (1 : Q'))) ?_
  exact Q'.add_comm_eqv _ _

/-- Exact geometric cell factor for a harmonic reciprocal step. -/
theorem qpow_driftRatio_sub_one_eqv (k n : Nat) :
    qpow (driftRatio k) n + (-(1 : Q')) ≈
      unit (driftDen k) (driftDen_pos k) *
        HeatKernelRGStep.geomSum (driftRatio k) n := by
  let r := driftRatio k
  let S := HeatKernelRGStep.geomSum r n
  let a := r + (-(1 : Q'))
  let u := unit (driftDen k) (driftDen_pos k)
  have hf := HeatKernelRGStep.oneSub_pow_factor r n
  have hn := Q'.neg_eqv_congr _ _ hf
  have hL : -((1 : Q') + (-(qpow r n))) ≈
      qpow r n + (-(1 : Q')) := neg_oneSub_eqv _
  have hbase : (1 : Q') + (-r) ≈ -a := oneSub_eqv_neg_sub r
  have hB : ((1 : Q') + (-r)) * S ≈ -(a * S) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ S hbase) ?_
    exact Q'.neg_mul_eqv a S
  have hR : -(((1 : Q') + (-r)) * S) ≈ a * S := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hB) ?_
    exact Q'.neg_neg_eqv (a * S)
  have ha : a ≈ u := by
    have hr := driftRatio_eqv_one_add_unitDen k
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-(1 : Q')) hr) ?_
    have hc : (1 : Q') + (-(1 : Q')) ≈ (0 : Q') := Q'.add_neg_self_eqv _
    refine Q'.eqv_trans _
      (((1 : Q') + (-(1 : Q'))) + u) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ u hc) (q_zero_add_eqv u)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hL)
    (Q'.eqv_trans _ _ _ hn
      (Q'.eqv_trans _ _ _ hR (Q'.mul_eqv_congr_right _ _ S ha)))

theorem driftSqFactor_increment_geom_eqv (k p : Nat) :
    driftSqFactor k (p + 1) + -(driftSqFactor k p) ≈
      driftSqFactor k p *
        (unit (driftDen k) (driftDen_pos k) *
          HeatKernelRGStep.geomSum (driftRatio k) (4 * p + 6)) := by
  refine Q'.eqv_trans _ _ _ (driftSqFactor_increment_eqv k p) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (qpow_driftRatio_sub_one_eqv k (4 * p + 6))

/-- Sharper geometric upper bound for bases above one.  The unit term is kept
exact and only the remaining `n` terms are bounded by the last power. -/
theorem geomSum_succ_le_one_add_last {r : Q'} (hr : (1 : Q') ≤ r) : ∀ n,
    HeatKernelRGStep.geomSum r (n + 1) ≤
      (1 : Q') + Q'.ofNat n * qpow r (n + 1)
  | 0 => by
      unfold HeatKernelRGStep.geomSum
      have hz : Q'.ofNat 0 * qpow r 1 ≈ (0 : Q') := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv _)
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (q_zero_add_eqv _)
        (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (1 : Q') _ _ hz) (q_add_zero_eqv _))))
  | n + 1 => by
      have ih := geomSum_succ_le_one_add_last hr n
      have hadd := Q'.add_le_add_right _ _ (qpow r (n + 1)) ih
      have hnum : Q'.ofNat (n + 1) ≈ Q'.ofNat n + (1 : Q') := by
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      have hmid :
          ((1 : Q') + Q'.ofNat n * qpow r (n + 1)) + qpow r (n + 1) ≈
            (1 : Q') + Q'.ofNat (n + 1) * qpow r (n + 1) := by
        apply Q'.eqv_symm
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (1 : Q') _ _
            (Q'.mul_eqv_congr_right _ _ _ hnum)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (1 : Q') _ _
            (Q'.add_mul_eqv _ _ _)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (1 : Q') _ _
            (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv _))) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
      have hr0 : (0 : Q') ≤ r := Q'.le_trans' _ _ _ (by decide) hr
      have hp : qpow r (n + 1) ≤ qpow r (n + 1 + 1) := by
        have h0 := qpow_nonneg r hr0 (n + 1)
        have hm := Q'.mul_le_mul_of_nonneg_left _ _ (qpow r (n + 1)) hr h0
        exact Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (Q'.mul_one_eqv _)) hm
      have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (n + 1)) hp
        (ExpNeg.ofNat_nonneg' (n + 1))
      have hlast := Q'.add_le_add_left (1 : Q') _ _ hs
      change HeatKernelRGStep.geomSum r (n + 1 + 1) ≤
        (1 : Q') + Q'.ofNat (n + 1) * qpow r (n + 1 + 1)
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmid) hlast)

theorem driftRatio_geomSum_sharp_le (k n : Nat) :
    HeatKernelRGStep.geomSum (driftRatio k) (n + 1) ≤
      (1 : Q') + Q'.ofNat n * qpow (driftRatio k) (n + 1) :=
  geomSum_succ_le_one_add_last (one_le_driftRatio k) n

private theorem one_add_sub_one_eqv (r : Q') :
    (1 : Q') + (r + (-(1 : Q'))) ≈ r := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ (r + ((1 : Q') + (-(1 : Q')))) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left r _ _ (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact q_add_zero_eqv r

private theorem sub_mul_add_eqv (r P : Q') :
    (r + (-(1 : Q'))) * P + P ≈ r * P := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ P (Q'.add_mul_eqv _ _ _)) ?_
  have hn : (-(1 : Q')) * P ≈ -P := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (1 : Q') P) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv P)
  refine Q'.eqv_trans _ (r * P + ((-(1 : Q')) * P + P)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (r * P) _ _
      (Q'.add_eqv_congr_right _ _ P hn)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (r * P) _ _
      (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
        (Q'.add_neg_self_eqv P))) ?_
  exact q_add_zero_eqv _

/-- Weighted chord inequality for powers above one. -/
theorem weighted_power_chord {r : Q'} (hr : (1 : Q') ≤ r) (m : Nat) :
    Q'.ofNat (m + 1) * qpow r m ≤
      (1 : Q') + Q'.ofNat m * qpow r (m + 1) := by
  let u := r + (-(1 : Q'))
  let P := qpow r m
  have hu0 : (0 : Q') ≤ u := Q'.sub_nonneg_of_le hr
  have hru : r ≈ (1 : Q') + u :=
    Q'.eqv_symm (one_add_sub_one_eqv r)
  have hg := qpow_one_add_growth hu0 hru m
  have hadd := Q'.add_le_add_right _ _ (Q'.ofNat m * P) hg
  have hnum : Q'.ofNat (m + 1) ≈ Q'.ofNat m + (1 : Q') := by
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv m 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hL : P + Q'.ofNat m * P ≈ Q'.ofNat (m + 1) * P := by
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ P hnum) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv P)) ?_
    exact Q'.add_comm_eqv _ _
  have hR : ((1 : Q') + Q'.ofNat m * u * P) + Q'.ofNat m * P ≈
      (1 : Q') + Q'.ofNat m * (P * r) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.add_eqv_congr_left (1 : Q') _ _ ?_
    refine Q'.eqv_trans _
      (Q'.ofNat m * (u * P) + Q'.ofNat m * P) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_add_eqv (Q'.ofNat m) (u * P) P)) ?_
    refine Q'.mul_eqv_congr_left (Q'.ofNat m) _ _ ?_
    unfold u
    exact Q'.eqv_trans _ _ _ (sub_mul_add_eqv r P)
      (Q'.mul_comm_eqv r P)
  change P ≤ (1 : Q') + Q'.ofNat m * u * P at hg
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hR))

/-- Symmetric endpoint bound for a geometric sum above one.  Keeping the
last *actual* power, rather than the next power, is what makes the induction
lossless at the first cell. -/
theorem geomSum_succ_twice_le_chord {r : Q'} (hr : (1 : Q') ≤ r) : ∀ n,
    HeatKernelRGStep.geomSum r (n + 1) +
        HeatKernelRGStep.geomSum r (n + 1) ≤
      Q'.ofNat (n + 1) * ((1 : Q') + qpow r n)
  | 0 => by
      change ((0 : Q') + 1) + ((0 : Q') + 1) ≤
        Q'.ofNat 1 * ((1 : Q') + 1)
      exact Q'.le_of_eqv (by decide)
  | n + 1 => by
      let S := HeatKernelRGStep.geomSum r (n + 1)
      let P := qpow r (n + 1)
      let P₀ := qpow r n
      let N := Q'.ofNat (n + 1)
      let M := Q'.ofNat n
      have ih := geomSum_succ_twice_le_chord hr n
      have hchord := weighted_power_chord hr n
      change S + S ≤ N * ((1 : Q') + P₀) at ih
      change N * P₀ ≤ (1 : Q') + M * P at hchord
      have hadd := Q'.add_le_add ih (Q'.le_refl' (P + P))
      have hchord' := Q'.add_le_add
        (Q'.add_le_add (Q'.le_refl' N) hchord)
        (Q'.le_refl' (P + P))
      have hL : (S + P) + (S + P) ≈ (S + S) + (P + P) := by
        ring_qeqv
      have hmid : N * ((1 : Q') + P₀) + (P + P) ≈
          (N + N * P₀) + (P + P) := by
        refine Q'.add_eqv_congr_right _ _ _ ?_
        refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
        exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv N)
      have hN : N ≈ M + (1 : Q') := by
        unfold N M
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      have hN₂ : Q'.ofNat (n + 1 + 1) ≈ N + (1 : Q') := by
        unfold N
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (n + 1) 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      have hR : (N + ((1 : Q') + M * P)) + (P + P) ≈
          Q'.ofNat (n + 1 + 1) * ((1 : Q') + P) := by
        refine Q'.eqv_trans _
          ((M + (1 : Q')) + ((1 : Q') + M * P) + (P + P)) _
          (Q'.add_eqv_congr_right _ _ (P + P)
            (Q'.add_eqv_congr_right _ _ ((1 : Q') + M * P) hN)) ?_
        refine Q'.eqv_trans _
          (((M + (1 : Q')) + (1 : Q')) * ((1 : Q') + P)) _
          (by ring_qeqv) ?_
        refine Q'.eqv_trans _
          ((N + (1 : Q')) * ((1 : Q') + P)) _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.add_eqv_congr_right _ _ (1 : Q') (Q'.eqv_symm hN))) ?_
        exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hN₂)
      change (S + P) + (S + P) ≤
        Q'.ofNat (n + 1 + 1) * ((1 : Q') + P)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
        (Q'.le_trans' _ _ _ hadd
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmid)
            (Q'.le_trans' _ _ _ hchord' (Q'.le_of_eqv hR))))

#print axioms weighted_power_chord
#print axioms geomSum_succ_twice_le_chord

/-- The exact harmonic drift cell obeys the symmetric endpoint envelope.
The factor two is retained on the left, so no division or rounding enters the
constructive estimate. -/
theorem driftSqFactor_increment_twice_le_chord (k p : Nat) :
    (driftSqFactor k (p + 1) + -(driftSqFactor k p)) +
        (driftSqFactor k (p + 1) + -(driftSqFactor k p)) ≤
      driftSqFactor k p *
        (unit (driftDen k) (driftDen_pos k) *
          (Q'.ofNat ((4 * p + 5) + 1) *
            ((1 : Q') + qpow (driftRatio k) (4 * p + 5)))) := by
  let D := driftSqFactor k (p + 1) + -(driftSqFactor k p)
  let G := driftSqFactor k p
  let u := unit (driftDen k) (driftDen_pos k)
  let S := HeatKernelRGStep.geomSum (driftRatio k) ((4 * p + 5) + 1)
  have hgeom := geomSum_succ_twice_le_chord
    (one_le_driftRatio k) (4 * p + 5)
  change S + S ≤ Q'.ofNat ((4 * p + 5) + 1) *
    ((1 : Q') + qpow (driftRatio k) (4 * p + 5)) at hgeom
  have hu0 : (0 : Q') ≤ u := unit_nonneg _ _
  have hG0 : (0 : Q') ≤ G := by
    unfold G driftSqFactor
    exact Q'.mul_nonneg _ _
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ u hgeom hu0
  have hGu := Q'.mul_le_mul_of_nonneg_left _ _ G hu hG0
  have hD : D ≈ G * (u * S) := by
    unfold D G u S
    exact driftSqFactor_increment_geom_eqv k p
  have hL : D + D ≈ G * (u * (S + S)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hD hD) ?_
    ring_qeqv
  change D + D ≤ G *
    (u * (Q'.ofNat ((4 * p + 5) + 1) *
      ((1 : Q') + qpow (driftRatio k) (4 * p + 5))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) hGu

#print axioms driftSqFactor_increment_twice_le_chord

theorem driftSqFactor_increment_sharp_le (k p : Nat) :
    driftSqFactor k (p + 1) + -(driftSqFactor k p) ≤
      driftSqFactor k p *
        (unit (driftDen k) (driftDen_pos k) *
          ((1 : Q') + Q'.ofNat (4 * p + 5) *
            qpow (driftRatio k) (4 * p + 6))) := by
  have hg := driftRatio_geomSum_sharp_le k (4 * p + 5)
  have hu0 : (0 : Q') ≤ unit (driftDen k) (driftDen_pos k) := unit_nonneg _ _
  have hu := Q'.mul_le_mul_of_nonneg_left _ _
    (unit (driftDen k) (driftDen_pos k)) hg hu0
  have hG0 : (0 : Q') ≤ driftSqFactor k p := by
    unfold driftSqFactor
    exact Q'.mul_nonneg _ _
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (driftSqFactor k p) hu hG0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (driftSqFactor_increment_geom_eqv k p)) hm

def compensatedGeomCell (k L p : Nat) : Q' :=
  (trapezoidNodeCumulative k L + -(trapezoidNodeCumulative k p)) *
    (driftSqFactor k p *
      (unit (driftDen k) (driftDen_pos k) *
        HeatKernelRGStep.geomSum (driftRatio k) (4 * p + 6)))

def compensatedGeomSum (k L : Nat) : Q' :=
  fsum (compensatedGeomCell k L) L

def compensatedChordCell (k L p : Nat) : Q' :=
  (trapezoidNodeCumulative k L + -(trapezoidNodeCumulative k p)) *
    (driftSqFactor k p *
      (unit (driftDen k) (driftDen_pos k) *
        (Q'.ofNat ((4 * p + 5) + 1) *
          ((1 : Q') + qpow (driftRatio k) (4 * p + 5)))))

def compensatedChordSum (k L : Nat) : Q' :=
  fsum (compensatedChordCell k L) L

/-- Exact mode-cell form of the compensated defect.  Unlike the linearized
envelope, this loses no small-scale reserve. -/
theorem compensatedAbelDefect_eq_geomSum (k L : Nat) :
    compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L ≈
      compensatedGeomSum k L := by
  unfold compensatedAbelDefect compensatedGeomSum
  apply CubeRatioBounds.fsum_eqv_congr
  intro p
  unfold compensatedGeomCell
  have hC :
      abelPrefix (trapezoidNodeCoeff k) L +
          -(abelPrefix (trapezoidNodeCoeff k) p) ≈
        trapezoidNodeCumulative k L + -(trapezoidNodeCumulative k p) :=
    Q'.add_eqv_congr'
      (abelPrefix_trapezoidNodeCoeff k L)
      (Q'.neg_eqv_congr _ _ (abelPrefix_trapezoidNodeCoeff k p))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hC) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (driftSqFactor_increment_geom_eqv k p)

/-- The doubled compensated defect is controlled by the symmetric endpoint
envelope whenever the terminal carrier dominates each earlier prefix. -/
theorem compensatedAbelDefect_twice_le_chord (k L : Nat)
    (hgap : ∀ p, p < L →
      (0 : Q') ≤ trapezoidNodeCumulative k L +
        -(trapezoidNodeCumulative k p)) :
    compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L +
        compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L ≤
      compensatedChordSum k L := by
  let f := fun p =>
    (abelPrefix (trapezoidNodeCoeff k) L +
      -(abelPrefix (trapezoidNodeCoeff k) p)) *
        (driftSqFactor k (p + 1) + -(driftSqFactor k p))
  have hsplit := CubeRatioBounds.fsum_add f f L
  have hsum : fsum (fun p => f p + f p) L ≤ compensatedChordSum k L := by
    unfold compensatedChordSum
    apply CubeRatioBounds.fsum_mono_lt
    intro p hp
    let C := trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k p)
    let d := driftSqFactor k (p + 1) + -(driftSqFactor k p)
    have hC : abelPrefix (trapezoidNodeCoeff k) L +
        -(abelPrefix (trapezoidNodeCoeff k) p) ≈ C :=
      Q'.add_eqv_congr'
        (abelPrefix_trapezoidNodeCoeff k L)
        (Q'.neg_eqv_congr _ _ (abelPrefix_trapezoidNodeCoeff k p))
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ C
      (driftSqFactor_increment_twice_le_chord k p) (hgap p hp)
    have hL : f p + f p ≈ C * (d + d) := by
      unfold f d
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _ hC)
          (Q'.mul_eqv_congr_right _ _ _ hC)) ?_
      ring_qeqv
    unfold compensatedChordCell
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) hm
  unfold compensatedAbelDefect
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hsplit)) hsum

#print axioms compensatedAbelDefect_twice_le_chord

def compensatedCellEnvelope (k L p : Nat) : Q' :=
  (trapezoidNodeCumulative k L + -(trapezoidNodeCumulative k p)) *
    (driftSqFactor k p *
      (Q'.ofNat (4 * p + 6) * unit (driftDen k) (driftDen_pos k) *
        qpow (driftRatio k) (4 * p + 6)))

def compensatedEnvelopeSum (k L : Nat) : Q' :=
  fsum (compensatedCellEnvelope k L) L

/-- The exact drift-ratio envelope bounds the compensated Abel defect once
the terminal carrier is known to dominate every earlier carrier. -/
theorem compensatedAbelDefect_le_envelope (k L : Nat)
    (hgap : ∀ p, p < L →
      (0 : Q') ≤ trapezoidNodeCumulative k L +
        -(trapezoidNodeCumulative k p)) :
    compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k) L ≤
      compensatedEnvelopeSum k L := by
  unfold compensatedAbelDefect compensatedEnvelopeSum
  apply CubeRatioBounds.fsum_mono_lt
  intro p hp
  let C := trapezoidNodeCumulative k L + -(trapezoidNodeCumulative k p)
  let d := driftSqFactor k (p + 1) + -(driftSqFactor k p)
  let e := driftSqFactor k p *
    (Q'.ofNat (4 * p + 6) * unit (driftDen k) (driftDen_pos k) *
      qpow (driftRatio k) (4 * p + 6))
  have hC :
      abelPrefix (trapezoidNodeCoeff k) L +
          -(abelPrefix (trapezoidNodeCoeff k) p) ≈ C := by
    exact Q'.add_eqv_congr'
      (abelPrefix_trapezoidNodeCoeff k L)
      (Q'.neg_eqv_congr _ _ (abelPrefix_trapezoidNodeCoeff k p))
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ C
    (driftSqFactor_increment_le k p) (hgap p hp)
  unfold compensatedCellEnvelope
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ d hC)) hm

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

/-- A doubled symmetric-chord budget implies the quantitative reserve.  The
positive factor two is cancelled only after all estimates have been made. -/
theorem compensated_reserve_twentyFourTwentyFive_of_chord (k : Nat)
    (hgap : ∀ p, p < Ncut k - 1 →
      (0 : Q') ≤ trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k p))
    (hchord : compensatedChordSum k (Ncut k - 1) +
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
  let a := compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k)
    (Ncut k - 1) + trapezoidTerminalCorrection k
  let b := Q'.mkPos 24 25 (by decide) *
    (-(trapezoidNodeCumulative k (Ncut k - 1) * driftSqFactor k 0))
  have hdef := compensatedAbelDefect_twice_le_chord k (Ncut k - 1) hgap
  have hadd := Q'.add_le_add hdef
    (Q'.le_refl' (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k))
  have hrearr :
      (compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k)
            (Ncut k - 1) +
          compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k)
            (Ncut k - 1)) +
        (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) ≈
      a + a := by
    unfold a
    ring_qeqv
  have haa : a + a ≤ b + b :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrearr)
      (Q'.le_trans' _ _ _ hadd hchord)
  have htwo : Q'.ofNat 2 * a ≤ Q'.ofNat 2 * b :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv a))
      (Q'.le_trans' _ _ _ haa
        (Q'.ge_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv b)))
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos
    (show (0 : Q') < Q'.ofNat 2 by decide) htwo

#print axioms compensated_reserve_twentyFourTwentyFive_of_chord

/-- A quantitative envelope budget implies the proposed all-scale `24/25`
reserve.  The remaining mathematical target is now an explicit positive-cell
sum with the exact harmonic unit denominator. -/
theorem compensated_reserve_twentyFourTwentyFive_of_envelope (k : Nat)
    (hgap : ∀ p, p < Ncut k - 1 →
      (0 : Q') ≤ trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k p))
    (henv : compensatedEnvelopeSum k (Ncut k - 1) +
          trapezoidTerminalCorrection k ≤
        Q'.mkPos 24 25 (by decide) *
          (-(trapezoidNodeCumulative k (Ncut k - 1) * driftSqFactor k 0))) :
    compensatedAbelDefect (trapezoidNodeCoeff k) (driftSqFactor k)
          (Ncut k - 1) + trapezoidTerminalCorrection k ≤
      Q'.mkPos 24 25 (by decide) *
        (-(trapezoidNodeCumulative k (Ncut k - 1) * driftSqFactor k 0)) := by
  have hdef := compensatedAbelDefect_le_envelope k (Ncut k - 1) hgap
  have hadd := Q'.add_le_add_right _ _ (trapezoidTerminalCorrection k) hdef
  exact Q'.le_trans' _ _ _ hadd henv

/-- The linearized cell envelope is too coarse at the smallest scale even
though the true `24/25` reserve holds there.  It must therefore be paired with
closed small-scale anchors or replaced by the exact geometric cell factor. -/
theorem compensatedEnvelope_twentyFourTwentyFive_fails_k0 :
    not (
      compensatedEnvelopeSum 0 (Ncut 0 - 1) + trapezoidTerminalCorrection 0 ≤
        Q'.mkPos 24 25 (by decide) *
          (-(trapezoidNodeCumulative 0 (Ncut 0 - 1) * driftSqFactor 0 0))) := by
  unfold compensatedEnvelopeSum compensatedCellEnvelope
    trapezoidTerminalCorrection trapezoidNodeCumulative harmonicD harmonicA
    twoInvSq oldAdj coordNormSq adjCorr driftSqFactor driftRatio driftDen
    harmW harmU ReciprocalBernoulliUpper.oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

/-- Carrier-gap positivity cannot be proved by demanding every successor node
coefficient be nonnegative: the first successor coefficient is negative at
`k=3`.  Positive later suffix mass is essential. -/
theorem trapezoidNodeCoeff_nonneg_fails_k3_i1 :
    not ((0 : Q') ≤ trapezoidNodeCoeff 3 1) := by
  unfold trapezoidNodeCoeff harmonicD harmonicA twoInvSq oldAdj oldDiag
    coordNormSq adjCorr harmW harmU ReciprocalBernoulliUpper.oneSub unit
    invSqTerm coeffW dimQ c4 qpow Ncut fsum
  decide

/-- Exact smallest-scale carrier-gap anchor. -/
theorem terminal_carrier_gap_nonneg_k0 {p : Nat} (hp : p < Ncut 0 - 1) :
    (0 : Q') ≤ trapezoidNodeCumulative 0 (Ncut 0 - 1) +
      -(trapezoidNodeCumulative 0 p) := by
  have hp' : p = 0 ∨ p = 1 ∨ p = 2 := by
    unfold Ncut at hp
    omega
  rcases hp' with rfl | rfl | rfl <;>
    unfold trapezoidNodeCumulative harmonicD harmonicA twoInvSq oldAdj
      coordNormSq adjCorr harmW harmU ReciprocalBernoulliUpper.oneSub unit
      invSqTerm coeffW dimQ c4 qpow Ncut fsum <;> decide

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

/-- The nearby uniform strengthening `19/20` is already false at the smallest
scale.  Thus `24/25` is not replaceable by a casual round-number margin. -/
theorem compensated_reserve_nineteenTwentieths_fails_k0 :
    not (
      compensatedAbelDefect (trapezoidNodeCoeff 0) (driftSqFactor 0)
            (Ncut 0 - 1) + trapezoidTerminalCorrection 0 ≤
        Q'.mkPos 19 20 (by decide) *
          (-(trapezoidNodeCumulative 0 (Ncut 0 - 1) * driftSqFactor 0 0))) := by
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
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.oldDiag_mul_driftSq_eqv_next
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.oldAdj_mul_driftAdj_eqv_next
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftRatio_mul_driftDen_eqv
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftRatio_eqv_one_add_unitDen
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.qpow_one_add_growth
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftRatio_qpow_growth
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.qpow_one_add_increment_le
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftSqFactor_increment_le
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.qpow_driftRatio_sub_one_eqv
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftSqFactor_increment_geom_eqv
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.compensatedAbelDefect_eq_geomSum
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.geomSum_succ_le_one_add_last
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftRatio_geomSum_sharp_le
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.driftSqFactor_increment_sharp_le
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.compensatedAbelDefect_le_envelope
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.start_add_forwardIncrementSum
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.finite_abel_compensated
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.trapezoidNode_finite_abel_compensated
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.weightedTrapezoidResidual_eq_compensated
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.compensated_reserve_twentyFourTwentyFive_of_envelope
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.compensatedEnvelope_twentyFourTwentyFive_fails_k0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.trapezoidNodeCoeff_nonneg_fails_k3_i1
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.terminal_carrier_gap_nonneg_k0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.weightedTrapezoidResidual_nonpos_of_reserve
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.compensated_reserve_k0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.compensated_reserve_twentyFourTwentyFive_k0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.compensated_reserve_nineteenTwentieths_fails_k0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.weightedTrapezoidResidual_nonpos_k0
#print axioms YMGap.Continuum.HarmonicWeightedAbelReserve.weightedTrapezoidResidual_eq_energy
