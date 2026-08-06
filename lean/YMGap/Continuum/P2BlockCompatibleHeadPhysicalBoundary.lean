/-
Track 11.7-fusion / R3k -- physical endpoint payment for the retuned
Dirichlet head.

This module keeps the all-scale proof symbolic.  It combines the exact
endpoint identity `3*A_N=N(N+1)(N+2)`, the factor-two retune law, and the
constant-cost endpoint floor.  The remaining arithmetic is a polynomial
comparison at the first open cutoff, propagated by the exact physical
schedule.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleHeadPhysicalFloor
import YMGap.Continuum.P2BlockCompatibleHeadDirichletCompiler
import YMGap.Continuum.EndpointCutoffTailFormula
import YMGap.Continuum.FusedNextScaleRetune
import YMGap.Continuum.HarmonicSymbolicAnchorRatio
import YMGap.Continuum.R1CornerAtoms
import YMGap.Continuum.ReciprocalBernoulliUpper

namespace YMGap.Continuum.P2BlockCompatibleHeadPhysicalBoundary

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.EndpointCutoffTailFormula
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.FusedNextScaleRetune
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.P2BlockCompatibleHeadDirichletCompiler
open YMGap.Continuum.P2BlockCompatibleHeadPhysicalFloor
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.R1CornerAtoms
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private def q2 : Q' := Q'.ofNat 2
private def q3 : Q' := Q'.ofNat 3
private def q5 : Q' := Q'.ofNat 5
private def q6 : Q' := Q'.ofNat 6

/-- The weighted adjacent correlation is bounded by its unweighted endpoint. -/
theorem adjCorr_le_endpoint {w : Q'} (hw0 : (0 : Q') <= w)
    (hw1 : w <= (1 : Q')) (N : Nat) :
    adjCorr w N <= adjCorr (1 : Q') N := by
  unfold adjCorr
  exact fsum_le_fsum' (fun i =>
    Q'.mul_le_mul_of_nonneg
      (coeffW_mono_w hw0 hw1 i)
      (coeffW_mono_w hw0 hw1 (i + 1))
      (coeffW_nonneg (by decide) i)
      (coeffW_nonneg hw0 (i + 1))) N

/-- Five retuned powers lose at most five halves of the original margin. -/
theorem twice_retuned_fifth_defect_le {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) :
    q2 * ((1 : Q') - qpow (p2RetunedWeight w) 5) <=
      q5 * ((1 : Q') - w) := by
  let q := p2RetunedWeight w
  have hdef := HeatKernelRGStep.oneSub_qpow_le
    (p2RetunedWeight_nonneg hw0) (p2RetunedWeight_le_one hw1) 5
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ q2 hdef (by decide)
  have hmargin : q2 * ((1 : Q') - q) ≈ (1 : Q') - w := by
    dsimp only [q]
    simpa only [p2RetunedWeight] using twice_retuned_base_margin w
  have hre :
      q2 * (Q'.ofNat 5 * ((1 : Q') - q)) ≈
        q5 * (q2 * ((1 : Q') - q)) := by
    unfold q2 q5
    ring_qeqv
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hre
      (Q'.mul_eqv_congr_left q5 _ _ hmargin)))

/-- Generic sharp cubic cap for the retune debt. -/
theorem headRetuneDebt_le_cubic {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (N : Nat) :
    headRetuneDebt w N <=
      q5 * (((1 : Q') - w) *
        (Q'.ofNat N * (Q'.ofNat N + 1) * (Q'.ofNat N + 2))) := by
  let defect := (1 : Q') + -qpow (p2RetunedWeight w) 5
  let A := adjCorr w N
  let A1 := adjCorr (1 : Q') N
  let margin := (1 : Q') - w
  let P := Q'.ofNat N * (Q'.ofNat N + 1) * (Q'.ofNat N + 2)
  have hdef0 : (0 : Q') <= defect :=
    Q'.sub_nonneg_of_le (HeatKernelGap.qpow_le_one
      (p2RetunedWeight_nonneg hw0) (p2RetunedWeight_le_one hw1) 5)
  have hA0 : (0 : Q') <= A := adjCorr_nonneg hw0 N
  have hA10 : (0 : Q') <= A1 := adjCorr_nonneg (by decide) N
  have hmargin0 : (0 : Q') <= margin := Q'.sub_nonneg_of_le hw1
  have hA : A <= A1 := adjCorr_le_endpoint hw0 hw1 N
  have hdef : q2 * defect <= q5 * margin := by
    dsimp only [defect, margin]
    exact twice_retuned_fifth_defect_le hw0 hw1
  have hprod : (q2 * defect) * A <= (q5 * margin) * A1 :=
    Q'.mul_le_mul_of_nonneg hdef hA
      (Q'.mul_nonneg _ _ (by decide) hmargin0) hA0
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ q3 hprod (by decide)
  have hendpoint : q3 * A1 ≈ P := by
    dsimp only [A1, P]
    exact adjCorr_endpoint_closed N
  have hleft : q3 * ((q2 * defect) * A) ≈ headRetuneDebt w N := by
    dsimp only [defect, A]
    unfold headRetuneDebt
    let d := (1 : Q') + -qpow (p2RetunedWeight w) 5
    let B := adjCorr w N
    have hconst : q3 * q2 ≈ q6 := by decide
    refine Q'.eqv_trans _ ((q3 * (q2 * d)) * B) _ ?_ ?_
    · exact Q'.eqv_symm (Q'.mul_assoc_eqv q3 (q2 * d) B)
    · refine Q'.eqv_trans _ (((q3 * q2) * d) * B) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ B
          (Q'.eqv_symm (Q'.mul_assoc_eqv q3 q2 d))
      · refine Q'.eqv_trans _ ((q3 * q2) * (d * B)) _
          (Q'.mul_assoc_eqv (q3 * q2) d B) ?_
        exact Q'.mul_eqv_congr_right _ _ _ hconst
  have hright : q3 * ((q5 * margin) * A1) ≈ q5 * (margin * P) := by
    refine Q'.eqv_trans _ (q5 * (margin * (q3 * A1))) _ ?_ ?_
    · unfold q3 q5
      ring_qeqv
    · exact Q'.mul_eqv_congr_left q5 _ _
        (Q'.mul_eqv_congr_left margin _ _ hendpoint)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hright))

/-- First open physical cutoff in the all-scale head campaign. -/
theorem blockNcut_ge_1279 (r : Nat) :
    1279 <= blockNcut (r + 8) := by
  have hpow : 2 ^ 8 <= 2 ^ (r + 8) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hclosed := blockNcut_closed (r + 8)
  have hscaled : 5 * 2 ^ 8 <= 5 * 2 ^ (r + 8) :=
    Nat.mul_le_mul_left 5 hpow
  have hbase : 5 * 2 ^ 8 = 1280 := by decide
  rw [hbase] at hscaled
  omega

/-- Cleared polynomial comparison which makes the cubic retune debt fit
inside the squared endpoint floor from scale eight onward. -/
theorem physical_cubic_cleared (r : Nat) :
    405 * blockNcut (r + 8) * (blockNcut (r + 8) + 1) *
        (blockNcut (r + 8) + 2) <=
      physicalWeightDen (r + 8) * blockNcut (r + 8) *
        blockNcut (r + 8) := by
  let N := blockNcut (r + 8)
  let D := physicalWeightDen (r + 8)
  have hN : 1279 <= N := blockNcut_ge_1279 r
  have hcoef : 10125 <= 8 * N := by omega
  have hmul := Nat.mul_le_mul_right (N + 2) hcoef
  have hshape : 8 * N * (N + 2) <= 12 * (N + 1) * N := by
    have hlinear : 8 * (N + 2) <= 12 * (N + 1) := by omega
    have h := Nat.mul_le_mul_right N hlinear
    calc
      8 * N * (N + 2) = 8 * (N + 2) * N := by ac_rfl
      _ <= 12 * (N + 1) * N := h
  have hcore : 10125 * (N + 2) <= 12 * (N + 1) * N :=
    Nat.le_trans hmul hshape
  have hfactor := Nat.mul_le_mul_left (N * (N + 1)) hcore
  have hcoord := physicalWeightDen_cutoff_square (r + 8)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  change 405 * N * (N + 1) * (N + 2) <= D * N * N
  have hscaled :
      25 * (405 * N * (N + 1) * (N + 2)) <=
        25 * (D * N * N) := by
    calc
      _ = (N * (N + 1)) * (10125 * (N + 2)) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]
        rw [← Nat.mul_assoc, show 25 * 405 = 10125 by decide]
      _ <= (N * (N + 1)) * (12 * (N + 1) * N) := hfactor
      _ = (25 * D) * (N * N) := by
        rw [hcoord]
        simp only [Nat.mul_comm, Nat.mul_left_comm]
      _ = _ := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

private theorem cubic_fraction_le_ninth_sq (N D : Nat) (hD : 0 < D)
    (hcleared : 405 * N * (N + 1) * (N + 2) <= D * N * N) :
    q5 * (Q'.mkPos 1 D hD *
        (Q'.ofNat N * Q'.ofNat (N + 1) * Q'.ofNat (N + 2))) <=
      (Q'.ofNat N * Q'.mkPos 1 9 (by decide)) *
        (Q'.ofNat N * Q'.mkPos 1 9 (by decide)) := by
  show
    (q5 * (Q'.mkPos 1 D hD *
      (Q'.ofNat N * Q'.ofNat (N + 1) * Q'.ofNat (N + 2)))).num *
        (((Q'.ofNat N * Q'.mkPos 1 9 (by decide)) *
          (Q'.ofNat N * Q'.mkPos 1 9 (by decide))).den : Int) <=
      ((Q'.ofNat N * Q'.mkPos 1 9 (by decide)) *
        (Q'.ofNat N * Q'.mkPos 1 9 (by decide))).num *
        ((q5 * (Q'.mkPos 1 D hD *
          (Q'.ofNat N * Q'.ofNat (N + 1) * Q'.ofNat (N + 2)))).den : Int)
  unfold q5
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.one_mul, Int.mul_one]
  push_cast
  have hcleared' :
      5 * (N * (N + 1) * (N + 1 + 1)) * 81 <= N * N * D := by
    simpa only [Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hcleared
  exact_mod_cast hcleared'

/-- The sharp cubic debt cap lies below the explicit endpoint square floor. -/
theorem physical_cubic_cap_le_endpoint_floor (r : Nat) :
    q5 * (((1 : Q') - blockWeight (r + 8)) *
        (Q'.ofNat (blockNcut (r + 8)) *
          (Q'.ofNat (blockNcut (r + 8)) + 1) *
          (Q'.ofNat (blockNcut (r + 8)) + 2))) <=
      (Q'.ofNat (blockNcut (r + 8)) * Q'.mkPos 1 9 (by decide)) *
        (Q'.ofNat (blockNcut (r + 8)) * Q'.mkPos 1 9 (by decide)) := by
  let N := blockNcut (r + 8)
  let D := physicalWeightDen (r + 8)
  have hmargin := one_sub_blockWeight_eqv_margin (r + 8)
  have hclosed := blockMargin_eqv_closed (r + 8)
  have hmarginClosed :
      ((1 : Q') - blockWeight (r + 8)) ≈
        Q'.mkPos 1 D (physicalWeightDen_pos (r + 8)) :=
    Q'.eqv_trans _ _ _ hmargin hclosed
  have hP :
      Q'.ofNat N * (Q'.ofNat N + 1) * (Q'.ofNat N + 2) ≈
        Q'.ofNat N * Q'.ofNat (N + 1) * Q'.ofNat (N + 2) := by
    have h1 : Q'.ofNat N + (1 : Q') ≈ Q'.ofNat (N + 1) := by
      exact Q'.eqv_symm (BulkModeCrux.ofNat_succ_eqv N)
    have h2 : Q'.ofNat N + (2 : Q') ≈ Q'.ofNat (N + 2) := by
      exact Q'.eqv_symm (Q'.ofNat_add_eqv N 2)
    refine Q'.eqv_trans _
      ((Q'.ofNat N * Q'.ofNat (N + 1)) * (Q'.ofNat N + 2)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat N) _ _ h1)
    · exact Q'.mul_eqv_congr_left _ _ _ h2
  have hre :
      q5 * (((1 : Q') - blockWeight (r + 8)) *
        (Q'.ofNat N * (Q'.ofNat N + 1) * (Q'.ofNat N + 2))) ≈
      q5 * (Q'.mkPos 1 D (physicalWeightDen_pos (r + 8)) *
        (Q'.ofNat N * Q'.ofNat (N + 1) * Q'.ofNat (N + 2))) := by
    refine Q'.mul_eqv_congr_left q5 _ _ ?_
    refine Q'.eqv_trans _
      (Q'.mkPos 1 D (physicalWeightDen_pos (r + 8)) *
        (Q'.ofNat N * (Q'.ofNat N + 1) * (Q'.ofNat N + 2))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hmarginClosed
    · exact Q'.mul_eqv_congr_left _ _ _ hP
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) ?_
  exact cubic_fraction_le_ninth_sq N D (physicalWeightDen_pos (r + 8))
    (physical_cubic_cleared r)

/-- The physical reciprocal margin is strong enough to force the final
coefficient ratio below one. -/
theorem physical_margin_cleared (r : Nat) :
    physicalWeightDen (r + 8) <=
      blockNcut (r + 8) * (2 * blockNcut (r + 8) + 1) := by
  let N := blockNcut (r + 8)
  let D := physicalWeightDen (r + 8)
  have hN : 2 <= N := Nat.le_trans (by decide) (blockNcut_ge_1279 r)
  have hcoord := physicalWeightDen_cutoff_square (r + 8)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have h1225 : (12 : Nat) <= 25 := by decide
  have hscaled : 25 * D <= 25 * ((N + 1) * (N + 1)) := by
    calc
      25 * D = 12 * (N + 1) * (N + 1) := hcoord
      _ = 12 * ((N + 1) * (N + 1)) := by ac_rfl
      _ <= 25 * ((N + 1) * (N + 1)) :=
        Nat.mul_le_mul_right ((N + 1) * (N + 1)) h1225
  have hD : D <= (N + 1) * (N + 1) :=
    Nat.le_of_mul_le_mul_left hscaled (by decide)
  have hsmall : N + 1 <= N * N := by
    have htwice : 2 * N <= N * N := Nat.mul_le_mul_right N hN
    exact Nat.le_trans (by omega) htwice
  have hsquare : (N + 1) * (N + 1) <= N * (2 * N + 1) := by
    have hadd := Nat.add_le_add_left hsmall (N * (N + 1))
    calc
      (N + 1) * (N + 1) = N * (N + 1) + (N + 1) := by
        rw [Nat.add_mul]
        simp
      _ <= N * (N + 1) + N * N := hadd
      _ = N * (2 * N + 1) := by
        simp only [Nat.mul_add, Nat.mul_one, Nat.two_mul]
        ac_rfl
  exact Nat.le_trans hD hsquare

private theorem bernDen_step_cover (N n D : Nat) (hD : 0 < D)
    (hcleared : D <= N * n) :
    Q'.ofNat (N + 1) <=
      Q'.ofNat N * bernDen (Q'.mkPos 1 D hD) n := by
  show (Q'.ofNat (N + 1)).num *
      ((Q'.ofNat N * bernDen (Q'.mkPos 1 D hD) n).den : Int) <=
    (Q'.ofNat N * bernDen (Q'.mkPos 1 D hD) n).num *
      (Q'.ofNat (N + 1)).den
  unfold bernDen
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.add_num_cast, Q'.add_den_cast, Q'.mkPos_num,
    Q'.mkPos_den, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.one_mul, Int.mul_one]
  push_cast
  have htarget : (N + 1) * D <= N * (D + n) := by
    have hadd := Nat.add_le_add_left hcleared (N * D)
    calc
      (N + 1) * D = N * D + D := by
        rw [Nat.add_mul]
        simp
      _ <= N * D + N * n := hadd
      _ = N * (D + n) := by rw [Nat.mul_add]
  exact_mod_cast htarget

/-- Reciprocal Bernoulli plus the physical cutoff coordinate makes the final
dimension growth lose to the heat power. -/
theorem physical_terminal_cross (r : Nat) :
    let N := blockNcut (r + 8)
    Q'.ofNat (N + 1) * qpow (blockWeight (r + 8)) (2 * N + 1) <=
      (1 : Q') * Q'.ofNat N := by
  let k := r + 8
  let N := blockNcut k
  let D := physicalWeightDen k
  let u := blockMargin k
  let n := 2 * N + 1
  have hu0 : (0 : Q') <= u := blockMargin_nonneg k
  have hu1 : u <= (1 : Q') := blockMargin_le_one k
  have hw0 : (0 : Q') <= blockWeight k := blockWeight_nonneg k
  have hclosed : u ≈ Q'.mkPos 1 D (physicalWeightDen_pos k) := by
    simpa only [u, D] using blockMargin_eqv_closed k
  have hden :
      bernDen u n ≈ bernDen (Q'.mkPos 1 D (physicalWeightDen_pos k)) n := by
    unfold bernDen
    exact Q'.add_eqv_congr_left 1 _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hclosed)
  have hcoverClosed :
      Q'.ofNat (N + 1) <=
        Q'.ofNat N * bernDen (Q'.mkPos 1 D (physicalWeightDen_pos k)) n := by
    apply bernDen_step_cover
    simpa only [k, N, D, n] using physical_margin_cleared r
  have hcover : Q'.ofNat (N + 1) <= Q'.ofNat N * bernDen u n :=
    Q'.le_trans' _ _ _ hcoverClosed
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat N) _ _ hden))
  have hbern :
      qpow (blockWeight k) n * bernDen u n <= (1 : Q') := by
    have h := oneSub_pow_mul_bernDen_le hu0 hu1 n
    have hweight : blockWeight k = oneSub u := rfl
    simpa only [hweight] using h
  have hcoverScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow (blockWeight k) n) hcover (qpow_nonneg _ hw0 n)
  have hbernScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat N) hbern (zero_le_ofNat N)
  have hleft :
      qpow (blockWeight k) n * Q'.ofNat (N + 1) ≈
        Q'.ofNat (N + 1) * qpow (blockWeight k) n :=
    Q'.mul_comm_eqv _ _
  have hmiddle :
      qpow (blockWeight k) n * (Q'.ofNat N * bernDen u n) ≈
        Q'.ofNat N * (qpow (blockWeight k) n * bernDen u n) := by
    ring_qeqv
  have hright : Q'.ofNat N * (1 : Q') ≈ (1 : Q') * Q'.ofNat N :=
    Q'.mul_comm_eqv _ _
  dsimp only [k, N, n] at hleft hmiddle hright hcoverScaled hbernScaled ⊢
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hcoverScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle)
        (Q'.le_trans' _ _ _ hbernScaled (Q'.le_of_eqv hright))))

/-- The physical coefficient string is descending across its final edge. -/
theorem physical_terminal_coeff_descending (r : Nat) :
    coeffW (blockWeight (r + 8)) (blockNcut (r + 8)) <=
      coeffW (blockWeight (r + 8)) (blockNcut (r + 8) - 1) := by
  let N := blockNcut (r + 8)
  have hN : 2 <= N := Nat.le_trans (by decide) (blockNcut_ge_1279 r)
  have hcross := physical_terminal_cross r
  have hs := coeffW_succ_le_of_cross
    (w := blockWeight (r + 8)) (R := (1 : Q')) (N - 1)
    (blockWeight_nonneg (r + 8)) (by
      simpa only [show N - 1 + 2 = N + 1 by omega,
        show 2 * (N - 1) + 3 = 2 * N + 1 by omega,
        show N - 1 + 1 = N by omega] using hcross)
  have hs' :
      coeffW (blockWeight (r + 8)) N <=
        (1 : Q') * coeffW (blockWeight (r + 8)) (N - 1) := by
    simpa only [show N - 1 + 1 = N by omega] using hs
  exact Q'.le_trans' _ _ _ hs'
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

private theorem boundary_rearrange (A B P Z : Q') :
    (P + (P + -Z)) + (A + B) ≈ A + B + q2 * P + -Z := by
  have hreorder :
      (P + (P + -Z)) + (A + B) ≈ A + B + (P + P) + -Z := by
    ring_qeqv
  have hq2 : q2 ≈ (1 : Q') + 1 := by
    unfold q2
    decide
  have hdoubleForward : q2 * P ≈ P + P := by
    refine Q'.eqv_trans _ (((1 : Q') + 1) * P) _
      (Q'.mul_eqv_congr_right _ _ P hq2) ?_
    refine Q'.eqv_trans _ ((1 : Q') * P + (1 : Q') * P) _
      (Q'.add_mul_eqv 1 1 P) ?_
    exact Q'.add_eqv_congr' (Q'.one_mul_eqv P) (Q'.one_mul_eqv P)
  have hreplace : A + B + (P + P) + -Z ≈ A + B + q2 * P + -Z :=
    Q'.add_eqv_congr_right _ _ (-Z)
      (Q'.add_eqv_congr_left (A + B) _ _ (Q'.eqv_symm hdoubleForward))
  exact Q'.eqv_trans _ _ _ hreorder hreplace

/-- The explicit boundary dominates the penultimate coefficient square. -/
theorem physical_endpoint_sq_le_headBoundary (r : Nat) :
    let w := blockWeight (r + 8)
    let N := blockNcut (r + 8)
    coeffW w (N - 1) * coeffW w (N - 1) <= headBoundary w N := by
  let w := blockWeight (r + 8)
  let N := blockNcut (r + 8)
  let c0 := coeffW w 0
  let c1 := coeffW w 1
  let cp := coeffW w (N - 1)
  let cn := coeffW w N
  have hw0 : (0 : Q') <= w := blockWeight_nonneg (r + 8)
  have hcp0 : (0 : Q') <= cp := coeffW_nonneg hw0 (N - 1)
  have hcn0 : (0 : Q') <= cn := coeffW_nonneg hw0 N
  have hdesc : cn <= cp := by
    simpa only [w, N, cn, cp] using physical_terminal_coeff_descending r
  have hsq : cn * cn <= cp * cp :=
    Q'.mul_le_mul_of_nonneg hdesc hdesc hcp0 hcn0
  have hz : (0 : Q') <= cp * cp + -(cn * cn) :=
    Q'.sub_nonneg_of_le hsq
  have hc00 : (0 : Q') <= c0 * c0 :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 0) (coeffW_nonneg hw0 0)
  have hc10 : (0 : Q') <= q2 * (c1 * c1) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 1) (coeffW_nonneg hw0 1))
  have hab0 : (0 : Q') <= c0 * c0 + q2 * (c1 * c1) :=
    Q'.le_trans' _ ((0 : Q') + 0) _ (by decide)
      (Q'.add_le_add hc00 hc10)
  have h1 := Q'.add_le_self_of_nonneg (cp * cp) _ hz
  have h2 := Q'.add_le_self_of_nonneg (cp * cp + (cp * cp + -(cn * cn))) _ hab0
  have hre :
      (cp * cp + (cp * cp + -(cn * cn))) +
          (c0 * c0 + q2 * (c1 * c1)) ≈ headBoundary w N := by
    change
      (cp * cp + (cp * cp + -(cn * cn))) +
          (c0 * c0 + q2 * (c1 * c1)) ≈
        c0 * c0 + q2 * (c1 * c1) + q2 * (cp * cp) + -(cn * cn)
    exact boundary_rearrange _ _ _ _
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hre))

/-- The retune debt is paid by the genuine physical head boundary at every
open scale `k = r+8`. -/
theorem physical_head_boundary (r : Nat) :
    headRetuneDebt (blockWeight (r + 8)) (blockNcut (r + 8)) <=
      headBoundary (blockWeight (r + 8)) (blockNcut (r + 8)) := by
  have hdebt := headRetuneDebt_le_cubic
    (blockWeight_nonneg (r + 8)) (blockWeight_le_one (r + 8))
    (blockNcut (r + 8))
  have hcap := physical_cubic_cap_le_endpoint_floor r
  have hfloor :
      (Q'.ofNat (blockNcut (r + 8)) * Q'.mkPos 1 9 (by decide)) *
          (Q'.ofNat (blockNcut (r + 8)) * Q'.mkPos 1 9 (by decide)) <=
        coeffW (blockWeight (r + 8)) (blockNcut (r + 8) - 1) *
          coeffW (blockWeight (r + 8)) (blockNcut (r + 8) - 1) := by
    simpa only [show r + 7 + 1 = r + 8 by omega] using
      physical_endpoint_coeff_sq_floor (r + 7)
  have hboundary := physical_endpoint_sq_le_headBoundary r
  exact Q'.le_trans' _ _ _ hdebt
    (Q'.le_trans' _ _ _ hcap
      (Q'.le_trans' _ _ _ hfloor hboundary))

#print axioms twice_retuned_fifth_defect_le
#print axioms headRetuneDebt_le_cubic
#print axioms physical_cubic_cleared
#print axioms physical_cubic_cap_le_endpoint_floor
#print axioms physical_margin_cleared
#print axioms physical_terminal_cross
#print axioms physical_terminal_coeff_descending
#print axioms physical_endpoint_sq_le_headBoundary
#print axioms physical_head_boundary

end YMGap.Continuum.P2BlockCompatibleHeadPhysicalBoundary
