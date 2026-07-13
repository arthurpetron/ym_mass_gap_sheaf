/-
# Exact fence for the proposed node-one quadratic boundary

The node-one premise suggested by the two-seed quadratic-cap reduction is not
uniform in the harmonic scale.  This module proves an exact counterexample at
`k = 551` without reducing the full `Ncut 551 = 553^2` character sum.  A
62-coordinate exact head and PF2 tail transport give a sharp global adjacent
ratio; an exact prefix gives the needed diagonal lower bound; and a monotone
far tail controls the terminal coefficient.
-/

import YMGap.Continuum.HarmonicCarrierGapK17Fence
import YMGap.Continuum.HarmonicDABoundTransport
import YMGap.Continuum.HarmonicSymbolicAnchorRatio
import YMGap.Continuum.HarmonicThetaPascalClosure

namespace YMGap.Continuum.HarmonicQuadraticBoundaryAll

set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.HarmonicCarrierGapK17Fence
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicHalfEdgeDominance
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.HarmonicThetaPascalClosure
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem rate_reassoc (r x y : Q') :
    (r * x) * y ≈ x * (r * y) := by
  ring_qeqv

private theorem square_reassoc (r x : Q') :
    x * (r * x) ≈ r * (x * x) := by
  ring_qeqv

private theorem square_rate_collect (r x : Q') :
    (r * x) * (r * x) ≈ (r * r) * (x * x) := by
  ring_qeqv

/-- A sharp rational upper rate for `A_551 / D_551`. -/
def rate551 : Q' := Q'.mkPos 124661 125000 (by decide)

private def c551 (i : Nat) : Q' := coeffW (harmW 551) i

/-- The exact 62-coordinate head lies below the sharp rational rate. -/
theorem head_ratio551 :
    adjCorr (harmW 551) 62 ≤ rate551 * coordNormSq (harmW 551) 61 := by
  unfold rate551 harmW harmU oneSub unit adjCorr coordNormSq coeffW dimQ c4
    qpow fsum
  decide

/-- The first coefficient beyond that head lies below the same rate. -/
theorem tail_ratio551 : c551 62 ≤ rate551 * c551 61 := by
  unfold c551
  apply coeffW_succ_le_of_cross 61 (harmW_nonneg 551)
  unfold rate551 harmW harmU oneSub unit qpow
  decide

/-- PF2 propagates the head rate through every later coefficient. -/
theorem tail_step551 {a : Nat} (ha : 61 ≤ a) :
    c551 (a + 1) ≤ rate551 * c551 a := by
  by_cases heq : a = 61
  · subst a
    exact tail_ratio551
  · have hlt : 61 < a := Nat.lt_of_le_of_ne ha (Ne.symm heq)
    have hinj := shifted_ratio_injection
      (harmW_nonneg 551) (harmW_le_one 551) (harmW_pos 551)
      (a := 61) (N := a) hlt
    have hca0 := coeffW_nonneg (harmW_nonneg 551) a
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _ (c551 a)
      tail_ratio551 hca0
    have hreassoc : (rate551 * c551 61) * c551 a ≈
        c551 61 * (rate551 * c551 a) :=
      rate_reassoc rate551 (c551 61) (c551 a)
    have hchain : c551 61 * c551 (a + 1) ≤
        c551 61 * (rate551 * c551 a) := by
      exact Q'.le_trans' _ _ _ hinj
        (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hreassoc))
    exact Q'.le_of_mul_le_mul_left hchain
      (FusionResidualBound.coeffW_pos (harmW_pos 551) 61)

private def edgeTail551 (j : Nat) : Q' :=
  c551 (62 + j) * c551 (62 + j + 1)

private def squareTail551 (j : Nat) : Q' :=
  c551 (62 + j) * c551 (62 + j)

private theorem tail_sum551 (M : Nat) :
    fsum edgeTail551 M ≤ rate551 * fsum squareTail551 M := by
  have ht : ∀ j, edgeTail551 j ≤ rate551 * squareTail551 j := by
    intro j
    unfold edgeTail551 squareTail551
    have hs := tail_step551 (a := 62 + j) (by omega)
    have hc0 := coeffW_nonneg (harmW_nonneg 551) (62 + j)
    have hreassoc : c551 (62 + j) *
          (rate551 * c551 (62 + j)) ≈
        rate551 * (c551 (62 + j) * c551 (62 + j)) :=
      square_reassoc rate551 (c551 (62 + j))
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hs hc0)
      (Q'.le_of_eqv hreassoc)
  have hsum := CubeRatioBounds.fsum_mono_lt M (fun j _ => ht j)
  have hpull := CubeRatioBounds.fsum_const_mul rate551 squareTail551 M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hpull)

/-- Every longer cutoff retains the exact global ratio. -/
theorem global_ratio551 (M : Nat) :
    adjCorr (harmW 551) (62 + M) ≤
      rate551 * coordNormSq (harmW 551) (62 + M) := by
  have hA : adjCorr (harmW 551) (62 + M) ≈
      adjCorr (harmW 551) 62 + fsum edgeTail551 M := by
    unfold adjCorr edgeTail551 c551
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW (harmW 551) a * coeffW (harmW 551) (a + 1)) 62 M
  have hD : coordNormSq (harmW 551) (62 + M) ≈
      coordNormSq (harmW 551) 61 + fsum squareTail551 (M + 1) := by
    unfold coordNormSq squareTail551 c551
    rw [show 62 + M + 1 = 62 + (M + 1) by omega]
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW (harmW 551) a * coeffW (harmW 551) a) 62 (M + 1)
  have hs0 : ∀ j, (0 : Q') ≤ squareTail551 j := by
    intro j
    unfold squareTail551 c551
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg 551) (62 + j))
      (coeffW_nonneg (harmW_nonneg 551) (62 + j))
  have htail : fsum squareTail551 M ≤ fsum squareTail551 (M + 1) :=
    AFRateCalibration.fsum_le_of_le hs0 (by omega)
  have hprefix : coordNormSq (harmW 551) 61 + fsum squareTail551 M ≤
      coordNormSq (harmW 551) (62 + M) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left (coordNormSq (harmW 551) 61) _ _ htail)
      (Q'.ge_of_eqv hD)
  have hpaid := Q'.add_le_add head_ratio551 (tail_sum551 M)
  have hcollect : rate551 * coordNormSq (harmW 551) 61 +
      rate551 * fsum squareTail551 M ≈
      rate551 * (coordNormSq (harmW 551) 61 + fsum squareTail551 M) :=
    Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
    (Q'.le_trans' _ _ _ hpaid
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
        (Q'.mul_le_mul_of_nonneg_left _ _ rate551 hprefix (by decide))))

theorem harmonicA_le_rate551_D :
    harmonicA 551 ≤ rate551 * harmonicD 551 := by
  have h62 : 62 ≤ Ncut 551 := by unfold Ncut; omega
  have h := global_ratio551 (Ncut 551 - 62)
  have heq : 62 + (Ncut 551 - 62) = Ncut 551 := Nat.add_sub_of_le h62
  rw [heq] at h
  simpa [harmonicA, harmonicD] using h

/-- A finite exact prefix supplies a sufficiently sharp diagonal lower bound. -/
theorem D551_lower : Q'.mkPos 51048 25 (by decide) ≤ harmonicD 551 := by
  have hp : Q'.mkPos 51048 25 (by decide) ≤
      coordNormSq (harmW 551) 61 := by
    unfold coordNormSq harmW harmU oneSub unit coeffW dimQ c4 qpow fsum
    decide
  have hmono : coordNormSq (harmW 551) 61 ≤ harmonicD 551 := by
    unfold coordNormSq harmonicD
    apply AFRateCalibration.fsum_le_of_le
    · intro i
      exact Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg 551) i)
        (coeffW_nonneg (harmW_nonneg 551) i)
    · unfold Ncut
      omega
  exact Q'.le_trans' _ _ _ hp hmono

private theorem gap_sub_succ (x y z q : Q') (hz : z ≈ y + q) :
    x + (-z) ≈ (x + (-y)) + (-q) := by
  refine Q'.eqv_trans _ (x + (-(y + q))) _
    (Q'.add_eqv_congr_left x _ _ (Q'.neg_eqv_congr _ _ hz)) ?_
  ring_qeqv

private theorem node_one_slack_algebra
    (B D lam e0 e1 eL d0 d1 dN : Q') :
    (((B * d0 + B * dN) + -(D * (e0 + eL)) +
        -((lam + lam) * (D * D))) +
      -(D * (e0 + e1) + -(B * d1))) ≈
      (((B * d0 + B * d1) + B * dN) +
        -(D * (((e0 + e0) + e1) + eL)) +
        -((lam + lam) * (D * D))) := by
  ring_qeqv

/-- The boundary after deleting node zero has one extra positive diagonal and
one extra pair of negative adjacent edges.  This is the exact all-scale
endpoint identity used by the counterexample below. -/
theorem carrier_node_one_gap_eq_slack (k : Nat) :
    let N := Ncut k
    let L := N - 1
    let D := harmonicD k
    let A := harmonicA k
    let lam := twoInvSq k
    let B := (A + lam * D) + (A + lam * D)
    trapezoidNodeCumulative k L + -(trapezoidNodeCumulative k 1) ≈
      ((B * oldDiag k 0 + B * oldDiag k 1) + B * oldDiag k N) +
        -(D * (((oldAdj k 0 + oldAdj k 0) + oldAdj k 1) + oldAdj k L)) +
        -((lam + lam) * (D * D)) := by
  dsimp only
  let N := Ncut k
  let L := N - 1
  let D := harmonicD k
  let A := harmonicA k
  let lam := twoInvSq k
  let B := (A + lam * D) + (A + lam * D)
  have hs := trapezoidNodeCumulative_succ_eq k 0
  have hsplit := gap_sub_succ
    (trapezoidNodeCumulative k L)
    (trapezoidNodeCumulative k 0)
    (trapezoidNodeCumulative k 1)
    (trapezoidNodeCoeff k 1) hs
  have htotal := carrier_total_gap_eq_slack k
  have hreplace :
      (trapezoidNodeCumulative k L +
          -(trapezoidNodeCumulative k 0)) +
          -(trapezoidNodeCoeff k 1) ≈
        (((B * oldDiag k 0 + B * oldDiag k N) +
          -(D * (oldAdj k 0 + oldAdj k L)) +
          -((lam + lam) * (D * D))) +
          -(trapezoidNodeCoeff k 1)) :=
    Q'.add_eqv_congr_right _ _ _ htotal
  refine Q'.eqv_trans _ _ _ hsplit
    (Q'.eqv_trans _ _ _ hreplace ?_)
  unfold trapezoidNodeCoeff
  exact node_one_slack_algebra B D lam
    (oldAdj k 0) (oldAdj k 1) (oldAdj k L)
    (oldDiag k 0) (oldDiag k 1) (oldDiag k N)

private theorem node_two_slack_algebra
    (B D lam e0 e1 e2 eL d0 d1 d2 dN : Q') :
    ((B * d0 + B * d1) + B * dN) +
      -(D * (((e0 + e0) + e1) + eL)) +
      -((lam + lam) * (D * D)) +
      -(D * (e1 + e2) + -(B * d2)) ≈
    (((B * d0 + B * d1) + B * d2) + B * dN) +
      -(D * ((((e0 + e0) + (e1 + e1)) + e2) + eL)) +
      -((lam + lam) * (D * D)) := by
  ring_qeqv

/-- Exact all-scale endpoint identity after deleting nodes zero and one. -/
theorem carrier_node_two_gap_eq_slack (k : Nat) :
    let N := Ncut k
    let L := N - 1
    let D := harmonicD k
    let A := harmonicA k
    let lam := twoInvSq k
    let B := (A + lam * D) + (A + lam * D)
    trapezoidNodeCumulative k L + -(trapezoidNodeCumulative k 2) ≈
      (((B * oldDiag k 0 + B * oldDiag k 1) + B * oldDiag k 2) +
        B * oldDiag k N) +
        -(D * ((((oldAdj k 0 + oldAdj k 0) +
          (oldAdj k 1 + oldAdj k 1)) + oldAdj k 2) + oldAdj k L)) +
        -((lam + lam) * (D * D)) := by
  dsimp only
  let N := Ncut k
  let L := N - 1
  let D := harmonicD k
  let A := harmonicA k
  let lam := twoInvSq k
  let B := (A + lam * D) + (A + lam * D)
  have hs := trapezoidNodeCumulative_succ_eq k 1
  have hsplit := gap_sub_succ
    (trapezoidNodeCumulative k L)
    (trapezoidNodeCumulative k 1)
    (trapezoidNodeCumulative k 2)
    (trapezoidNodeCoeff k 2) hs
  have hone := carrier_node_one_gap_eq_slack k
  have hreplace :
      (trapezoidNodeCumulative k L +
          -(trapezoidNodeCumulative k 1)) +
          -(trapezoidNodeCoeff k 2) ≈
        (((((B * oldDiag k 0 + B * oldDiag k 1) + B * oldDiag k N) +
          -(D * (((oldAdj k 0 + oldAdj k 0) + oldAdj k 1) + oldAdj k L)) +
          -((lam + lam) * (D * D))) +
          -(trapezoidNodeCoeff k 2))) :=
    Q'.add_eqv_congr_right _ _ _ hone
  refine Q'.eqv_trans _ _ _ hsplit
    (Q'.eqv_trans _ _ _ hreplace ?_)
  unfold trapezoidNodeCoeff
  exact node_two_slack_algebra B D lam
    (oldAdj k 0) (oldAdj k 1) (oldAdj k 2) (oldAdj k L)
    (oldDiag k 0) (oldDiag k 1) (oldDiag k 2) (oldDiag k N)

private theorem harmonicBlock551_le :
    qpow (harmW 551) 553 ≤ Q'.mkPos 46 125 (by decide) := by
  unfold harmW harmU oneSub unit qpow
  decide

private theorem harmonicResidual551_le :
    qpow (harmW 551) 176 ≤ Q'.mkPos 3 4 (by decide) := by
  unfold harmW harmU oneSub unit qpow
  decide

private theorem c551_94_le :
    c551 94 ≤ Q'.mkPos 1 100000 (by decide) := by
  let w := harmW 551
  let r := Q'.mkPos 46 125 (by decide)
  let s := Q'.mkPos 3 4 (by decide)
  have hiter : qpow w (553 * 16) ≈ qpow (qpow w 553) 16 :=
    AbelianFusionCLT.qpowR_exp_mul w 553 16
  have hpow0 : (0 : Q') ≤ qpow w 553 :=
    qpow_nonneg _ (harmW_nonneg 551) 553
  have hblock : qpow (qpow w 553) 16 ≤ qpow r 16 :=
    HeatKernelGap.qpow_mono hpow0 (by simpa [w, r] using harmonicBlock551_le) 16
  have hmain : qpow w (553 * 16) ≤ qpow r 16 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hiter) hblock
  have hsplit : qpow w (c4 94) ≈
      qpow w (553 * 16) * qpow w 176 := by
    rw [show c4 94 = 553 * 16 + 176 by decide]
    exact HeatKernelRGStep.qpow_add w (553 * 16) 176
  have hres : qpow w 176 ≤ s := by
    simpa [w, s] using harmonicResidual551_le
  have hres0 : (0 : Q') ≤ qpow w 176 :=
    qpow_nonneg _ (harmW_nonneg 551) 176
  have hrpow0 : (0 : Q') ≤ qpow r 16 :=
    qpow_nonneg _ (by unfold r; decide) 16
  have hm1 := Q'.mul_le_mul_of_nonneg_right _ _ (qpow w 176) hmain hres0
  have hm2 := Q'.mul_le_mul_of_nonneg_left _ _ (qpow r 16) hres hrpow0
  have hp : qpow w (c4 94) ≤ qpow r 16 * s :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.le_trans' _ _ _ hm1 hm2)
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 95) hp (by decide)
  unfold c551 coeffW dimQ
  exact Q'.le_trans' _ _ _ hscale (by
    unfold r s qpow
    decide)

private theorem c551_succ_le {a : Nat} (ha : 61 ≤ a) :
    c551 (a + 1) ≤ c551 a := by
  have hs := tail_step551 ha
  have hc0 := coeffW_nonneg (harmW_nonneg 551) a
  have hr : rate551 ≤ (1 : Q') := by unfold rate551; decide
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (c551 a) hr hc0
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv _)))

private theorem c551_antitone_from {a : Nat} (ha : 61 ≤ a) :
    ∀ b, a ≤ b → c551 b ≤ c551 a
  | 0, hab => by omega
  | b + 1, hab => by
      by_cases heq : a = b + 1
      · subst a
        exact Q'.le_refl' _
      · have hab' : a ≤ b := by omega
        exact Q'.le_trans' _ _ _ (c551_succ_le (a := b) (by omega))
          (c551_antitone_from ha b hab')

/-- The terminal character at the first bad scale is below `10⁻⁵`, proved
from two short exact power bounds and the PF2 monotone tail. -/
theorem terminalCoeff551_le :
    c551 (Ncut 551) ≤ Q'.mkPos 1 100000 (by decide) := by
  have ht := c551_antitone_from (a := 94) (by decide)
    (Ncut 551) (by unfold Ncut; omega)
  exact Q'.le_trans' _ _ _ ht c551_94_le

private theorem c551_62_le : c551 62 ≤ Q'.mkPos 3 50 (by decide) := by
  let w := harmW 551
  let r := Q'.mkPos 46 125 (by decide)
  have hiter : qpow w (553 * 7) ≈ qpow (qpow w 553) 7 :=
    AbelianFusionCLT.qpowR_exp_mul w 553 7
  have hpow0 : (0 : Q') ≤ qpow w 553 :=
    qpow_nonneg _ (harmW_nonneg 551) 553
  have hblock : qpow (qpow w 553) 7 ≤ qpow r 7 :=
    HeatKernelGap.qpow_mono hpow0 (by simpa [w, r] using harmonicBlock551_le) 7
  have hmain : qpow w (553 * 7) ≤ qpow r 7 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hiter) hblock
  have hsplit : qpow w (c4 62) ≈
      qpow w (553 * 7) * qpow w 97 := by
    rw [show c4 62 = 553 * 7 + 97 by decide]
    exact HeatKernelRGStep.qpow_add w (553 * 7) 97
  have hres : qpow w 97 ≤ (1 : Q') :=
    HeatKernelGap.qpow_le_one (harmW_nonneg 551) (harmW_le_one 551) 97
  have hres0 : (0 : Q') ≤ qpow w 97 :=
    qpow_nonneg _ (harmW_nonneg 551) 97
  have hrpow0 : (0 : Q') ≤ qpow r 7 :=
    qpow_nonneg _ (by unfold r; decide) 7
  have hm1 := Q'.mul_le_mul_of_nonneg_right _ _ (qpow w 97) hmain hres0
  have hm2 := Q'.mul_le_mul_of_nonneg_left _ _ (qpow r 7) hres hrpow0
  have hp : qpow w (c4 62) ≤ qpow r 7 * (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.le_trans' _ _ _ hm1 hm2)
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 63) hp (by decide)
  unfold c551 coeffW dimQ
  exact Q'.le_trans' _ _ _ hscale (by
    unfold r qpow
    decide)

private theorem square_tail551_step (j : Nat) :
    squareTail551 (j + 1) ≤
      (rate551 * rate551) * squareTail551 j := by
  have hs := tail_step551 (a := 62 + j) (by omega)
  have hc0 := coeffW_nonneg (harmW_nonneg 551) (62 + j)
  have hc10 := coeffW_nonneg (harmW_nonneg 551) (62 + j + 1)
  have hr0 : (0 : Q') ≤ rate551 * c551 (62 + j) :=
    Q'.mul_nonneg _ _ (by unfold rate551; decide) hc0
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ (c551 (62 + j + 1)) hs hc10
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _
    (rate551 * c551 (62 + j)) hs hr0
  unfold squareTail551
  rw [show 62 + (j + 1) = 62 + j + 1 by omega]
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (by
      exact square_rate_collect rate551 (c551 (62 + j)))))

private theorem squareTail551_zero_le :
    squareTail551 0 ≤ Q'.mkPos 9 2500 (by decide) := by
  unfold squareTail551
  have ht := c551_62_le
  have hc0 := coeffW_nonneg (harmW_nonneg 551) 62
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ (c551 62) ht hc0
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.mkPos 3 50 (by decide)) ht (by decide)
  exact Q'.le_trans' _ _ _ h1 h2

private theorem squareTail551_le_one (M : Nat) :
    fsum squareTail551 M ≤ (1 : Q') := by
  have h := CharacterTail.geom_series_le squareTail551
    (Q'.mkPos 9 2500 (by decide)) (rate551 * rate551) (1 : Q')
    (by unfold rate551; decide) (by decide) squareTail551_zero_le
    square_tail551_step (by unfold rate551; decide) M
  rw [MovingCutoff.fsum_eq_finSum]
  exact h

private theorem headD551_plus_one_le :
    coordNormSq (harmW 551) 61 + (1 : Q') ≤ Q'.ofNat 2050 := by
  unfold coordNormSq harmW harmU oneSub unit coeffW dimQ c4 qpow fsum
  decide

/-- A sharp finite-head/geometric-tail upper bound for the diagonal norm. -/
theorem D551_upper : harmonicD 551 ≤ Q'.ofNat 2050 := by
  have h62 : 62 ≤ Ncut 551 := by unfold Ncut; omega
  let M := Ncut 551 - 62
  have hD : harmonicD 551 ≈
      coordNormSq (harmW 551) 61 + fsum squareTail551 (M + 1) := by
    unfold harmonicD coordNormSq squareTail551 c551
    rw [show Ncut 551 + 1 = 62 + (M + 1) by
      unfold M
      omega]
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW (harmW 551) a * coeffW (harmW 551) a) 62 (M + 1)
  have hadd := Q'.add_le_add_left (coordNormSq (harmW 551) 61) _ _
    (squareTail551_le_one (M + 1))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hD)
    (Q'.le_trans' _ _ _ hadd headD551_plus_one_le)

private def massUpper551 : Q' := Q'.mkPos 1 250 (by decide)

private theorem prefixMass551_upper :
    coordNormSq (harmW 551) 40 - adjCorr (harmW 551) 40 ≤
      massUpper551 * coordNormSq (harmW 551) 40 := by
  unfold massUpper551 coordNormSq adjCorr harmW harmU oneSub unit coeffW dimQ
    c4 qpow fsum
  decide

theorem harmonicMass551_le : harmonicMass 551 ≤ massUpper551 := by
  exact harmonicMass_le_of_prefix 551 40 (Ncut 551 - 40) massUpper551
    (by unfold Ncut; omega) prefixMass551_upper

private theorem harmonicMass_mul_D551 :
    harmonicMass 551 * harmonicD 551 ≈ harmonicD 551 - harmonicA 551 := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (harmonicD 551) (harmonicMass_eq_DA 551))
    (Q'.divPos_mul_eqv _ _ _)

private theorem one_sub_mul_eqv_sub_mul (U D : Q') :
    ((1 : Q') + (-U)) * D ≈ D + -(U * D) := by
  ring_qeqv

private theorem sub_add_cancel_eqv (D A : Q') :
    (D + (-A)) + A ≈ D := by
  refine Q'.eqv_trans _ (D + ((-A) + A)) _ (Q'.add_assoc_eqv D (-A) A) ?_
  refine Q'.eqv_trans _ (D + 0) _
    (Q'.add_eqv_congr_left D _ _ (Q'.neg_add_self_eqv A)) ?_
  exact QPoly.q_add_zero_eqv D

private theorem A_lower_of_DA {A D U : Q'} (hDA : D + (-A) ≤ U * D) :
    ((1 : Q') + (-U)) * D ≤ A := by
  have hadd := Q'.add_le_add_right _ _ A hDA
  have hD : D ≤ U * D + A :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (sub_add_cancel_eqv D A)) hadd
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_mul_eqv_sub_mul U D))
    (Q'.sub_le_of_le_add hD)

theorem harmonicA551_lower :
    (((1 : Q') + (-massUpper551)) * harmonicD 551) ≤ harmonicA 551 := by
  have hD0 := Q'.le_of_lt (harmonicD_pos 551)
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (harmonicD 551)
    harmonicMass551_le hD0
  have hDA : harmonicD 551 - harmonicA 551 ≤
      massUpper551 * harmonicD 551 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv harmonicMass_mul_D551) hm
  exact A_lower_of_DA hDA

private def B551 : Q' :=
  (harmonicA 551 + twoInvSq 551 * harmonicD 551) +
    (harmonicA 551 + twoInvSq 551 * harmonicD 551)

private theorem B551_nonneg : (0 : Q') ≤ B551 := by
  have hA := adjCorr_nonneg (harmW_nonneg 551) (Ncut 551)
  have hl : (0 : Q') ≤ twoInvSq 551 := by
    unfold twoInvSq
    exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) 551)
  have hD := Q'.le_of_lt (harmonicD_pos 551)
  unfold B551 harmonicA
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ hA (Q'.mul_nonneg _ _ hl hD))
    (Q'.zero_le_add _ _ hA (Q'.mul_nonneg _ _ hl hD))

private theorem pair_collect551 (r lam D : Q') :
    (r * D + lam * D) + (r * D + lam * D) ≈
      ((r + lam) + (r + lam)) * D := by
  ring_qeqv

private theorem pair_upper551 {A D lam r : Q'} (hA : A ≤ r * D) :
    (A + lam * D) + (A + lam * D) ≤
      ((r + lam) + (r + lam)) * D := by
  have hs := Q'.add_le_add hA (Q'.le_refl' (lam * D))
  have ht := Q'.add_le_add hs hs
  exact Q'.le_trans' _ _ _ ht (Q'.le_of_eqv (pair_collect551 r lam D))

private theorem triple_factor (B x y z : Q') :
    (B * x + B * y) + B * z ≈ B * ((x + y) + z) := by
  ring_qeqv

private theorem terminalDiag551_upper :
    oldDiag 551 (Ncut 551) ≤
      Q'.mkPos 1 100000 (by decide) * Q'.mkPos 1 100000 (by decide) := by
  have ht := terminalCoeff551_le
  unfold oldDiag at ht ⊢
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _
    (coeffW (harmW 551) (Ncut 551)) ht
    (coeffW_nonneg (harmW_nonneg 551) (Ncut 551))
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.mkPos 1 100000 (by decide)) ht (by decide)
  exact Q'.le_trans' _ _ _ h1 h2

private theorem headTriple551_upper :
    (B551 * oldDiag 551 0 + B551 * oldDiag 551 1) +
        B551 * oldDiag 551 (Ncut 551) ≤
      (((rate551 + twoInvSq 551) + (rate551 + twoInvSq 551)) *
        harmonicD 551) *
        ((oldDiag 551 0 + oldDiag 551 1) +
          Q'.mkPos 1 100000 (by decide) * Q'.mkPos 1 100000 (by decide)) := by
  have hsum :
      (oldDiag 551 0 + oldDiag 551 1) + oldDiag 551 (Ncut 551) ≤
        (oldDiag 551 0 + oldDiag 551 1) +
          Q'.mkPos 1 100000 (by decide) * Q'.mkPos 1 100000 (by decide) :=
    Q'.add_le_add_left (oldDiag 551 0 + oldDiag 551 1) _ _
      terminalDiag551_upper
  have hsum0 : (0 : Q') ≤
      (oldDiag 551 0 + oldDiag 551 1) + oldDiag 551 (Ncut 551) := by
    unfold oldDiag
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _
          (coeffW_nonneg (harmW_nonneg 551) 0)
          (coeffW_nonneg (harmW_nonneg 551) 0))
        (Q'.mul_nonneg _ _
          (coeffW_nonneg (harmW_nonneg 551) 1)
          (coeffW_nonneg (harmW_nonneg 551) 1)))
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg 551) (Ncut 551))
        (coeffW_nonneg (harmW_nonneg 551) (Ncut 551)))
  have hBup : B551 ≤
      ((rate551 + twoInvSq 551) + (rate551 + twoInvSq 551)) *
        harmonicD 551 := by
    unfold B551
    exact pair_upper551 harmonicA_le_rate551_D
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _
    ((oldDiag 551 0 + oldDiag 551 1) + oldDiag 551 (Ncut 551))
    hBup hsum0
  have hC0 : (0 : Q') ≤
      ((rate551 + twoInvSq 551) + (rate551 + twoInvSq 551)) *
        harmonicD 551 :=
    Q'.le_trans' _ _ _ B551_nonneg hBup
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _
    (((rate551 + twoInvSq 551) + (rate551 + twoInvSq 551)) *
      harmonicD 551) hsum hC0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (triple_factor B551
      (oldDiag 551 0) (oldDiag 551 1) (oldDiag 551 (Ncut 551))))
    (Q'.le_trans' _ _ _ h1 h2)

private theorem edge551_drop :
    -(harmonicD 551 *
        (((oldAdj 551 0 + oldAdj 551 0) + oldAdj 551 1) +
          oldAdj 551 (Ncut 551 - 1))) ≤
      -(harmonicD 551 *
        ((oldAdj 551 0 + oldAdj 551 0) + oldAdj 551 1)) := by
  have heL : (0 : Q') ≤ oldAdj 551 (Ncut 551 - 1) := by
    unfold oldAdj
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg 551) _)
      (coeffW_nonneg (harmW_nonneg 551) _)
  have he := Q'.add_le_self_of_nonneg
    ((oldAdj 551 0 + oldAdj 551 0) + oldAdj 551 1) _ heL
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD 551) he
    (Q'.le_of_lt (harmonicD_pos 551))
  exact Q'.neg_le_neg hm

private theorem budget551_upper :
    -((twoInvSq 551 + twoInvSq 551) *
        (harmonicD 551 * harmonicD 551)) ≤
      -((twoInvSq 551 + twoInvSq 551) *
        (harmonicD 551 * Q'.mkPos 51048 25 (by decide))) := by
  have hDD := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD 551) D551_lower
    (Q'.le_of_lt (harmonicD_pos 551))
  have hl : (0 : Q') ≤ twoInvSq 551 + twoInvSq 551 := by
    have h : (0 : Q') ≤ twoInvSq 551 := by
      unfold twoInvSq
      exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) 551)
    exact Q'.zero_le_add _ _ h h
  exact Q'.neg_le_neg
    (Q'.mul_le_mul_of_nonneg_left _ _ (twoInvSq 551 + twoInvSq 551) hDD hl)

private def bracket551 : Q' :=
  ((rate551 + twoInvSq 551) + (rate551 + twoInvSq 551)) *
      ((oldDiag 551 0 + oldDiag 551 1) +
        Q'.mkPos 1 100000 (by decide) * Q'.mkPos 1 100000 (by decide)) +
    -((oldAdj 551 0 + oldAdj 551 0) + oldAdj 551 1) +
    -((twoInvSq 551 + twoInvSq 551) * Q'.mkPos 51048 25 (by decide))

theorem bracket551_neg : bracket551 < (0 : Q') := by
  unfold bracket551 rate551 twoInvSq invSqTerm oldAdj oldDiag harmW harmU
    oneSub unit coeffW dimQ c4 qpow
  decide

private theorem slack_collect551
    (D C S E lam d : Q') :
    ((C * D) * S + -(D * E)) + -((lam + lam) * (D * d)) ≈
      D * ((C * S + (-E)) + -((lam + lam) * d)) := by
  ring_qeqv

private theorem carrier_node_one_slack551_le :
    let N := Ncut 551
    let L := N - 1
    let D := harmonicD 551
    let A := harmonicA 551
    let lam := twoInvSq 551
    let B := (A + lam * D) + (A + lam * D)
    ((B * oldDiag 551 0 + B * oldDiag 551 1) + B * oldDiag 551 N) +
        -(D * (((oldAdj 551 0 + oldAdj 551 0) + oldAdj 551 1) +
          oldAdj 551 L)) +
        -((lam + lam) * (D * D)) ≤ D * bracket551 := by
  dsimp only
  have hhead :
      (((harmonicA 551 + twoInvSq 551 * harmonicD 551) +
          (harmonicA 551 + twoInvSq 551 * harmonicD 551)) * oldDiag 551 0 +
        ((harmonicA 551 + twoInvSq 551 * harmonicD 551) +
          (harmonicA 551 + twoInvSq 551 * harmonicD 551)) * oldDiag 551 1) +
        ((harmonicA 551 + twoInvSq 551 * harmonicD 551) +
          (harmonicA 551 + twoInvSq 551 * harmonicD 551)) *
            oldDiag 551 (Ncut 551) ≤
      (((rate551 + twoInvSq 551) + (rate551 + twoInvSq 551)) *
        harmonicD 551) *
        ((oldDiag 551 0 + oldDiag 551 1) +
          Q'.mkPos 1 100000 (by decide) * Q'.mkPos 1 100000 (by decide)) := by
    simpa only [B551] using headTriple551_upper
  have hall := Q'.add_le_add (Q'.add_le_add hhead edge551_drop) budget551_upper
  unfold bracket551
  exact Q'.le_trans' _ _ _ hall (Q'.le_of_eqv
    (slack_collect551 (harmonicD 551)
      ((rate551 + twoInvSq 551) + (rate551 + twoInvSq 551))
      ((oldDiag 551 0 + oldDiag 551 1) +
        Q'.mkPos 1 100000 (by decide) * Q'.mkPos 1 100000 (by decide))
      ((oldAdj 551 0 + oldAdj 551 0) + oldAdj 551 1)
      (twoInvSq 551) (Q'.mkPos 51048 25 (by decide))))

/-- Exact counterexample to the proposed all-`k` node-one boundary premise.
At `k = 551`, deleting node zero leaves a strictly negative terminal gap. -/
theorem node_one_boundary_fails_k551 :
    ¬ ((0 : Q') ≤
      trapezoidNodeCumulative 551 (Ncut 551 - 1) +
        -(trapezoidNodeCumulative 551 1)) := by
  intro hgap
  have hid := carrier_node_one_gap_eq_slack 551
  have hup :
      trapezoidNodeCumulative 551 (Ncut 551 - 1) +
          -(trapezoidNodeCumulative 551 1) ≤
        harmonicD 551 * bracket551 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hid) carrier_node_one_slack551_le
  have hneg : harmonicD 551 * bracket551 < (0 : Q') := by
    have hm := Q'.mul_lt_mul_of_pos_left (harmonicD_pos 551) bracket551_neg
    exact HeatKernelRGStep.lt_of_lt_of_le hm
      (Q'.le_of_eqv (Q'.mul_zero_eqv (harmonicD 551)))
  exact ClusteringImpliesGap.lt_irrefl' (0 : Q') (Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ hgap hup) hneg)

private theorem pair_lower551 :
    ((((1 : Q') + (-massUpper551)) + twoInvSq 551) +
        (((1 : Q') + (-massUpper551)) + twoInvSq 551)) * harmonicD 551 ≤
      B551 := by
  have hs := Q'.add_le_add harmonicA551_lower
    (Q'.le_refl' (twoInvSq 551 * harmonicD 551))
  have ht := Q'.add_le_add hs hs
  unfold B551
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (pair_collect551 ((1 : Q') + (-massUpper551))
        (twoInvSq 551) (harmonicD 551)))) ht

private theorem terminalLeftCoeff551_le :
    c551 (Ncut 551 - 1) ≤ Q'.mkPos 1 100000 (by decide) := by
  have ht := c551_antitone_from (a := 94) (by decide)
    (Ncut 551 - 1) (by unfold Ncut; omega)
  exact Q'.le_trans' _ _ _ ht c551_94_le

private theorem terminalEdge551_upper :
    oldAdj 551 (Ncut 551 - 1) ≤
      Q'.mkPos 1 100000 (by decide) * Q'.mkPos 1 100000 (by decide) := by
  unfold oldAdj
  rw [show Ncut 551 - 1 + 1 = Ncut 551 by unfold Ncut; omega]
  have hL0 := coeffW_nonneg (harmW_nonneg 551) (Ncut 551 - 1)
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _
    (c551 (Ncut 551 - 1)) terminalCoeff551_le hL0
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.mkPos 1 100000 (by decide)) terminalLeftCoeff551_le (by decide)
  exact Q'.le_trans' _ _ _ h1 h2

private theorem headSeedTwo551_lower :
    (((((1 : Q') + (-massUpper551)) + twoInvSq 551) +
        (((1 : Q') + (-massUpper551)) + twoInvSq 551)) * harmonicD 551) *
        ((oldDiag 551 0 + oldDiag 551 1) + oldDiag 551 2) ≤
      ((B551 * oldDiag 551 0 + B551 * oldDiag 551 1) +
        B551 * oldDiag 551 2) + B551 * oldDiag 551 (Ncut 551) := by
  have hS0 : (0 : Q') ≤
      (oldDiag 551 0 + oldDiag 551 1) + oldDiag 551 2 := by
    unfold oldDiag
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _
          (coeffW_nonneg (harmW_nonneg 551) 0)
          (coeffW_nonneg (harmW_nonneg 551) 0))
        (Q'.mul_nonneg _ _
          (coeffW_nonneg (harmW_nonneg 551) 1)
          (coeffW_nonneg (harmW_nonneg 551) 1)))
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg 551) 2)
        (coeffW_nonneg (harmW_nonneg 551) 2))
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _
    ((oldDiag 551 0 + oldDiag 551 1) + oldDiag 551 2)
    pair_lower551 hS0
  have hterm : (0 : Q') ≤ B551 * oldDiag 551 (Ncut 551) := by
    unfold oldDiag
    exact Q'.mul_nonneg _ _ B551_nonneg
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg 551) (Ncut 551))
        (coeffW_nonneg (harmW_nonneg 551) (Ncut 551)))
  have hadd := Q'.add_le_self_of_nonneg
    (((B551 * oldDiag 551 0 + B551 * oldDiag 551 1) + B551 * oldDiag 551 2))
    (B551 * oldDiag 551 (Ncut 551)) hterm
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (triple_factor B551
      (oldDiag 551 0) (oldDiag 551 1) (oldDiag 551 2))) hadd)

private theorem edgeSeedTwo551_lower :
    -(harmonicD 551 *
        (((((oldAdj 551 0 + oldAdj 551 0) +
          (oldAdj 551 1 + oldAdj 551 1)) + oldAdj 551 2) +
          Q'.mkPos 1 100000 (by decide) * Q'.mkPos 1 100000 (by decide)))) ≤
      -(harmonicD 551 *
        ((((oldAdj 551 0 + oldAdj 551 0) +
          (oldAdj 551 1 + oldAdj 551 1)) + oldAdj 551 2) +
          oldAdj 551 (Ncut 551 - 1))) := by
  have he := Q'.add_le_add_left
    (((oldAdj 551 0 + oldAdj 551 0) +
      (oldAdj 551 1 + oldAdj 551 1)) + oldAdj 551 2) _ _
    terminalEdge551_upper
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD 551) he
    (Q'.le_of_lt (harmonicD_pos 551))
  exact Q'.neg_le_neg hm

private theorem budgetSeedTwo551_lower :
    -((twoInvSq 551 + twoInvSq 551) *
        (harmonicD 551 * Q'.ofNat 2050)) ≤
      -((twoInvSq 551 + twoInvSq 551) *
        (harmonicD 551 * harmonicD 551)) := by
  have hDD := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD 551) D551_upper
    (Q'.le_of_lt (harmonicD_pos 551))
  have hl : (0 : Q') ≤ twoInvSq 551 + twoInvSq 551 := by
    have h : (0 : Q') ≤ twoInvSq 551 := by
      unfold twoInvSq
      exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) 551)
    exact Q'.zero_le_add _ _ h h
  exact Q'.neg_le_neg
    (Q'.mul_le_mul_of_nonneg_left _ _ (twoInvSq 551 + twoInvSq 551) hDD hl)

private def bracketSeedTwo551 : Q' :=
  ((((1 : Q') + (-massUpper551)) + twoInvSq 551) +
      (((1 : Q') + (-massUpper551)) + twoInvSq 551)) *
      ((oldDiag 551 0 + oldDiag 551 1) + oldDiag 551 2) +
    -(((((oldAdj 551 0 + oldAdj 551 0) +
      (oldAdj 551 1 + oldAdj 551 1)) + oldAdj 551 2) +
      Q'.mkPos 1 100000 (by decide) * Q'.mkPos 1 100000 (by decide))) +
    -((twoInvSq 551 + twoInvSq 551) * Q'.ofNat 2050)

theorem bracketSeedTwo551_pos : (0 : Q') < bracketSeedTwo551 := by
  unfold bracketSeedTwo551 massUpper551 twoInvSq invSqTerm oldAdj oldDiag harmW harmU
    oneSub unit coeffW dimQ c4 qpow
  decide

private theorem carrier_node_two_slack551_lower :
    harmonicD 551 * bracketSeedTwo551 ≤
      (((B551 * oldDiag 551 0 + B551 * oldDiag 551 1) +
        B551 * oldDiag 551 2) + B551 * oldDiag 551 (Ncut 551)) +
        -(harmonicD 551 *
          ((((oldAdj 551 0 + oldAdj 551 0) +
            (oldAdj 551 1 + oldAdj 551 1)) + oldAdj 551 2) +
            oldAdj 551 (Ncut 551 - 1))) +
        -((twoInvSq 551 + twoInvSq 551) *
          (harmonicD 551 * harmonicD 551)) := by
  have hall := Q'.add_le_add
    (Q'.add_le_add headSeedTwo551_lower edgeSeedTwo551_lower)
    budgetSeedTwo551_lower
  unfold bracketSeedTwo551
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
    (slack_collect551 (harmonicD 551)
      ((((1 : Q') + (-massUpper551)) + twoInvSq 551) +
        (((1 : Q') + (-massUpper551)) + twoInvSq 551))
      ((oldDiag 551 0 + oldDiag 551 1) + oldDiag 551 2)
      ((((oldAdj 551 0 + oldAdj 551 0) +
        (oldAdj 551 1 + oldAdj 551 1)) + oldAdj 551 2) +
        Q'.mkPos 1 100000 (by decide) * Q'.mkPos 1 100000 (by decide))
      (twoInvSq 551) (Q'.ofNat 2050))) hall

/-- The first corrected boundary at the counterexample scale is seed two. -/
theorem node_two_boundary_holds_k551 :
    (0 : Q') ≤ trapezoidNodeCumulative 551 (Ncut 551 - 1) +
      -(trapezoidNodeCumulative 551 2) := by
  have hid := carrier_node_two_gap_eq_slack 551
  have hpos : (0 : Q') < harmonicD 551 * bracketSeedTwo551 := by
    have hm := Q'.mul_lt_mul_of_pos_left (harmonicD_pos 551) bracketSeedTwo551_pos
    exact Q'.lt_of_le_of_lt
      (Q'.ge_of_eqv (Q'.mul_zero_eqv (harmonicD 551))) hm
  exact Q'.le_trans' _ _ _ (Q'.le_of_lt hpos)
    (Q'.le_trans' _ _ _ carrier_node_two_slack551_lower (Q'.ge_of_eqv hid))

#print axioms head_ratio551
#print axioms tail_ratio551
#print axioms tail_step551
#print axioms global_ratio551
#print axioms harmonicA_le_rate551_D
#print axioms D551_lower
#print axioms carrier_node_one_gap_eq_slack
#print axioms terminalCoeff551_le
#print axioms D551_upper
#print axioms harmonicMass551_le
#print axioms carrier_node_two_gap_eq_slack
#print axioms bracket551_neg
#print axioms node_one_boundary_fails_k551
#print axioms bracketSeedTwo551_pos
#print axioms node_two_boundary_holds_k551

end YMGap.Continuum.HarmonicQuadraticBoundaryAll
