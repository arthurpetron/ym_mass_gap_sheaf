/-
Track 11.7-fusion / R4n -- exact penultimate half-time shell.

At channel `s = 2*N-2`, the two Clebsch boxes contain two and four
endpoint pairs.  On the physical schedule the terminal heat coefficients
are descending, while Bernoulli gives the uniform constant floor

  2/3 <= w_k^(2*N_k).

The four-pair box therefore contains three copies of the two-pair product:
one from the diagonal square and two from the distance-two orientations.
The factor `2/3` pays those three copies exactly.  This proves the
penultimate half-time cell without evaluating a growing convolution.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeTerminalShell
import YMGap.Continuum.P2BlockCompatibleScheduleClosed
import YMGap.Continuum.ReciprocalBernoulliUpper

namespace YMGap.Continuum.P2HalfTimePenultimateShell

set_option maxHeartbeats 200000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2RetunedFenceTopShell
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private def twoThirds : Q' := Q'.mkPos 2 3 (by decide)
private def oneThird : Q' := Q'.mkPos 1 3 (by decide)

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

private theorem add_nonneg {a b : Q'} (ha : (0 : Q') <= a)
    (hb : (0 : Q') <= b) : (0 : Q') <= a + b :=
  Q'.le_trans' _ ((0 : Q') + 0) _ (by decide) (Q'.add_le_add ha hb)

private theorem twoThirds_triple (D X : Q') :
    twoThirds * (D * (X + (X + (X + 0)))) ≈ D * (X + X) := by
  have hthreeConst : Q'.ofNat 3 ≈ (1 : Q') + (1 + 1) := by decide
  have htwoConst : Q'.ofNat 2 ≈ (1 : Q') + 1 := by decide
  have hthreeMul : Q'.ofNat 3 * X ≈ X + (X + X) := by
    refine Q'.eqv_trans _ (((1 : Q') + (1 + 1)) * X) _
      (Q'.mul_eqv_congr_right _ _ X hthreeConst) ?_
    refine Q'.eqv_trans _ ((1 : Q') * X + ((1 : Q') + 1) * X) _
      (Q'.add_mul_eqv _ _ X) ?_
    refine Q'.add_eqv_congr' (Q'.one_mul_eqv X) ?_
    refine Q'.eqv_trans _ ((1 : Q') * X + (1 : Q') * X) _
      (Q'.add_mul_eqv _ _ X) ?_
    exact Q'.add_eqv_congr' (Q'.one_mul_eqv X) (Q'.one_mul_eqv X)
  have htwoMul : Q'.ofNat 2 * X ≈ X + X := by
    refine Q'.eqv_trans _ (((1 : Q') + 1) * X) _
      (Q'.mul_eqv_congr_right _ _ X htwoConst) ?_
    refine Q'.eqv_trans _ ((1 : Q') * X + (1 : Q') * X) _
      (Q'.add_mul_eqv _ _ X) ?_
    exact Q'.add_eqv_congr' (Q'.one_mul_eqv X) (Q'.one_mul_eqv X)
  have hthree : X + (X + (X + 0)) ≈ Q'.ofNat 3 * X := by
    refine Q'.eqv_trans _ (X + (X + X)) _ ?_ (Q'.eqv_symm hthreeMul)
    exact Q'.add_eqv_congr_left X _ _
      (Q'.add_eqv_congr_left X _ _ (q_add_zero_eqv X))
  have hinside : D * (X + (X + (X + 0))) ≈ D * (Q'.ofNat 3 * X) :=
    Q'.mul_eqv_congr_left D _ _ hthree
  have hconst : twoThirds * Q'.ofNat 3 ≈ Q'.ofNat 2 := by
    unfold twoThirds
    decide
  refine Q'.eqv_trans _ (twoThirds * (D * (Q'.ofNat 3 * X))) _
    (Q'.mul_eqv_congr_left twoThirds _ _ hinside) ?_
  refine Q'.eqv_trans _ ((twoThirds * Q'.ofNat 3) * (D * X)) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _ (Q'.ofNat 2 * (D * X)) _
    (Q'.mul_eqv_congr_right _ _ (D * X) hconst) ?_
  refine Q'.eqv_trans _ (D * (Q'.ofNat 2 * X)) _ (by ring_qeqv) ?_
  exact Q'.mul_eqv_congr_left D _ _ htwoMul

/-! ## 1. Constant-size endpoint scalar -/

/-- Three positive copies in the four-pair endpoint box, together with the
`2/3` heat floor, pay the two-pair penultimate box. -/
theorem penultimateHalfTimeScalar (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 2 <= N)
    (hpow : twoThirds <= qpow w (2 * N))
    (hBA : coeffW w (N - 1) <= coeffW w (N - 2))
    (hCB : coeffW w N <= coeffW w (N - 1)) :
    dimQ (2 * N - 2) *
        ((coeffW w (N - 1) * coeffW w N) +
          (coeffW w (N - 1) * coeffW w N)) <=
      qpow w (2 * N) *
        (dimQ (2 * N - 1) *
          ((coeffW w (N - 1) * coeffW w (N - 1)) +
            ((coeffW w (N - 2) * coeffW w N) +
              ((coeffW w (N - 2) * coeffW w N) +
                coeffW w N * coeffW w N)))) := by
  let A := coeffW w (N - 2)
  let B := coeffW w (N - 1)
  let C := coeffW w N
  let X := B * C
  let low := dimQ (2 * N - 2)
  let high := dimQ (2 * N - 1)
  let box := B * B + (A * C + (A * C + C * C))
  have hB0 : (0 : Q') <= B := coeffW_nonneg hw0 (N - 1)
  have hC0 : (0 : Q') <= C := coeffW_nonneg hw0 N
  have hX0 : (0 : Q') <= X := Q'.mul_nonneg _ _ hB0 hC0
  have hBB : X <= B * B := by
    exact Q'.mul_le_mul_of_nonneg_left _ _ B hCB hB0
  have hAC : X <= A * C := by
    exact Q'.mul_le_mul_of_nonneg_right _ _ C hBA hC0
  have hCC0 : (0 : Q') <= C * C := Q'.mul_nonneg _ _ hC0 hC0
  have hbox : X + (X + (X + 0)) <= box := by
    exact Q'.add_le_add hBB
      (Q'.add_le_add hAC (Q'.add_le_add hAC hCC0))
  have hdim : low <= high := by
    have hnat : 2 * N - 2 + 1 <= 2 * N - 1 + 1 := by omega
    simpa only [low, high, dimQ] using ofNat_le_ofNat hnat
  have hdouble0 : (0 : Q') <= X + X := add_nonneg hX0 hX0
  have hdimScaled : low * (X + X) <= high * (X + X) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdim hdouble0
  have hthree0 : (0 : Q') <= X + (X + (X + 0)) := by
    exact add_nonneg hX0
      (add_nonneg hX0 (add_nonneg hX0 (by decide)))
  have hhigh0 : (0 : Q') <= high := by
    unfold high dimQ
    exact HeatKernelRGStep.zero_le_ofNat _
  have hboxScaled :
      twoThirds * (high * (X + (X + (X + 0)))) <=
        twoThirds * (high * box) := by
    have hinner := Q'.mul_le_mul_of_nonneg_left _ _ high hbox hhigh0
    exact Q'.mul_le_mul_of_nonneg_left _ _ twoThirds hinner (by decide)
  have hpowScaled : twoThirds * (high * box) <=
      qpow w (2 * N) * (high * box) := by
    have hbox0 : (0 : Q') <= box :=
      Q'.le_trans' _ _ _ hthree0 hbox
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hpow
      (Q'.mul_nonneg _ _ hhigh0 hbox0)
  have hcollapse := twoThirds_triple high X
  change low * (X + X) <= qpow w (2 * N) * (high * box)
  exact Q'.le_trans' _ _ _ hdimScaled
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcollapse)
      (Q'.le_trans' _ _ _ hboxScaled hpowScaled))

/-! ## 2. Physical schedule bounds -/

private theorem blockNcut_ge_79 (r : Nat) :
    79 <= blockNcut (r + 4) := by
  induction r with
  | zero => decide
  | succ r ih =>
      rw [show r + 1 + 4 = (r + 4) + 1 by omega, blockNcut_succ]
      omega

private theorem physical_twice_cutoff_cleared (r : Nat) :
    3 * (2 * blockNcut (r + 4)) <= physicalWeightDen (r + 4) := by
  let N := blockNcut (r + 4)
  let D := physicalWeightDen (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hcoord := physicalWeightDen_cutoff_square (r + 4)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have h13 : 13 <= N := Nat.le_trans (by decide) hN
  have h13N : 13 * N <= N * N := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right N h13
  have hNN : N * N <= (N + 1) * (N + 1) :=
    Nat.mul_le_mul (Nat.le_succ N) (Nat.le_succ N)
  have hpoly : 25 * (3 * (2 * N)) <= 12 * (N + 1) * (N + 1) := by
    calc
      25 * (3 * (2 * N)) = 150 * N := by omega
      _ <= 156 * N := by omega
      _ = 12 * (13 * N) := by omega
      _ <= 12 * (N * N) := Nat.mul_le_mul_left 12 h13N
      _ <= 12 * ((N + 1) * (N + 1)) := Nat.mul_le_mul_left 12 hNN
      _ = 12 * (N + 1) * (N + 1) := by ac_rfl
  have hscaled : 25 * (3 * (2 * N)) <= 25 * D := by
    rw [hcoord]
    exact hpoly
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

private theorem scaled_recip_le_third (n D : Nat) (hD : 0 < D)
    (h : 3 * n <= D) :
    Q'.ofNat n * Q'.mkPos 1 D hD <= oneThird := by
  show (Q'.ofNat n * Q'.mkPos 1 D hD).num * (oneThird.den : Int) <=
    oneThird.num * ((Q'.ofNat n * Q'.mkPos 1 D hD).den : Int)
  unfold oneThird
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  push_cast
  exact_mod_cast (by simpa only [Nat.mul_comm] using h)

private theorem physical_twoThirds_power_floor (r : Nat) :
    twoThirds <=
      qpow (blockWeight (r + 4)) (2 * blockNcut (r + 4)) := by
  let k := r + 4
  let N := blockNcut k
  let D := physicalWeightDen k
  let n := 2 * N
  let loss := Q'.ofNat n * ((1 : Q') - blockWeight k)
  have hmargin : ((1 : Q') - blockWeight k) ≈
      Q'.mkPos 1 D (physicalWeightDen_pos k) :=
    Q'.eqv_trans _ _ _ (one_sub_blockWeight_eqv_margin k)
      (blockMargin_eqv_closed k)
  have hlossClosed : loss ≈
      Q'.ofNat n * Q'.mkPos 1 D (physicalWeightDen_pos k) :=
    Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hmargin
  have hloss : loss <= oneThird :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hlossClosed)
      (scaled_recip_le_third n D (physicalWeightDen_pos k) (by
        simpa only [k, N, D, n] using physical_twice_cutoff_cleared r))
  have hsum : twoThirds + loss <= (1 : Q') := by
    have h := Q'.add_le_add_left twoThirds _ _ hloss
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by
      unfold twoThirds oneThird
      decide))
  have hsub : twoThirds <= (1 : Q') - loss := by
    have hs := Q'.add_le_add_right _ _ (-loss) hsum
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hs
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv twoThirds loss (-loss)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left twoThirds _ 0 (Q'.add_neg_self_eqv loss)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' twoThirds)
  have hbern := MovingCutoff.qpow_ge_bernoulli
    (blockWeight_nonneg k) (blockWeight_le_one k) n
  exact Q'.le_trans' _ _ _ hsub (by simpa only [loss] using hbern)

private theorem physical_margin_cleared_penultimate (r : Nat) :
    let N := blockNcut (r + 4)
    physicalWeightDen (r + 4) <= (N - 1) * (2 * N - 1) := by
  let N := blockNcut (r + 4)
  let D := physicalWeightDen (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hcoord := physicalWeightDen_cutoff_square (r + 4)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have hD : D <= (N + 1) * (N + 1) := by
    have h1225 : (12 : Nat) <= 25 := by decide
    have hscaled : 25 * D <= 25 * ((N + 1) * (N + 1)) := by
      calc
        25 * D = 12 * (N + 1) * (N + 1) := hcoord
        _ = 12 * ((N + 1) * (N + 1)) := by ac_rfl
        _ <= 25 * ((N + 1) * (N + 1)) :=
          Nat.mul_le_mul_right ((N + 1) * (N + 1)) h1225
    exact Nat.le_of_mul_le_mul_left hscaled (by decide)
  have h5N : 5 * N <= N * N := by
    simpa only [Nat.mul_comm] using
      Nat.mul_le_mul_right N (Nat.le_trans (by decide) hN)
  have hsquare : (N + 1) * (N + 1) <= (N - 1) * (2 * N - 1) := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [hM] at h5N
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at h5N
    rw [hM]
    have htwo : 2 * (M + 1) - 1 = 2 * M + 1 := by omega
    rw [htwo]
    simp only [Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    have hmm : M * (M * 2) = 2 * (M * M) := by ac_rfl
    rw [hmm]
    omega
  exact Nat.le_trans hD hsquare

private theorem physical_margin_cleared_terminal (r : Nat) :
    let N := blockNcut (r + 4)
    physicalWeightDen (r + 4) <= N * (2 * N + 1) := by
  let N := blockNcut (r + 4)
  let D := physicalWeightDen (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hcoord := physicalWeightDen_cutoff_square (r + 4)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have hD : D <= (N + 1) * (N + 1) := by
    have h1225 : (12 : Nat) <= 25 := by decide
    have hscaled : 25 * D <= 25 * ((N + 1) * (N + 1)) := by
      calc
        25 * D = 12 * (N + 1) * (N + 1) := hcoord
        _ = 12 * ((N + 1) * (N + 1)) := by ac_rfl
        _ <= 25 * ((N + 1) * (N + 1)) :=
          Nat.mul_le_mul_right ((N + 1) * (N + 1)) h1225
    exact Nat.le_of_mul_le_mul_left hscaled (by decide)
  have h2N : 2 * N <= N * N := by
    simpa only [Nat.mul_comm] using
      Nat.mul_le_mul_right N (Nat.le_trans (by decide) hN)
  have hsquare : (N + 1) * (N + 1) <= N * (2 * N + 1) := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [hM]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul,
      Nat.mul_comm, Nat.mul_left_comm]
    have hmm : M * (M * 2) = 2 * (M * M) := by ac_rfl
    rw [hmm]
    omega
  exact Nat.le_trans hD hsquare

private theorem bernDen_step_cover (m n D : Nat) (hD : 0 < D)
    (hcleared : D <= m * n) :
    Q'.ofNat (m + 1) <=
      Q'.ofNat m * bernDen (Q'.mkPos 1 D hD) n := by
  show (Q'.ofNat (m + 1)).num *
      ((Q'.ofNat m * bernDen (Q'.mkPos 1 D hD) n).den : Int) <=
    (Q'.ofNat m * bernDen (Q'.mkPos 1 D hD) n).num *
      (Q'.ofNat (m + 1)).den
  unfold bernDen
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.add_num_cast, Q'.add_den_cast, Q'.mkPos_num,
    Q'.mkPos_den, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.one_mul, Int.mul_one]
  push_cast
  have htarget : (m + 1) * D <= m * (D + n) := by
    have hadd := Nat.add_le_add_left hcleared (m * D)
    calc
      (m + 1) * D = m * D + D := by rw [Nat.add_mul]; simp
      _ <= m * D + m * n := hadd
      _ = m * (D + n) := by rw [Nat.mul_add]
  exact_mod_cast htarget

private theorem physical_power_upper_step (r m n : Nat)
    (hcleared : physicalWeightDen (r + 4) <= m * n) :
    Q'.ofNat (m + 1) * qpow (blockWeight (r + 4)) n <= Q'.ofNat m := by
  let k := r + 4
  let D := physicalWeightDen k
  let u := blockMargin k
  have hclosed : u ≈ Q'.mkPos 1 D (physicalWeightDen_pos k) := by
    simpa only [u, D] using blockMargin_eqv_closed k
  have hden : bernDen u n ≈
      bernDen (Q'.mkPos 1 D (physicalWeightDen_pos k)) n := by
    unfold bernDen
    exact Q'.add_eqv_congr_left 1 _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hclosed)
  have hcoverClosed : Q'.ofNat (m + 1) <=
      Q'.ofNat m * bernDen (Q'.mkPos 1 D (physicalWeightDen_pos k)) n :=
    bernDen_step_cover m n D (physicalWeightDen_pos k) (by
      simpa only [k, D] using hcleared)
  have hcover : Q'.ofNat (m + 1) <= Q'.ofNat m * bernDen u n :=
    Q'.le_trans' _ _ _ hcoverClosed
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat m) _ _ hden))
  have hbern : qpow (blockWeight k) n * bernDen u n <= (1 : Q') := by
    have h := oneSub_pow_mul_bernDen_le
      (blockMargin_nonneg k) (blockMargin_le_one k) n
    have hweight : blockWeight k = oneSub u := rfl
    simpa only [hweight] using h
  have hcoverScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow (blockWeight k) n) hcover
      (qpow_nonneg _ (blockWeight_nonneg k) n)
  have hbernScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat m) hbern (HeatKernelRGStep.zero_le_ofNat m)
  have hleft : qpow (blockWeight k) n * Q'.ofNat (m + 1) ≈
      Q'.ofNat (m + 1) * qpow (blockWeight k) n := Q'.mul_comm_eqv _ _
  have hmiddle :
      qpow (blockWeight k) n * (Q'.ofNat m * bernDen u n) ≈
        Q'.ofNat m * (qpow (blockWeight k) n * bernDen u n) := by
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hcoverScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle)
        (Q'.le_trans' _ _ _ hbernScaled (Q'.le_of_eqv (Q'.mul_one_eqv _)))))

private theorem physical_penultimate_coeff_descending (r : Nat) :
    coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 1) <=
      coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 2) := by
  let N := blockNcut (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hp0 : Q'.ofNat (N - 1 + 1) *
      qpow (blockWeight (r + 4)) (2 * N - 1) <= Q'.ofNat (N - 1) :=
    physical_power_upper_step r (N - 1) (2 * N - 1) (by
      simpa only [N] using physical_margin_cleared_penultimate r)
  have hp : Q'.ofNat N * qpow (blockWeight (r + 4)) (2 * N - 1) <=
      (1 : Q') * Q'.ofNat (N - 1) := by
    have hp1 : Q'.ofNat N * qpow (blockWeight (r + 4)) (2 * N - 1) <=
        Q'.ofNat (N - 1) := by
      simpa only [show N - 1 + 1 = N by omega] using hp0
    exact Q'.le_trans' _ _ _ hp1 (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have hs := coeffW_succ_le_of_cross
    (w := blockWeight (r + 4)) (R := (1 : Q')) (N - 2)
    (blockWeight_nonneg (r + 4)) (by
      simpa only [show N - 2 + 2 = N by omega,
        show 2 * (N - 2) + 3 = 2 * N - 1 by omega] using hp)
  have hs' : coeffW (blockWeight (r + 4)) (N - 1) <=
      (1 : Q') * coeffW (blockWeight (r + 4)) (N - 2) := by
    simpa only [show N - 2 + 1 = N - 1 by omega] using hs
  exact Q'.le_trans' _ _ _ hs' (Q'.le_of_eqv (Q'.one_mul_eqv _))

private theorem physical_terminal_coeff_descending_from_four (r : Nat) :
    coeffW (blockWeight (r + 4)) (blockNcut (r + 4)) <=
      coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 1) := by
  let N := blockNcut (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hp0 : Q'.ofNat (N + 1) *
      qpow (blockWeight (r + 4)) (2 * N + 1) <= Q'.ofNat N :=
    physical_power_upper_step r N (2 * N + 1) (by
      simpa only [N] using physical_margin_cleared_terminal r)
  have hp : Q'.ofNat (N + 1) *
      qpow (blockWeight (r + 4)) (2 * N + 1) <=
        (1 : Q') * Q'.ofNat N :=
    Q'.le_trans' _ _ _ hp0 (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have hs := coeffW_succ_le_of_cross
    (w := blockWeight (r + 4)) (R := (1 : Q')) (N - 1)
    (blockWeight_nonneg (r + 4)) (by
      simpa only [show N - 1 + 2 = N + 1 by omega,
        show 2 * (N - 1) + 3 = 2 * N + 1 by omega] using hp)
  have hs' : coeffW (blockWeight (r + 4)) N <=
      (1 : Q') * coeffW (blockWeight (r + 4)) (N - 1) := by
    simpa only [show N - 1 + 1 = N by omega] using hs
  exact Q'.le_trans' _ _ _ hs' (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-! ## 3. Box, line-sum, and physical cells -/

theorem halfTimeBox_penultimate_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 2) * boxSum (blockWeight k) N (2 * N - 1) <=
      qpow (blockWeight k) (2 * N) *
        (dimQ (2 * N - 1) * boxSum (blockWeight k) N (2 * N - 2)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hN : 2 <= N := Nat.le_trans (by decide : 2 <= 79) (by
    simpa only [k, N] using blockNcut_ge_79 r)
  have hscalar := penultimateHalfTimeScalar w N (blockWeight_nonneg k) hN
    (by simpa only [k, N, w] using physical_twoThirds_power_floor r)
    (by simpa only [k, N, w] using physical_penultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_terminal_coeff_descending_from_four r)
  have eleft :
      dimQ (2 * N - 2) * boxSum w N (2 * N - 1) ≈
        dimQ (2 * N - 2) *
          ((coeffW w (N - 1) * coeffW w N) +
            (coeffW w (N - 1) * coeffW w N)) :=
    Q'.mul_eqv_congr_left _ _ _ (boxSum_top_odd w N (by omega))
  have eright :
      qpow w (2 * N) *
          (dimQ (2 * N - 1) *
            ((coeffW w (N - 1) * coeffW w (N - 1)) +
              ((coeffW w (N - 2) * coeffW w N) +
                ((coeffW w (N - 2) * coeffW w N) +
                  coeffW w N * coeffW w N)))) ≈
        qpow w (2 * N) *
          (dimQ (2 * N - 1) * boxSum w N (2 * N - 2)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm
        (boxSum_top_even w N hN)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hscalar (Q'.le_of_eqv eright))

theorem halfTimeLineSum_penultimate_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 2) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 1) <=
      qpow (blockWeight k) (2 * N) *
        (dimQ (2 * N - 1) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 2)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hbox := halfTimeBox_penultimate_physical r
  have eleft :
      dimQ (2 * N - 2) * lineSum (lagCorr w N) (2 * N - 1) ≈
        dimQ (2 * N - 2) * boxSum w N (2 * N - 1) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (2 * N - 1)))
  have eright :
      qpow w (2 * N) *
          (dimQ (2 * N - 1) * boxSum w N (2 * N - 2)) ≈
        qpow w (2 * N) *
          (dimQ (2 * N - 1) * lineSum (lagCorr w N) (2 * N - 2)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N (2 * N - 2)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ (by simpa only [k, N, w] using hbox)
      (Q'.le_of_eqv eright))

/-- Every physical scale `k >= 4` inherits the constant-cost penultimate
shell proof. -/
theorem physical_halfTime_lineSum_penultimate_from_four (k : Nat) (hk : 4 <= k) :
    let N := blockNcut k
    dimQ (2 * N - 2) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 1) <=
      qpow (blockWeight k) (2 * N) *
        (dimQ (2 * N - 1) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 2)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using halfTimeLineSum_penultimate_physical r

end YMGap.Continuum.P2HalfTimePenultimateShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimePenultimateShell.penultimateHalfTimeScalar
#print axioms YMGap.Continuum.P2HalfTimePenultimateShell.halfTimeBox_penultimate_physical
#print axioms YMGap.Continuum.P2HalfTimePenultimateShell.halfTimeLineSum_penultimate_physical
#print axioms YMGap.Continuum.P2HalfTimePenultimateShell.physical_halfTime_lineSum_penultimate_from_four
