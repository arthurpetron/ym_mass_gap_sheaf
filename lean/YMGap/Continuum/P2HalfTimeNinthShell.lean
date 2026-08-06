/-
Track 11.7-fusion / R4w -- exact ninth half-time boundary shell.

At channel `s = 2*N-9`, the adjacent Clebsch boxes have twenty-five and
thirty endpoint pairs.  `P2HalfTimeNinthRatio` supplies the sharp comparison
`6*B8 <= 5*B9`.  This module proves the exact thirty-pair support, the physical
`5/6` heat floor, the ninth endpoint coefficient descent, and the resulting
physical line-sum transport.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeNinthRatio

namespace YMGap.Continuum.P2HalfTimeNinthShell

set_option maxHeartbeats 360000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeEighthRatio
open YMGap.Continuum.P2HalfTimeEighthShell
open YMGap.Continuum.P2HalfTimeFifthShell
open YMGap.Continuum.P2HalfTimeFourthShell
open YMGap.Continuum.P2HalfTimeNinthRatio
open YMGap.Continuum.P2HalfTimePenultimateShell
open YMGap.Continuum.P2HalfTimeSeventhShell
open YMGap.Continuum.P2HalfTimeSixthShell
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private def fiveSixths : Q' := Q'.mkPos 5 6 (by decide)
private def oneSixth : Q' := Q'.mkPos 1 6 (by decide)

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem ofNat_le_ofNat {a b : Nat} (h : a <= b) :
    Q'.ofNat a <= Q'.ofNat b := by
  show (Int.ofNat a) * (1 : Int) <= (Int.ofNat b) * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr h

/-! ## 1. Exact thirty-pair endpoint support -/

private theorem fusionInd_comm (a b s : Nat) :
    fusionInd a b s = fusionInd b a s := by
  unfold fusionInd
  rw [fusionOK_symm_ab]

private theorem fusionInd_top_nine_low (N : Nat) (hN : 9 <= N) :
    fusionInd (N - 9) N (2 * N - 9) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 9) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 9) N = N - 9 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 9 + N + (2 * N - 9) = 2 * (2 * N - 9) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 9), Nat.mul_mod_left]

private theorem fusionInd_top_nine_lowMid (N : Nat) (hN : 9 <= N) :
    fusionInd (N - 7) N (2 * N - 9) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 7) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 7) N = N - 7 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 7 + N + (2 * N - 9) = 2 * (2 * N - 8) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 8), Nat.mul_mod_left]

private theorem fusionInd_top_nine_mid (N : Nat) (hN : 9 <= N) :
    fusionInd (N - 5) N (2 * N - 9) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 5) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 5) N = N - 5 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 5 + N + (2 * N - 9) = 2 * (2 * N - 7) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 7), Nat.mul_mod_left]

private theorem fusionInd_top_nine_highMid (N : Nat) (hN : 9 <= N) :
    fusionInd (N - 3) N (2 * N - 9) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 3) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 3) N = N - 3 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 3 + N + (2 * N - 9) = 2 * (2 * N - 6) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 6), Nat.mul_mod_left]

private theorem fusionInd_top_nine_high (N : Nat) (hN : 9 <= N) :
    fusionInd (N - 1) N (2 * N - 9) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 1) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 1) N = N - 1 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 1 + N + (2 * N - 9) = 2 * (2 * N - 5) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 5), Nat.mul_mod_left]

private theorem fusionInd_top_nine_diag_zero (N : Nat) (hN : 9 <= N) :
    fusionInd N N (2 * N - 9) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff N N (2 * N - 9)).mp hok with
    ⟨_, _, hp⟩
  omega

private theorem fusionInd_top_nine_zero_other
    (N a : Nat) (hN : 9 <= N) (ha : a < N)
    (hne9 : a ≠ N - 9) (hne7 : a ≠ N - 7)
    (hne5 : a ≠ N - 5) (hne3 : a ≠ N - 3)
    (hne1 : a ≠ N - 1) :
    fusionInd a N (2 * N - 9) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff a N (2 * N - 9)).mp hok with
    ⟨_, hhi, hp⟩
  have halow : N - 9 <= a := by omega
  have hcases : a = N - 9 ∨ a = N - 8 ∨ a = N - 7 ∨
      a = N - 6 ∨ a = N - 5 ∨ a = N - 4 ∨
      a = N - 3 ∨ a = N - 2 ∨ a = N - 1 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h
  · exact hne9 h
  · subst a; omega
  · exact hne7 h
  · subst a; omega
  · exact hne5 h
  · subst a; omega
  · exact hne3 h
  · subst a; omega
  · exact hne1 h

private theorem topNineRow (w : Q') (N : Nat) (hN : 9 <= N) :
    fsum (fun a => fusionInd a N (2 * N - 9) *
      (coeffW w a * coeffW w N)) N ≈
      ((((coeffW w (N - 9) * coeffW w N +
        coeffW w (N - 7) * coeffW w N) +
        coeffW w (N - 5) * coeffW w N) +
        coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N) := by
  let g := fun a => fusionInd a N (2 * N - 9) *
    (coeffW w a * coeffW w N)
  have hsplit : fsum g N =
      (((((((((fsum g (N - 9) + g (N - 9)) + g (N - 8)) + g (N - 7)) +
        g (N - 6)) + g (N - 5)) + g (N - 4)) + g (N - 3)) +
        g (N - 2)) + g (N - 1)) := by
    rw [show N = (N - 9) + 9 by omega]
    rfl
  rw [hsplit]
  have hpre : fsum g (N - 9) ≈ (0 : Q') := by
    apply fsum_zero_below
    intro a ha
    dsimp only [g]
    rw [fusionInd_top_nine_zero_other N a hN (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h9 : g (N - 9) ≈ coeffW w (N - 9) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_nine_low N hN]
    exact Q'.one_mul_eqv _
  have h8 : g (N - 8) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_nine_zero_other N (N - 8) hN (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h7 : g (N - 7) ≈ coeffW w (N - 7) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_nine_lowMid N hN]
    exact Q'.one_mul_eqv _
  have h6 : g (N - 6) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_nine_zero_other N (N - 6) hN (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h5 : g (N - 5) ≈ coeffW w (N - 5) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_nine_mid N hN]
    exact Q'.one_mul_eqv _
  have h4 : g (N - 4) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_nine_zero_other N (N - 4) hN (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h3 : g (N - 3) ≈ coeffW w (N - 3) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_nine_highMid N hN]
    exact Q'.one_mul_eqv _
  have h2 : g (N - 2) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_nine_zero_other N (N - 2) hN (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h1 : g (N - 1) ≈ coeffW w (N - 1) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_nine_high N hN]
    exact Q'.one_mul_eqv _
  let M := (((((((((0 : Q') + coeffW w (N - 9) * coeffW w N) + 0) +
    coeffW w (N - 7) * coeffW w N) + 0) +
    coeffW w (N - 5) * coeffW w N) + 0) +
    coeffW w (N - 3) * coeffW w N) + 0) +
    coeffW w (N - 1) * coeffW w N
  refine Q'.eqv_trans _ M _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr'
                    (Q'.add_eqv_congr' hpre h9) h8) h7) h6) h5) h4) h3) h2) h1
  · dsimp only [M]
    ring_qeqv

theorem boxSumDelta_top_nine (w : Q') (N : Nat) (hN : 9 <= N) :
    boxSumDelta w (N - 1) (2 * N - 9) ≈
      ((((coeffW w (N - 9) * coeffW w N +
          coeffW w (N - 7) * coeffW w N) +
        coeffW w (N - 5) * coeffW w N) +
        coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N) +
      ((((coeffW w (N - 9) * coeffW w N +
          coeffW w (N - 7) * coeffW w N) +
        coeffW w (N - 5) * coeffW w N) +
        coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft := topNineRow w N hN
  have hright0 := topNineRow w N hN
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 9) *
        (coeffW w N * coeffW w b)) N ≈
        ((((coeffW w (N - 9) * coeffW w N +
          coeffW w (N - 7) * coeffW w N) +
          coeffW w (N - 5) * coeffW w N) +
          coeffW w (N - 3) * coeffW w N) +
          coeffW w (N - 1) * coeffW w N) := by
    refine Q'.eqv_trans _ _ _ ?_ hright0
    apply CubeRatioBounds.fsum_eqv_congr
    intro b
    rw [fusionInd_comm N b (2 * N - 9)]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
  rw [fusionInd_top_nine_diag_zero N hN]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hleft
      (Q'.add_eqv_congr' hright (Q'.zero_mul_eqv _))) ?_
  ring_qeqv

/-- Channel `2*N-9` has exactly thirty Clebsch pairs. -/
theorem boxSum_top_nine (w : Q') (N : Nat) (hN : 9 <= N) :
    boxSum w N (2 * N - 9) ≈
      endpointBoxNineExpr
        (coeffW w (N - 9)) (coeffW w (N - 8))
        (coeffW w (N - 7)) (coeffW w (N - 6))
        (coeffW w (N - 5)) (coeffW w (N - 4))
        (coeffW w (N - 3)) (coeffW w (N - 2))
        (coeffW w (N - 1)) (coeffW w N) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 9)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold := boxSum_top_seven w (N - 1) (by omega)
  rw [show 2 * (N - 1) - 7 = 2 * N - 9 by omega] at hold
  have hraw := Q'.add_eqv_congr' hold (boxSumDelta_top_nine w N hN)
  refine Q'.eqv_trans _ _ _ hraw ?_
  simp only [
    show N - 1 - 4 = N - 5 by omega,
    show N - 1 - 3 = N - 4 by omega,
    show N - 1 - 5 = N - 6 by omega,
    show N - 1 - 2 = N - 3 by omega,
    show N - 1 - 6 = N - 7 by omega,
    show N - 1 - 1 = N - 2 by omega,
    show N - 1 - 7 = N - 8 by omega]
  simp only [endpointBoxNineExpr, qSum]
  ring_qeqv

/-! ## 2. Physical `5/6` floor and ninth endpoint descent -/

private theorem physical_six_times_ninth_exponent_cleared (r : Nat) :
    6 * (2 * blockNcut (r + 4) - 7) <= physicalWeightDen (r + 4) := by
  let N := blockNcut (r + 4)
  let D := physicalWeightDen (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hcoord := physicalWeightDen_cutoff_square (r + 4)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have h25 : 25 <= N := Nat.le_trans (by decide) hN
  have h25N : 25 * N <= N * N := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right N h25
  have hNN : N * N <= (N + 1) * (N + 1) :=
    Nat.mul_le_mul (Nat.le_succ N) (Nat.le_succ N)
  have hpoly : 25 * (6 * (2 * N - 7)) <= 12 * (N + 1) * (N + 1) := by
    calc
      25 * (6 * (2 * N - 7)) <= 300 * N := by omega
      _ = 12 * (25 * N) := by omega
      _ <= 12 * (N * N) := Nat.mul_le_mul_left 12 h25N
      _ <= 12 * ((N + 1) * (N + 1)) := Nat.mul_le_mul_left 12 hNN
      _ = 12 * (N + 1) * (N + 1) := by ac_rfl
  have hscaled : 25 * (6 * (2 * N - 7)) <= 25 * D := by
    rw [hcoord]
    exact hpoly
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

private theorem scaled_recip_le_sixth (n D : Nat) (hD : 0 < D)
    (h : 6 * n <= D) :
    Q'.ofNat n * Q'.mkPos 1 D hD <= oneSixth := by
  show (Q'.ofNat n * Q'.mkPos 1 D hD).num * (oneSixth.den : Int) <=
    oneSixth.num * ((Q'.ofNat n * Q'.mkPos 1 D hD).den : Int)
  unfold oneSixth
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  push_cast
  exact_mod_cast (by simpa only [Nat.mul_comm] using h)

theorem physical_fiveSixths_power_floor_ninth (r : Nat) :
    fiveSixths <=
      qpow (blockWeight (r + 4)) (2 * blockNcut (r + 4) - 7) := by
  let k := r + 4
  let N := blockNcut k
  let D := physicalWeightDen k
  let n := 2 * N - 7
  let loss := Q'.ofNat n * ((1 : Q') - blockWeight k)
  have hmargin : ((1 : Q') - blockWeight k) ≈
      Q'.mkPos 1 D (physicalWeightDen_pos k) :=
    Q'.eqv_trans _ _ _ (one_sub_blockWeight_eqv_margin k)
      (blockMargin_eqv_closed k)
  have hlossClosed : loss ≈
      Q'.ofNat n * Q'.mkPos 1 D (physicalWeightDen_pos k) :=
    Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hmargin
  have hloss : loss <= oneSixth :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hlossClosed)
      (scaled_recip_le_sixth n D (physicalWeightDen_pos k) (by
        simpa only [k, N, D, n] using
          physical_six_times_ninth_exponent_cleared r))
  have hsum : fiveSixths + loss <= (1 : Q') := by
    have h := Q'.add_le_add_left fiveSixths _ _ hloss
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by
      unfold fiveSixths oneSixth
      decide))
  have hsub : fiveSixths <= (1 : Q') - loss := by
    have hs := Q'.add_le_add_right _ _ (-loss) hsum
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hs
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv fiveSixths loss (-loss)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left fiveSixths _ 0 (Q'.add_neg_self_eqv loss)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' fiveSixths)
  have hbern := MovingCutoff.qpow_ge_bernoulli
    (blockWeight_nonneg k) (blockWeight_le_one k) n
  exact Q'.le_trans' _ _ _ hsub (by simpa only [loss] using hbern)

private theorem physical_margin_cleared_ninth (r : Nat) :
    let N := blockNcut (r + 4)
    physicalWeightDen (r + 4) <= (N - 8) * (2 * N - 15) := by
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
  have hsquare : (N + 1) * (N + 1) <= (N - 8) * (2 * N - 15) := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 8 := ⟨N - 8, by omega⟩
    have hM30 : 30 <= M := by omega
    have hM20 : 20 <= M := Nat.le_trans (by decide) hM30
    have h20M : 20 * M <= M * M := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right M hM20
    rw [hM]
    have htwo : 2 * (M + 8) - 15 = 2 * M + 1 := by omega
    rw [htwo]
    simp only [Nat.add_sub_cancel, Nat.mul_add,
      Nat.mul_one, Nat.one_mul, Nat.mul_comm]
    have hmm : M * (M * 2) = 2 * (M * M) := by ac_rfl
    rw [hmm]
    omega
  exact Nat.le_trans hD hsquare

theorem physical_ninth_coeff_descending (r : Nat) :
    coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 8) <=
      coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 9) := by
  let N := blockNcut (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hp0 : Q'.ofNat (N - 8 + 1) *
      qpow (blockWeight (r + 4)) (2 * N - 15) <= Q'.ofNat (N - 8) :=
    physical_power_upper_step r (N - 8) (2 * N - 15) (by
      simpa only [N] using physical_margin_cleared_ninth r)
  have hp : Q'.ofNat (N - 7) *
      qpow (blockWeight (r + 4)) (2 * N - 15) <=
        (1 : Q') * Q'.ofNat (N - 8) := by
    have hp1 : Q'.ofNat (N - 7) *
        qpow (blockWeight (r + 4)) (2 * N - 15) <= Q'.ofNat (N - 8) := by
      simpa only [show N - 8 + 1 = N - 7 by omega] using hp0
    exact Q'.le_trans' _ _ _ hp1 (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have hs := coeffW_succ_le_of_cross
    (w := blockWeight (r + 4)) (R := (1 : Q')) (N - 9)
    (blockWeight_nonneg (r + 4)) (by
      simpa only [show N - 9 + 2 = N - 7 by omega,
        show 2 * (N - 9) + 3 = 2 * N - 15 by omega] using hp)
  have hs' : coeffW (blockWeight (r + 4)) (N - 8) <=
      (1 : Q') * coeffW (blockWeight (r + 4)) (N - 9) := by
    simpa only [show N - 9 + 1 = N - 8 by omega] using hs
  exact Q'.le_trans' _ _ _ hs' (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-! ## 3. Physical box and line-sum transport -/

theorem ninthHalfTimeBoxScalar (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 9 <= N)
    (hpow : fiveSixths <= qpow w (2 * N - 7))
    (hJI : coeffW w (N - 8) <= coeffW w (N - 9))
    (hIH : coeffW w (N - 7) <= coeffW w (N - 8))
    (hHG : coeffW w (N - 6) <= coeffW w (N - 7))
    (hGF : coeffW w (N - 5) <= coeffW w (N - 6))
    (hFE : coeffW w (N - 4) <= coeffW w (N - 5))
    (hEA : coeffW w (N - 3) <= coeffW w (N - 4))
    (hAX : coeffW w (N - 2) <= coeffW w (N - 3))
    (hXB : coeffW w (N - 1) <= coeffW w (N - 2))
    (hBC : coeffW w N <= coeffW w (N - 1)) :
    dimQ (2 * N - 9) * boxSum w N (2 * N - 8) <=
      qpow w (2 * N - 7) *
        (dimQ (2 * N - 8) * boxSum w N (2 * N - 9)) := by
  let J := coeffW w (N - 9)
  let I := coeffW w (N - 8)
  let H := coeffW w (N - 7)
  let G := coeffW w (N - 6)
  let F := coeffW w (N - 5)
  let E := coeffW w (N - 4)
  let A := coeffW w (N - 3)
  let X := coeffW w (N - 2)
  let B := coeffW w (N - 1)
  let C := coeffW w N
  have hC0 : (0 : Q') <= C := coeffW_nonneg hw0 N
  have hratioExpr : endpointBoxEightExpr I H G F E A X B C <=
      fiveSixths * endpointBoxNineExpr J I H G F E A X B C := by
    simpa only [J, I, H, G, F, E, A, X, B, C] using
      ninthBoxRatio J I H G F E A X B C
        hJI hIH hHG hGF hFE hEA hAX hXB hBC hC0
  have eEight : boxSum w N (2 * N - 8) ≈
      endpointBoxEightExpr I H G F E A X B C := by
    simpa only [I, H, G, F, E, A, X, B, C] using
      boxSum_top_eight w N (by omega)
  have eNine : boxSum w N (2 * N - 9) ≈
      endpointBoxNineExpr J I H G F E A X B C := by
    simpa only [J, I, H, G, F, E, A, X, B, C] using boxSum_top_nine w N hN
  have hratio : boxSum w N (2 * N - 8) <=
      fiveSixths * boxSum w N (2 * N - 9) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv eEight) ?_
    refine Q'.le_trans' _ _ _ hratioExpr ?_
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left fiveSixths _ _ (Q'.eqv_symm eNine))
  let low := dimQ (2 * N - 9)
  let high := dimQ (2 * N - 8)
  have hboxLeft0 : (0 : Q') <= boxSum w N (2 * N - 8) :=
    boxSum_nonneg hw0 N (2 * N - 8)
  have hboxRight0 : (0 : Q') <= boxSum w N (2 * N - 9) :=
    boxSum_nonneg hw0 N (2 * N - 9)
  have hdim : low <= high := by
    have hnat : 2 * N - 9 + 1 <= 2 * N - 8 + 1 := by omega
    simpa only [low, high, dimQ] using ofNat_le_ofNat hnat
  have hdimScaled : low * boxSum w N (2 * N - 8) <=
      high * boxSum w N (2 * N - 8) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdim hboxLeft0
  have hhigh0 : (0 : Q') <= high := by
    unfold high dimQ
    exact HeatKernelRGStep.zero_le_ofNat _
  have hratioScaled : high * boxSum w N (2 * N - 8) <=
      high * (fiveSixths * boxSum w N (2 * N - 9)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ high hratio hhigh0
  have hreorder :
      high * (fiveSixths * boxSum w N (2 * N - 9)) ≈
        fiveSixths * (high * boxSum w N (2 * N - 9)) := by
    ring_qeqv
  have hhighBox0 : (0 : Q') <= high * boxSum w N (2 * N - 9) :=
    Q'.mul_nonneg _ _ hhigh0 hboxRight0
  have hpowScaled : fiveSixths * (high * boxSum w N (2 * N - 9)) <=
      qpow w (2 * N - 7) * (high * boxSum w N (2 * N - 9)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hhighBox0
  change low * boxSum w N (2 * N - 8) <=
    qpow w (2 * N - 7) * (high * boxSum w N (2 * N - 9))
  exact Q'.le_trans' _ _ _ hdimScaled
    (Q'.le_trans' _ _ _ hratioScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hpowScaled))

theorem halfTimeBox_ninth_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 9) * boxSum (blockWeight k) N (2 * N - 8) <=
      qpow (blockWeight k) (2 * N - 7) *
        (dimQ (2 * N - 8) * boxSum (blockWeight k) N (2 * N - 9)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hN : 9 <= N := Nat.le_trans (by decide : 9 <= 79) (by
    simpa only [k, N] using blockNcut_ge_79 r)
  exact ninthHalfTimeBoxScalar w N
    (by simpa only [k, w] using blockWeight_nonneg k) hN
    (by simpa only [k, N, w] using physical_fiveSixths_power_floor_ninth r)
    (by simpa only [k, N, w] using physical_ninth_coeff_descending r)
    (by simpa only [k, N, w] using physical_eighth_coeff_descending r)
    (by simpa only [k, N, w] using physical_seventh_coeff_descending r)
    (by simpa only [k, N, w] using physical_sixth_coeff_descending r)
    (by simpa only [k, N, w] using physical_fifth_coeff_descending r)
    (by simpa only [k, N, w] using physical_fourth_coeff_descending r)
    (by simpa only [k, N, w] using physical_prepenultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_penultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_terminal_coeff_descending_from_four r)

theorem halfTimeLineSum_ninth_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 9) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 8) <=
      qpow (blockWeight k) (2 * N - 7) *
        (dimQ (2 * N - 8) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 9)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hbox := halfTimeBox_ninth_physical r
  have eleft :
      dimQ (2 * N - 9) * lineSum (lagCorr w N) (2 * N - 8) ≈
        dimQ (2 * N - 9) * boxSum w N (2 * N - 8) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (2 * N - 8)))
  have eright :
      qpow w (2 * N - 7) *
          (dimQ (2 * N - 8) * boxSum w N (2 * N - 9)) ≈
        qpow w (2 * N - 7) *
          (dimQ (2 * N - 8) * lineSum (lagCorr w N) (2 * N - 9)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N (2 * N - 9)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ (by simpa only [k, N, w] using hbox)
      (Q'.le_of_eqv eright))

theorem physical_halfTime_lineSum_ninth_from_four (k : Nat) (hk : 4 <= k) :
    let N := blockNcut k
    dimQ (2 * N - 9) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 8) <=
      qpow (blockWeight k) (2 * N - 7) *
        (dimQ (2 * N - 8) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 9)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using halfTimeLineSum_ninth_physical r

end YMGap.Continuum.P2HalfTimeNinthShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeNinthShell.boxSumDelta_top_nine
#print axioms YMGap.Continuum.P2HalfTimeNinthShell.boxSum_top_nine
#print axioms YMGap.Continuum.P2HalfTimeNinthShell.physical_fiveSixths_power_floor_ninth
#print axioms YMGap.Continuum.P2HalfTimeNinthShell.physical_ninth_coeff_descending
#print axioms YMGap.Continuum.P2HalfTimeNinthShell.ninthHalfTimeBoxScalar
#print axioms YMGap.Continuum.P2HalfTimeNinthShell.halfTimeBox_ninth_physical
#print axioms YMGap.Continuum.P2HalfTimeNinthShell.halfTimeLineSum_ninth_physical
#print axioms YMGap.Continuum.P2HalfTimeNinthShell.physical_halfTime_lineSum_ninth_from_four
