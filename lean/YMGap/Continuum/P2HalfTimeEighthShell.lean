/-
Track 11.7-fusion / R4u -- exact eighth half-time boundary shell.

At channel `s = 2*N-8`, the adjacent Clebsch boxes have twenty and
twenty-five endpoint pairs.  `P2HalfTimeEighthRatio` supplies the sharp
equal-coefficient comparison `5*B7 <= 4*B8`.  This module proves the exact
twenty-five-pair support, the physical `4/5` heat floor, the eighth endpoint
coefficient descent, and the resulting physical line-sum transport.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeEighthRatio

namespace YMGap.Continuum.P2HalfTimeEighthShell

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
open YMGap.Continuum.P2HalfTimeFifthShell
open YMGap.Continuum.P2HalfTimeFourthShell
open YMGap.Continuum.P2HalfTimePenultimateShell
open YMGap.Continuum.P2HalfTimeSeventhShell
open YMGap.Continuum.P2HalfTimeSixthShell
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private def fourFifths : Q' := Q'.mkPos 4 5 (by decide)
private def oneFifth : Q' := Q'.mkPos 1 5 (by decide)

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

/-! ## 1. Exact twenty-five-pair endpoint support -/

private theorem fusionInd_comm (a b s : Nat) :
    fusionInd a b s = fusionInd b a s := by
  unfold fusionInd
  rw [fusionOK_symm_ab]

private theorem fusionInd_top_eight_low (N : Nat) (hN : 8 <= N) :
    fusionInd (N - 8) N (2 * N - 8) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 8) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 8) N = N - 8 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 8 + N + (2 * N - 8) = 2 * (2 * N - 8) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 8), Nat.mul_mod_left]

private theorem fusionInd_top_eight_lowMid (N : Nat) (hN : 8 <= N) :
    fusionInd (N - 6) N (2 * N - 8) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 6) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 6) N = N - 6 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 6 + N + (2 * N - 8) = 2 * (2 * N - 7) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 7), Nat.mul_mod_left]

private theorem fusionInd_top_eight_highMid (N : Nat) (hN : 8 <= N) :
    fusionInd (N - 4) N (2 * N - 8) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 4) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 4) N = N - 4 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 4 + N + (2 * N - 8) = 2 * (2 * N - 6) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 6), Nat.mul_mod_left]

private theorem fusionInd_top_eight_high (N : Nat) (hN : 8 <= N) :
    fusionInd (N - 2) N (2 * N - 8) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 2) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 2) N = N - 2 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 2 + N + (2 * N - 8) = 2 * (2 * N - 5) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 5), Nat.mul_mod_left]

private theorem fusionInd_top_eight_diag (N : Nat) (hN : 8 <= N) :
    fusionInd N N (2 * N - 8) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  simp only [Nat.max_self, Nat.min_self]
  refine ⟨by omega, by omega, ?_⟩
  have he : N + N + (2 * N - 8) = 2 * (2 * N - 4) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 4), Nat.mul_mod_left]

private theorem fusionInd_top_eight_zero_other
    (N a : Nat) (hN : 8 <= N) (ha : a < N)
    (hne8 : a ≠ N - 8) (hne6 : a ≠ N - 6)
    (hne4 : a ≠ N - 4) (hne2 : a ≠ N - 2) :
    fusionInd a N (2 * N - 8) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff a N (2 * N - 8)).mp hok with
    ⟨_, hhi, hp⟩
  have halow : N - 8 <= a := by omega
  have hcases : a = N - 8 ∨ a = N - 7 ∨ a = N - 6 ∨
      a = N - 5 ∨ a = N - 4 ∨ a = N - 3 ∨
      a = N - 2 ∨ a = N - 1 := by omega
  rcases hcases with h | h | h | h | h | h | h | h
  · exact hne8 h
  · subst a; omega
  · exact hne6 h
  · subst a; omega
  · exact hne4 h
  · subst a; omega
  · exact hne2 h
  · subst a; omega

private theorem topEightRow (w : Q') (N : Nat) (hN : 8 <= N) :
    fsum (fun a => fusionInd a N (2 * N - 8) *
      (coeffW w a * coeffW w N)) N ≈
      (((coeffW w (N - 8) * coeffW w N +
        coeffW w (N - 6) * coeffW w N) +
        coeffW w (N - 4) * coeffW w N) +
        coeffW w (N - 2) * coeffW w N) := by
  let g := fun a => fusionInd a N (2 * N - 8) *
    (coeffW w a * coeffW w N)
  have hsplit : fsum g N =
      ((((((((fsum g (N - 8) + g (N - 8)) + g (N - 7)) + g (N - 6)) +
        g (N - 5)) + g (N - 4)) + g (N - 3)) + g (N - 2)) +
        g (N - 1)) := by
    rw [show N = (N - 8) + 8 by omega]
    rfl
  rw [hsplit]
  have hpre : fsum g (N - 8) ≈ (0 : Q') := by
    apply fsum_zero_below
    intro a ha
    dsimp only [g]
    rw [fusionInd_top_eight_zero_other N a hN (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h8 : g (N - 8) ≈ coeffW w (N - 8) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_eight_low N hN]
    exact Q'.one_mul_eqv _
  have h7 : g (N - 7) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_eight_zero_other N (N - 7) hN (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h6 : g (N - 6) ≈ coeffW w (N - 6) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_eight_lowMid N hN]
    exact Q'.one_mul_eqv _
  have h5 : g (N - 5) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_eight_zero_other N (N - 5) hN (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h4 : g (N - 4) ≈ coeffW w (N - 4) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_eight_highMid N hN]
    exact Q'.one_mul_eqv _
  have h3 : g (N - 3) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_eight_zero_other N (N - 3) hN (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h2 : g (N - 2) ≈ coeffW w (N - 2) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_eight_high N hN]
    exact Q'.one_mul_eqv _
  have h1 : g (N - 1) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_eight_zero_other N (N - 1) hN (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  let M := ((((((((0 : Q') + coeffW w (N - 8) * coeffW w N) + 0) +
    coeffW w (N - 6) * coeffW w N) + 0) +
    coeffW w (N - 4) * coeffW w N) + 0) +
    coeffW w (N - 2) * coeffW w N) + 0
  refine Q'.eqv_trans _ M _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr' hpre h8) h7) h6) h5) h4) h3) h2) h1
  · dsimp only [M]
    ring_qeqv

theorem boxSumDelta_top_eight (w : Q') (N : Nat) (hN : 8 <= N) :
    boxSumDelta w (N - 1) (2 * N - 8) ≈
      (((coeffW w (N - 8) * coeffW w N +
          coeffW w (N - 6) * coeffW w N) +
        coeffW w (N - 4) * coeffW w N) +
        coeffW w (N - 2) * coeffW w N) +
      ((((coeffW w (N - 8) * coeffW w N +
          coeffW w (N - 6) * coeffW w N) +
        coeffW w (N - 4) * coeffW w N) +
        coeffW w (N - 2) * coeffW w N) +
        coeffW w N * coeffW w N) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft := topEightRow w N hN
  have hright0 := topEightRow w N hN
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 8) *
        (coeffW w N * coeffW w b)) N ≈
        (((coeffW w (N - 8) * coeffW w N +
          coeffW w (N - 6) * coeffW w N) +
          coeffW w (N - 4) * coeffW w N) +
          coeffW w (N - 2) * coeffW w N) := by
    refine Q'.eqv_trans _ _ _ ?_ hright0
    apply CubeRatioBounds.fsum_eqv_congr
    intro b
    rw [fusionInd_comm N b (2 * N - 8)]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
  rw [fusionInd_top_eight_diag N hN]
  exact Q'.add_eqv_congr' hleft
    (Q'.add_eqv_congr' hright (Q'.one_mul_eqv _))

/-- Channel `2*N-8` has exactly twenty-five Clebsch pairs. -/
theorem boxSum_top_eight (w : Q') (N : Nat) (hN : 8 <= N) :
    boxSum w N (2 * N - 8) ≈
      endpointBoxEightExpr
        (coeffW w (N - 8)) (coeffW w (N - 7))
        (coeffW w (N - 6)) (coeffW w (N - 5))
        (coeffW w (N - 4)) (coeffW w (N - 3))
        (coeffW w (N - 2)) (coeffW w (N - 1)) (coeffW w N) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 8)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold := boxSum_top_six w (N - 1) (by omega)
  rw [show 2 * (N - 1) - 6 = 2 * N - 8 by omega] at hold
  have hraw := Q'.add_eqv_congr' hold (boxSumDelta_top_eight w N hN)
  refine Q'.eqv_trans _ _ _ hraw ?_
  simp only [
    show N - 1 - 3 = N - 4 by omega,
    show N - 1 - 4 = N - 5 by omega,
    show N - 1 - 2 = N - 3 by omega,
    show N - 1 - 5 = N - 6 by omega,
    show N - 1 - 1 = N - 2 by omega,
    show N - 1 - 6 = N - 7 by omega]
  simp only [endpointBoxEightExpr, qSum]
  ring_qeqv

/-- The existing exact depth-seven support, repackaged in the common endpoint
polynomial used by the eighth-shell ratio certificate. -/
theorem boxSum_top_seven_expr (w : Q') (N : Nat) (hN : 8 <= N) :
    boxSum w N (2 * N - 7) ≈
      endpointBoxSevenExpr
        (coeffW w (N - 7)) (coeffW w (N - 6))
        (coeffW w (N - 5)) (coeffW w (N - 4))
        (coeffW w (N - 3)) (coeffW w (N - 2))
        (coeffW w (N - 1)) (coeffW w N) := by
  have hraw := boxSum_top_seven w N (by omega)
  refine Q'.eqv_trans _ _ _ hraw ?_
  simp only [endpointBoxSevenExpr, qSum]
  ring_qeqv

/-! ## 2. Physical `4/5` floor and eighth endpoint descent -/

private theorem physical_five_times_eighth_exponent_cleared (r : Nat) :
    5 * (2 * blockNcut (r + 4) - 6) <= physicalWeightDen (r + 4) := by
  let N := blockNcut (r + 4)
  let D := physicalWeightDen (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hcoord := physicalWeightDen_cutoff_square (r + 4)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have h21 : 21 <= N := Nat.le_trans (by decide) hN
  have h21N : 21 * N <= N * N := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right N h21
  have hNN : N * N <= (N + 1) * (N + 1) :=
    Nat.mul_le_mul (Nat.le_succ N) (Nat.le_succ N)
  have hpoly : 25 * (5 * (2 * N - 6)) <= 12 * (N + 1) * (N + 1) := by
    calc
      25 * (5 * (2 * N - 6)) <= 250 * N := by omega
      _ <= 252 * N := by omega
      _ = 12 * (21 * N) := by omega
      _ <= 12 * (N * N) := Nat.mul_le_mul_left 12 h21N
      _ <= 12 * ((N + 1) * (N + 1)) := Nat.mul_le_mul_left 12 hNN
      _ = 12 * (N + 1) * (N + 1) := by ac_rfl
  have hscaled : 25 * (5 * (2 * N - 6)) <= 25 * D := by
    rw [hcoord]
    exact hpoly
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

private theorem scaled_recip_le_fifth (n D : Nat) (hD : 0 < D)
    (h : 5 * n <= D) :
    Q'.ofNat n * Q'.mkPos 1 D hD <= oneFifth := by
  show (Q'.ofNat n * Q'.mkPos 1 D hD).num * (oneFifth.den : Int) <=
    oneFifth.num * ((Q'.ofNat n * Q'.mkPos 1 D hD).den : Int)
  unfold oneFifth
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  push_cast
  exact_mod_cast (by simpa only [Nat.mul_comm] using h)

theorem physical_fourFifths_power_floor_eighth (r : Nat) :
    fourFifths <=
      qpow (blockWeight (r + 4)) (2 * blockNcut (r + 4) - 6) := by
  let k := r + 4
  let N := blockNcut k
  let D := physicalWeightDen k
  let n := 2 * N - 6
  let loss := Q'.ofNat n * ((1 : Q') - blockWeight k)
  have hmargin : ((1 : Q') - blockWeight k) ≈
      Q'.mkPos 1 D (physicalWeightDen_pos k) :=
    Q'.eqv_trans _ _ _ (one_sub_blockWeight_eqv_margin k)
      (blockMargin_eqv_closed k)
  have hlossClosed : loss ≈
      Q'.ofNat n * Q'.mkPos 1 D (physicalWeightDen_pos k) :=
    Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hmargin
  have hloss : loss <= oneFifth :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hlossClosed)
      (scaled_recip_le_fifth n D (physicalWeightDen_pos k) (by
        simpa only [k, N, D, n] using
          physical_five_times_eighth_exponent_cleared r))
  have hsum : fourFifths + loss <= (1 : Q') := by
    have h := Q'.add_le_add_left fourFifths _ _ hloss
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by
      unfold fourFifths oneFifth
      decide))
  have hsub : fourFifths <= (1 : Q') - loss := by
    have hs := Q'.add_le_add_right _ _ (-loss) hsum
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hs
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv fourFifths loss (-loss)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left fourFifths _ 0 (Q'.add_neg_self_eqv loss)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' fourFifths)
  have hbern := MovingCutoff.qpow_ge_bernoulli
    (blockWeight_nonneg k) (blockWeight_le_one k) n
  exact Q'.le_trans' _ _ _ hsub (by simpa only [loss] using hbern)

private theorem physical_margin_cleared_eighth (r : Nat) :
    let N := blockNcut (r + 4)
    physicalWeightDen (r + 4) <= (N - 7) * (2 * N - 13) := by
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
  have hsquare : (N + 1) * (N + 1) <= (N - 7) * (2 * N - 13) := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 7 := ⟨N - 7, by omega⟩
    have hM20 : 20 <= M := by omega
    have h20M : 20 * M <= M * M := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right M hM20
    rw [hM]
    have htwo : 2 * (M + 7) - 13 = 2 * M + 1 := by omega
    rw [htwo]
    simp only [Nat.add_sub_cancel, Nat.mul_add,
      Nat.mul_one, Nat.one_mul, Nat.mul_comm]
    have hmm : M * (M * 2) = 2 * (M * M) := by ac_rfl
    rw [hmm]
    omega
  exact Nat.le_trans hD hsquare

theorem physical_eighth_coeff_descending (r : Nat) :
    coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 7) <=
      coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 8) := by
  let N := blockNcut (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hp0 : Q'.ofNat (N - 7 + 1) *
      qpow (blockWeight (r + 4)) (2 * N - 13) <= Q'.ofNat (N - 7) :=
    physical_power_upper_step r (N - 7) (2 * N - 13) (by
      simpa only [N] using physical_margin_cleared_eighth r)
  have hp : Q'.ofNat (N - 6) *
      qpow (blockWeight (r + 4)) (2 * N - 13) <=
        (1 : Q') * Q'.ofNat (N - 7) := by
    have hp1 : Q'.ofNat (N - 6) *
        qpow (blockWeight (r + 4)) (2 * N - 13) <= Q'.ofNat (N - 7) := by
      simpa only [show N - 7 + 1 = N - 6 by omega] using hp0
    exact Q'.le_trans' _ _ _ hp1 (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have hs := coeffW_succ_le_of_cross
    (w := blockWeight (r + 4)) (R := (1 : Q')) (N - 8)
    (blockWeight_nonneg (r + 4)) (by
      simpa only [show N - 8 + 2 = N - 6 by omega,
        show 2 * (N - 8) + 3 = 2 * N - 13 by omega] using hp)
  have hs' : coeffW (blockWeight (r + 4)) (N - 7) <=
      (1 : Q') * coeffW (blockWeight (r + 4)) (N - 8) := by
    simpa only [show N - 8 + 1 = N - 7 by omega] using hs
  exact Q'.le_trans' _ _ _ hs' (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-! ## 3. Physical box and line-sum transport -/

theorem eighthHalfTimeBoxScalar (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 8 <= N)
    (hpow : fourFifths <= qpow w (2 * N - 6))
    (hIH : coeffW w (N - 7) <= coeffW w (N - 8))
    (hHG : coeffW w (N - 6) <= coeffW w (N - 7))
    (hGF : coeffW w (N - 5) <= coeffW w (N - 6))
    (hFE : coeffW w (N - 4) <= coeffW w (N - 5))
    (hEA : coeffW w (N - 3) <= coeffW w (N - 4))
    (hAX : coeffW w (N - 2) <= coeffW w (N - 3))
    (hXB : coeffW w (N - 1) <= coeffW w (N - 2))
    (hBC : coeffW w N <= coeffW w (N - 1)) :
    dimQ (2 * N - 8) * boxSum w N (2 * N - 7) <=
      qpow w (2 * N - 6) *
        (dimQ (2 * N - 7) * boxSum w N (2 * N - 8)) := by
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
  have hratioExpr : endpointBoxSevenExpr H G F E A X B C <=
      fourFifths * endpointBoxEightExpr I H G F E A X B C := by
    simpa only [I, H, G, F, E, A, X, B, C] using
      eighthBoxRatio I H G F E A X B C hIH hHG hGF hFE hEA hAX hXB hBC hC0
  have eSeven : boxSum w N (2 * N - 7) ≈
      endpointBoxSevenExpr H G F E A X B C := by
    simpa only [H, G, F, E, A, X, B, C] using boxSum_top_seven_expr w N hN
  have eEight : boxSum w N (2 * N - 8) ≈
      endpointBoxEightExpr I H G F E A X B C := by
    simpa only [I, H, G, F, E, A, X, B, C] using boxSum_top_eight w N hN
  have hratio : boxSum w N (2 * N - 7) <=
      fourFifths * boxSum w N (2 * N - 8) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv eSeven) ?_
    refine Q'.le_trans' _ _ _ hratioExpr ?_
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left fourFifths _ _ (Q'.eqv_symm eEight))
  let low := dimQ (2 * N - 8)
  let high := dimQ (2 * N - 7)
  have hboxLeft0 : (0 : Q') <= boxSum w N (2 * N - 7) :=
    boxSum_nonneg hw0 N (2 * N - 7)
  have hboxRight0 : (0 : Q') <= boxSum w N (2 * N - 8) :=
    boxSum_nonneg hw0 N (2 * N - 8)
  have hdim : low <= high := by
    have hnat : 2 * N - 8 + 1 <= 2 * N - 7 + 1 := by omega
    simpa only [low, high, dimQ] using ofNat_le_ofNat hnat
  have hdimScaled : low * boxSum w N (2 * N - 7) <=
      high * boxSum w N (2 * N - 7) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdim hboxLeft0
  have hhigh0 : (0 : Q') <= high := by
    unfold high dimQ
    exact HeatKernelRGStep.zero_le_ofNat _
  have hratioScaled : high * boxSum w N (2 * N - 7) <=
      high * (fourFifths * boxSum w N (2 * N - 8)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ high hratio hhigh0
  have hreorder :
      high * (fourFifths * boxSum w N (2 * N - 8)) ≈
        fourFifths * (high * boxSum w N (2 * N - 8)) := by
    ring_qeqv
  have hhighBox0 : (0 : Q') <= high * boxSum w N (2 * N - 8) :=
    Q'.mul_nonneg _ _ hhigh0 hboxRight0
  have hpowScaled : fourFifths * (high * boxSum w N (2 * N - 8)) <=
      qpow w (2 * N - 6) * (high * boxSum w N (2 * N - 8)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hhighBox0
  change low * boxSum w N (2 * N - 7) <=
    qpow w (2 * N - 6) * (high * boxSum w N (2 * N - 8))
  exact Q'.le_trans' _ _ _ hdimScaled
    (Q'.le_trans' _ _ _ hratioScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hpowScaled))

theorem halfTimeBox_eighth_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 8) * boxSum (blockWeight k) N (2 * N - 7) <=
      qpow (blockWeight k) (2 * N - 6) *
        (dimQ (2 * N - 7) * boxSum (blockWeight k) N (2 * N - 8)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hN : 8 <= N := Nat.le_trans (by decide : 8 <= 79) (by
    simpa only [k, N] using blockNcut_ge_79 r)
  exact eighthHalfTimeBoxScalar w N
    (by simpa only [k, w] using blockWeight_nonneg k) hN
    (by simpa only [k, N, w] using physical_fourFifths_power_floor_eighth r)
    (by simpa only [k, N, w] using physical_eighth_coeff_descending r)
    (by simpa only [k, N, w] using physical_seventh_coeff_descending r)
    (by simpa only [k, N, w] using physical_sixth_coeff_descending r)
    (by simpa only [k, N, w] using physical_fifth_coeff_descending r)
    (by simpa only [k, N, w] using physical_fourth_coeff_descending r)
    (by simpa only [k, N, w] using physical_prepenultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_penultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_terminal_coeff_descending_from_four r)

theorem halfTimeLineSum_eighth_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 8) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 7) <=
      qpow (blockWeight k) (2 * N - 6) *
        (dimQ (2 * N - 7) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 8)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hbox := halfTimeBox_eighth_physical r
  have eleft :
      dimQ (2 * N - 8) * lineSum (lagCorr w N) (2 * N - 7) ≈
        dimQ (2 * N - 8) * boxSum w N (2 * N - 7) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (2 * N - 7)))
  have eright :
      qpow w (2 * N - 6) *
          (dimQ (2 * N - 7) * boxSum w N (2 * N - 8)) ≈
        qpow w (2 * N - 6) *
          (dimQ (2 * N - 7) * lineSum (lagCorr w N) (2 * N - 8)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N (2 * N - 8)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ (by simpa only [k, N, w] using hbox)
      (Q'.le_of_eqv eright))

theorem physical_halfTime_lineSum_eighth_from_four (k : Nat) (hk : 4 <= k) :
    let N := blockNcut k
    dimQ (2 * N - 8) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 7) <=
      qpow (blockWeight k) (2 * N - 6) *
        (dimQ (2 * N - 7) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 8)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using halfTimeLineSum_eighth_physical r

end YMGap.Continuum.P2HalfTimeEighthShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeEighthShell.boxSumDelta_top_eight
#print axioms YMGap.Continuum.P2HalfTimeEighthShell.boxSum_top_eight
#print axioms YMGap.Continuum.P2HalfTimeEighthShell.boxSum_top_seven_expr
#print axioms YMGap.Continuum.P2HalfTimeEighthShell.physical_fourFifths_power_floor_eighth
#print axioms YMGap.Continuum.P2HalfTimeEighthShell.physical_eighth_coeff_descending
#print axioms YMGap.Continuum.P2HalfTimeEighthShell.eighthHalfTimeBoxScalar
#print axioms YMGap.Continuum.P2HalfTimeEighthShell.halfTimeBox_eighth_physical
#print axioms YMGap.Continuum.P2HalfTimeEighthShell.halfTimeLineSum_eighth_physical
#print axioms YMGap.Continuum.P2HalfTimeEighthShell.physical_halfTime_lineSum_eighth_from_four
