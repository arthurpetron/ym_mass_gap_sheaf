/-
Track 11.7-fusion / R4p -- exact fourth half-time boundary shell.

At channel `s = 2*N-4`, the adjacent Clebsch boxes have six and nine
endpoint pairs.  For descending endpoint coefficients
`E >= A >= X >= B >= C`, their scalar difference has the nonnegative
factorization

  2*U - 3*T
    = 4*C*(X-B) + 2*C*(A-X) + 4*C*(E-A)
      + 2*(B-C)^2 + 2*(B-C)*(X-B)
      + 4*(B-C)*(A-X) + 2*(X-B)^2.

Thus `T <= (2/3)*U`.  The physical Bernoulli floor pays the factor `2/3`,
dimension monotonicity pays the adjacent channel, and a sound reflected
integer-polynomial certificate avoids every growing rational normalization.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeAntepenultimateShell
import YMGap.Continuum.P2RetunedFenceThirdShell
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.P2HalfTimeFourthShell

set_option maxHeartbeats 240000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeAntepenultimateShell
open YMGap.Continuum.P2HalfTimePenultimateShell
open YMGap.Continuum.P2RetunedFenceSecondShell
open YMGap.Continuum.P2RetunedFenceThirdShell
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private def oneThird : Q' := Q'.mkPos 1 3 (by decide)

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one]; ac_rfl))

private theorem ofNat_le_ofNat {a b : Nat} (h : a <= b) :
    Q'.ofNat a <= Q'.ofNat b := by
  show (Int.ofNat a) * (1 : Int) <= (Int.ofNat b) * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr h

private theorem add_nonneg {a b : Q'} (ha : (0 : Q') <= a)
    (hb : (0 : Q') <= b) : (0 : Q') <= a + b :=
  Q'.le_trans' _ ((0 : Q') + 0) _ (by decide) (Q'.add_le_add ha hb)

/-! ## 1. Reflected nine-pair/six-pair certificate -/

private def fourthFactorLeft : RingNormaliser.PolyExpr :=
  let E := RingNormaliser.PolyExpr.var 0
  let A := RingNormaliser.PolyExpr.var 1
  let X := RingNormaliser.PolyExpr.var 2
  let B := RingNormaliser.PolyExpr.var 3
  let C := RingNormaliser.PolyExpr.var 4
  let U :=
    .add
      (.add (.mul X X)
        (.add (.mul A B) (.add (.mul A B) (.mul B B))))
      (.add (.add (.mul E C) (.mul X C))
        (.add (.add (.mul E C) (.mul X C)) (.mul C C)))
  .mul (.const 2) U

private def fourthFactorRight : RingNormaliser.PolyExpr :=
  let E := RingNormaliser.PolyExpr.var 0
  let A := RingNormaliser.PolyExpr.var 1
  let X := RingNormaliser.PolyExpr.var 2
  let B := RingNormaliser.PolyExpr.var 3
  let C := RingNormaliser.PolyExpr.var 4
  let T :=
    .add (.add (.mul X B) (.mul X B))
      (.add (.add (.mul A C) (.mul B C))
        (.add (.mul A C) (.mul B C)))
  let dE := .add E (.neg A)
  let dA := .add A (.neg X)
  let dX := .add X (.neg B)
  let dB := .add B (.neg C)
  let slack :=
    .add (.mul (.mul (.const 4) C) dX)
      (.add (.mul (.mul (.const 2) C) dA)
        (.add (.mul (.mul (.const 4) C) dE)
          (.add (.mul (.const 2) (.mul dB dB))
            (.add (.mul (.mul (.const 2) dB) dX)
              (.add (.mul (.mul (.const 4) dB) dA)
                (.mul (.const 2) (.mul dX dX)))))))
  .add (.mul (.const 3) T) slack

private theorem fourthFactor_normal :
    RingNormaliser.normalize fourthFactorLeft =
      RingNormaliser.normalize fourthFactorRight := by decide

private theorem fourth_factor_core (E A X B C : Q') :
    Q'.ofNat 2 *
        ((X * X + (A * B + (A * B + B * B))) +
          ((E * C + X * C) + ((E * C + X * C) + C * C))) ≈
      Q'.ofNat 3 *
          (((X * B) + (X * B)) +
            ((A * C + B * C) + (A * C + B * C))) +
        (Q'.ofNat 4 * C * (X + -B) +
          (Q'.ofNat 2 * C * (A + -X) +
            (Q'.ofNat 4 * C * (E + -A) +
              (Q'.ofNat 2 * ((B + -C) * (B + -C)) +
                (Q'.ofNat 2 * (B + -C) * (X + -B) +
                  (Q'.ofNat 4 * (B + -C) * (A + -X) +
                    Q'.ofNat 2 * ((X + -B) * (X + -B)))))))) := by
  simpa [fourthFactorLeft, fourthFactorRight, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      fourthFactorLeft fourthFactorRight fourthFactor_normal
      (fun | 0 => E | 1 => A | 2 => X | 3 => B | _ => C))

/-- The six-pair endpoint box is at most two thirds of the adjacent
nine-pair box for descending nonnegative endpoint coefficients. -/
theorem fourthBoxRatio (E A X B C : Q')
    (hAE : A <= E) (hXA : X <= A) (hBX : B <= X) (hCB : C <= B)
    (hC0 : (0 : Q') <= C) :
    ((X * B) + (X * B)) +
        ((A * C + B * C) + (A * C + B * C)) <=
      twoThirds *
        ((X * X + (A * B + (A * B + B * B))) +
          ((E * C + X * C) + ((E * C + X * C) + C * C))) := by
  let T := ((X * B) + (X * B)) +
    ((A * C + B * C) + (A * C + B * C))
  let U := (X * X + (A * B + (A * B + B * B))) +
    ((E * C + X * C) + ((E * C + X * C) + C * C))
  let dE := E + -A
  let dA := A + -X
  let dX := X + -B
  let dB := B + -C
  let slack :=
    Q'.ofNat 4 * C * dX +
      (Q'.ofNat 2 * C * dA +
        (Q'.ofNat 4 * C * dE +
          (Q'.ofNat 2 * (dB * dB) +
            (Q'.ofNat 2 * dB * dX +
              (Q'.ofNat 4 * dB * dA + Q'.ofNat 2 * (dX * dX))))))
  have hdE0 : (0 : Q') <= dE := by
    simpa only [dE] using Q'.sub_nonneg_of_le hAE
  have hdA0 : (0 : Q') <= dA := by
    simpa only [dA] using Q'.sub_nonneg_of_le hXA
  have hdX0 : (0 : Q') <= dX := by
    simpa only [dX] using Q'.sub_nonneg_of_le hBX
  have hdB0 : (0 : Q') <= dB := by
    simpa only [dB] using Q'.sub_nonneg_of_le hCB
  have h4CdX0 : (0 : Q') <= Q'.ofNat 4 * C * dX :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdX0
  have h2CdA0 : (0 : Q') <= Q'.ofNat 2 * C * dA :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdA0
  have h4CdE0 : (0 : Q') <= Q'.ofNat 4 * C * dE :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdE0
  have h2dB20 : (0 : Q') <= Q'.ofNat 2 * (dB * dB) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hdB0 hdB0)
  have h2dBdX0 : (0 : Q') <= Q'.ofNat 2 * dB * dX :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdB0) hdX0
  have h4dBdA0 : (0 : Q') <= Q'.ofNat 4 * dB * dA :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdB0) hdA0
  have h2dX20 : (0 : Q') <= Q'.ofNat 2 * (dX * dX) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hdX0 hdX0)
  have hslack0 : (0 : Q') <= slack := by
    exact add_nonneg h4CdX0
      (add_nonneg h2CdA0
        (add_nonneg h4CdE0
          (add_nonneg h2dB20
            (add_nonneg h2dBdX0 (add_nonneg h4dBdA0 h2dX20)))))
  have hthirdSlack0 : (0 : Q') <= oneThird * slack :=
    Q'.mul_nonneg _ _ (by decide) hslack0
  have hfactor : twoThirds * U ≈ T + oneThird * slack := by
    have h23 : twoThirds ≈ Q'.ofNat 2 * oneThird := by
      unfold twoThirds oneThird
      ring_qeqv
    have h13 : oneThird * Q'.ofNat 3 ≈ (1 : Q') := by
      unfold oneThird
      ring_qeqv
    have hcore : Q'.ofNat 2 * U ≈ Q'.ofNat 3 * T + slack := by
      simpa only [T, U, slack, dE, dA, dX, dB] using
        fourth_factor_core E A X B C
    refine Q'.eqv_trans _ ((Q'.ofNat 2 * oneThird) * U) _
      (Q'.mul_eqv_congr_right _ _ U h23) ?_
    refine Q'.eqv_trans _ (oneThird * (Q'.ofNat 2 * U)) _ ?_ ?_
    · refine Q'.eqv_trans _ ((oneThird * Q'.ofNat 2) * U) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ U
          (Q'.mul_comm_eqv (Q'.ofNat 2) oneThird)
      · exact Q'.mul_assoc_eqv oneThird (Q'.ofNat 2) U
    · refine Q'.eqv_trans _ (oneThird * (Q'.ofNat 3 * T + slack)) _
        (Q'.mul_eqv_congr_left oneThird _ _ hcore) ?_
      refine Q'.eqv_trans _
        (oneThird * (Q'.ofNat 3 * T) + oneThird * slack) _
        (Q'.mul_add_eqv oneThird (Q'.ofNat 3 * T) slack) ?_
      refine Q'.add_eqv_congr_right _ _ (oneThird * slack) ?_
      refine Q'.eqv_trans _ ((oneThird * Q'.ofNat 3) * T) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv oneThird (Q'.ofNat 3) T)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * T) _
        (Q'.mul_eqv_congr_right _ _ T h13) ?_
      exact Q'.one_mul_eqv T
  have hbase : T <= T + oneThird * slack :=
    Q'.add_le_self_of_nonneg T (oneThird * slack) hthirdSlack0
  change T <= twoThirds * U
  exact Q'.le_trans' _ _ _ hbase (Q'.ge_of_eqv hfactor)

/-! ## 2. Physical coefficient descent and half-time scalar -/

private theorem physical_margin_cleared_fourth (r : Nat) :
    let N := blockNcut (r + 4)
    physicalWeightDen (r + 4) <= (N - 3) * (2 * N - 5) := by
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
  have hsquare : (N + 1) * (N + 1) <= (N - 3) * (2 * N - 5) := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
    have hM10 : 10 <= M := by omega
    have h10M : 10 * M <= M * M := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right M hM10
    rw [hM]
    have htwo : 2 * (M + 3) - 5 = 2 * M + 1 := by omega
    rw [htwo]
    simp only [Nat.add_sub_cancel, Nat.mul_add,
      Nat.mul_one, Nat.one_mul, Nat.mul_comm]
    have hmm : M * (M * 2) = 2 * (M * M) := by ac_rfl
    rw [hmm]
    omega
  exact Nat.le_trans hD hsquare

/-- The physical heat string descends one more endpoint edge, from `N-4`
to `N-3`. -/
theorem physical_fourth_coeff_descending (r : Nat) :
    coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 3) <=
      coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 4) := by
  let N := blockNcut (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hp0 : Q'.ofNat (N - 3 + 1) *
      qpow (blockWeight (r + 4)) (2 * N - 5) <= Q'.ofNat (N - 3) :=
    physical_power_upper_step r (N - 3) (2 * N - 5) (by
      simpa only [N] using physical_margin_cleared_fourth r)
  have hp : Q'.ofNat (N - 2) *
      qpow (blockWeight (r + 4)) (2 * N - 5) <=
        (1 : Q') * Q'.ofNat (N - 3) := by
    have hp1 : Q'.ofNat (N - 2) *
        qpow (blockWeight (r + 4)) (2 * N - 5) <= Q'.ofNat (N - 3) := by
      simpa only [show N - 3 + 1 = N - 2 by omega] using hp0
    exact Q'.le_trans' _ _ _ hp1 (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have hs := coeffW_succ_le_of_cross
    (w := blockWeight (r + 4)) (R := (1 : Q')) (N - 4)
    (blockWeight_nonneg (r + 4)) (by
      simpa only [show N - 4 + 2 = N - 2 by omega,
        show 2 * (N - 4) + 3 = 2 * N - 5 by omega] using hp)
  have hs' : coeffW (blockWeight (r + 4)) (N - 3) <=
      (1 : Q') * coeffW (blockWeight (r + 4)) (N - 4) := by
    simpa only [show N - 4 + 1 = N - 3 by omega] using hs
  exact Q'.le_trans' _ _ _ hs' (Q'.le_of_eqv (Q'.one_mul_eqv _))

theorem physical_twoThirds_power_floor_fourth (r : Nat) :
    twoThirds <=
      qpow (blockWeight (r + 4)) (2 * blockNcut (r + 4) - 2) := by
  have hfloor := physical_twoThirds_power_floor r
  have hmono := HeatKernelRGStep.qpow_antitone
    (blockWeight_nonneg (r + 4)) (blockWeight_le_one (r + 4))
    (2 * blockNcut (r + 4) - 2) (2 * blockNcut (r + 4)) (by
      have := blockNcut_pos (r + 4)
      omega)
  exact Q'.le_trans' _ _ _ hfloor hmono

theorem fourthHalfTimeScalar (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 4 <= N)
    (hpow : twoThirds <= qpow w (2 * N - 2))
    (hAE : coeffW w (N - 3) <= coeffW w (N - 4))
    (hXA : coeffW w (N - 2) <= coeffW w (N - 3))
    (hBX : coeffW w (N - 1) <= coeffW w (N - 2))
    (hCB : coeffW w N <= coeffW w (N - 1)) :
    dimQ (2 * N - 4) *
        (((coeffW w (N - 2) * coeffW w (N - 1)) +
            (coeffW w (N - 2) * coeffW w (N - 1))) +
          (((coeffW w (N - 3) * coeffW w N +
              coeffW w (N - 1) * coeffW w N) +
            (coeffW w (N - 3) * coeffW w N +
              coeffW w (N - 1) * coeffW w N)))) <=
      qpow w (2 * N - 2) *
        (dimQ (2 * N - 3) *
          (((coeffW w (N - 2) * coeffW w (N - 2)) +
            ((coeffW w (N - 3) * coeffW w (N - 1)) +
              ((coeffW w (N - 3) * coeffW w (N - 1)) +
                coeffW w (N - 1) * coeffW w (N - 1)))) +
          ((coeffW w (N - 4) * coeffW w N +
              coeffW w (N - 2) * coeffW w N) +
            ((coeffW w (N - 4) * coeffW w N +
                coeffW w (N - 2) * coeffW w N) +
              coeffW w N * coeffW w N)))) := by
  let E := coeffW w (N - 4)
  let A := coeffW w (N - 3)
  let X := coeffW w (N - 2)
  let B := coeffW w (N - 1)
  let C := coeffW w N
  let T := ((X * B) + (X * B)) +
    ((A * C + B * C) + (A * C + B * C))
  let U := (X * X + (A * B + (A * B + B * B))) +
    ((E * C + X * C) + ((E * C + X * C) + C * C))
  let low := dimQ (2 * N - 4)
  let high := dimQ (2 * N - 3)
  have hE0 : (0 : Q') <= E := coeffW_nonneg hw0 (N - 4)
  have hA0 : (0 : Q') <= A := coeffW_nonneg hw0 (N - 3)
  have hX0 : (0 : Q') <= X := coeffW_nonneg hw0 (N - 2)
  have hB0 : (0 : Q') <= B := coeffW_nonneg hw0 (N - 1)
  have hC0 : (0 : Q') <= C := coeffW_nonneg hw0 N
  have hT0 : (0 : Q') <= T := by
    exact add_nonneg
      (add_nonneg (Q'.mul_nonneg _ _ hX0 hB0)
        (Q'.mul_nonneg _ _ hX0 hB0))
      (add_nonneg
        (add_nonneg (Q'.mul_nonneg _ _ hA0 hC0)
          (Q'.mul_nonneg _ _ hB0 hC0))
        (add_nonneg (Q'.mul_nonneg _ _ hA0 hC0)
          (Q'.mul_nonneg _ _ hB0 hC0)))
  have hU0 : (0 : Q') <= U := by
    exact add_nonneg
      (add_nonneg (Q'.mul_nonneg _ _ hX0 hX0)
        (add_nonneg (Q'.mul_nonneg _ _ hA0 hB0)
          (add_nonneg (Q'.mul_nonneg _ _ hA0 hB0)
            (Q'.mul_nonneg _ _ hB0 hB0))))
      (add_nonneg
        (add_nonneg (Q'.mul_nonneg _ _ hE0 hC0)
          (Q'.mul_nonneg _ _ hX0 hC0))
        (add_nonneg
          (add_nonneg (Q'.mul_nonneg _ _ hE0 hC0)
            (Q'.mul_nonneg _ _ hX0 hC0))
          (Q'.mul_nonneg _ _ hC0 hC0)))
  have hratio : T <= twoThirds * U := by
    simpa only [E, A, X, B, C, T, U] using
      fourthBoxRatio E A X B C hAE hXA hBX hCB hC0
  have hdim : low <= high := by
    have hnat : 2 * N - 4 + 1 <= 2 * N - 3 + 1 := by omega
    simpa only [low, high, dimQ] using ofNat_le_ofNat hnat
  have hdimScaled : low * T <= high * T :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdim hT0
  have hhigh0 : (0 : Q') <= high := by
    unfold high dimQ
    exact HeatKernelRGStep.zero_le_ofNat _
  have hratioScaled : high * T <= high * (twoThirds * U) :=
    Q'.mul_le_mul_of_nonneg_left _ _ high hratio hhigh0
  have hreorder : high * (twoThirds * U) ≈ twoThirds * (high * U) := by
    ring_qeqv
  have hhighU0 : (0 : Q') <= high * U := Q'.mul_nonneg _ _ hhigh0 hU0
  have hpowScaled : twoThirds * (high * U) <=
      qpow w (2 * N - 2) * (high * U) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hhighU0
  change low * T <= qpow w (2 * N - 2) * (high * U)
  exact Q'.le_trans' _ _ _ hdimScaled
    (Q'.le_trans' _ _ _ hratioScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hpowScaled))

/-! ## 3. Exact physical box and line-sum transport -/

theorem halfTimeBox_fourth_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 4) * boxSum (blockWeight k) N (2 * N - 3) <=
      qpow (blockWeight k) (2 * N - 2) *
        (dimQ (2 * N - 3) * boxSum (blockWeight k) N (2 * N - 4)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hN : 4 <= N := Nat.le_trans (by decide : 4 <= 79) (by
    simpa only [k, N] using blockNcut_ge_79 r)
  have hscalar := fourthHalfTimeScalar w N
    (blockWeight_nonneg k) hN
    (by simpa only [k, N, w] using physical_twoThirds_power_floor_fourth r)
    (by simpa only [k, N, w] using physical_fourth_coeff_descending r)
    (by simpa only [k, N, w] using physical_prepenultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_penultimate_coeff_descending r)
    (by simpa only [k, N, w] using
      physical_terminal_coeff_descending_from_four r)
  have eleft :
      dimQ (2 * N - 4) * boxSum w N (2 * N - 3) ≈
        dimQ (2 * N - 4) *
          (((coeffW w (N - 2) * coeffW w (N - 1)) +
              (coeffW w (N - 2) * coeffW w (N - 1))) +
            (((coeffW w (N - 3) * coeffW w N +
                coeffW w (N - 1) * coeffW w N) +
              (coeffW w (N - 3) * coeffW w N +
                coeffW w (N - 1) * coeffW w N)))) :=
    Q'.mul_eqv_congr_left _ _ _ (boxSum_top_three w N (by omega))
  have eright :
      qpow w (2 * N - 2) *
          (dimQ (2 * N - 3) *
            (((coeffW w (N - 2) * coeffW w (N - 2)) +
              ((coeffW w (N - 3) * coeffW w (N - 1)) +
                ((coeffW w (N - 3) * coeffW w (N - 1)) +
                  coeffW w (N - 1) * coeffW w (N - 1)))) +
            ((coeffW w (N - 4) * coeffW w N +
                coeffW w (N - 2) * coeffW w N) +
              ((coeffW w (N - 4) * coeffW w N +
                  coeffW w (N - 2) * coeffW w N) +
                coeffW w N * coeffW w N)))) ≈
        qpow w (2 * N - 2) *
          (dimQ (2 * N - 3) * boxSum w N (2 * N - 4)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm
        (boxSum_top_four w N hN)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hscalar (Q'.le_of_eqv eright))

theorem halfTimeLineSum_fourth_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 4) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 3) <=
      qpow (blockWeight k) (2 * N - 2) *
        (dimQ (2 * N - 3) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 4)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hbox := halfTimeBox_fourth_physical r
  have eleft :
      dimQ (2 * N - 4) * lineSum (lagCorr w N) (2 * N - 3) ≈
        dimQ (2 * N - 4) * boxSum w N (2 * N - 3) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (2 * N - 3)))
  have eright :
      qpow w (2 * N - 2) *
          (dimQ (2 * N - 3) * boxSum w N (2 * N - 4)) ≈
        qpow w (2 * N - 2) *
          (dimQ (2 * N - 3) * lineSum (lagCorr w N) (2 * N - 4)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N (2 * N - 4)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ (by simpa only [k, N, w] using hbox)
      (Q'.le_of_eqv eright))

/-- Every physical scale `k >= 4` inherits the constant-cost fourth-shell
proof. -/
theorem physical_halfTime_lineSum_fourth_from_four (k : Nat) (hk : 4 <= k) :
    let N := blockNcut k
    dimQ (2 * N - 4) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 3) <=
      qpow (blockWeight k) (2 * N - 2) *
        (dimQ (2 * N - 3) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 4)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using halfTimeLineSum_fourth_physical r

end YMGap.Continuum.P2HalfTimeFourthShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeFourthShell.fourthBoxRatio
#print axioms YMGap.Continuum.P2HalfTimeFourthShell.physical_fourth_coeff_descending
#print axioms YMGap.Continuum.P2HalfTimeFourthShell.physical_twoThirds_power_floor_fourth
#print axioms YMGap.Continuum.P2HalfTimeFourthShell.fourthHalfTimeScalar
#print axioms YMGap.Continuum.P2HalfTimeFourthShell.halfTimeBox_fourth_physical
#print axioms YMGap.Continuum.P2HalfTimeFourthShell.halfTimeLineSum_fourth_physical
#print axioms YMGap.Continuum.P2HalfTimeFourthShell.physical_halfTime_lineSum_fourth_from_four
