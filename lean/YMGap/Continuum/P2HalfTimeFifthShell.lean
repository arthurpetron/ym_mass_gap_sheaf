/-
Track 11.7-fusion / R4q -- exact fifth half-time boundary shell.

At channel `s = 2*N-5`, the adjacent Clebsch boxes have nine and twelve
endpoint pairs.  Their equal-coefficient ratio is sharply `3/4`.  For a
descending endpoint string `F >= E >= A >= X >= B >= C`, the cleared
difference `3*V - 4*U` is a sum of eleven nonnegative increment products.

This file extracts the twelve-pair shell by a finite support theorem, checks
the nonlinear factorization through the proved reflective polynomial
normalizer, proves the physical `3/4` Bernoulli floor, and transports the
result to the exact line-sum carrier.  No growing convolution is evaluated.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeFourthShell
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.P2HalfTimeFifthShell

set_option maxHeartbeats 300000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeFourthShell
open YMGap.Continuum.P2HalfTimePenultimateShell
open YMGap.Continuum.P2RetunedFenceSecondShell
open YMGap.Continuum.P2RetunedFenceThirdShell
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private def threeFourths : Q' := Q'.mkPos 3 4 (by decide)
private def oneFourth : Q' := Q'.mkPos 1 4 (by decide)

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

private theorem add_nonneg {a b : Q'} (ha : (0 : Q') <= a)
    (hb : (0 : Q') <= b) : (0 : Q') <= a + b :=
  Q'.le_trans' _ ((0 : Q') + 0) _ (by decide) (Q'.add_le_add ha hb)

/-! ## 1. Exact twelve-pair endpoint support -/

private theorem fusionInd_comm (a b s : Nat) :
    fusionInd a b s = fusionInd b a s := by
  unfold fusionInd
  rw [fusionOK_symm_ab]

private theorem fusionInd_top_five_low (N : Nat) (hN : 5 <= N) :
    fusionInd (N - 5) N (2 * N - 5) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 5) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 5) N = N - 5 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 5 + N + (2 * N - 5) = 2 * (2 * N - 5) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 5), Nat.mul_mod_left]

private theorem fusionInd_top_five_mid (N : Nat) (hN : 5 <= N) :
    fusionInd (N - 3) N (2 * N - 5) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 3) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 3) N = N - 3 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 3 + N + (2 * N - 5) = 2 * (2 * N - 4) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 4), Nat.mul_mod_left]

private theorem fusionInd_top_five_high (N : Nat) (hN : 5 <= N) :
    fusionInd (N - 1) N (2 * N - 5) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 1) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 1) N = N - 1 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 1 + N + (2 * N - 5) = 2 * (2 * N - 3) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 3), Nat.mul_mod_left]

private theorem fusionInd_top_five_diag_zero (N : Nat) (hN : 5 <= N) :
    fusionInd N N (2 * N - 5) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff N N (2 * N - 5)).mp hok with
    ⟨_, _, hp⟩
  omega

private theorem fusionInd_top_five_zero_other
    (N a : Nat) (hN : 5 <= N) (ha : a < N)
    (hne5 : a ≠ N - 5) (hne3 : a ≠ N - 3) (hne1 : a ≠ N - 1) :
    fusionInd a N (2 * N - 5) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff a N (2 * N - 5)).mp hok with
    ⟨_, hhi, hp⟩
  have halow : N - 5 <= a := by omega
  have hcases : a = N - 5 ∨ a = N - 4 ∨ a = N - 3 ∨
      a = N - 2 ∨ a = N - 1 := by omega
  rcases hcases with h | h | h | h | h
  · exact hne5 h
  · subst a; omega
  · exact hne3 h
  · subst a; omega
  · exact hne1 h

private theorem topFiveRow (w : Q') (N : Nat) (hN : 5 <= N) :
    fsum (fun a => fusionInd a N (2 * N - 5) *
      (coeffW w a * coeffW w N)) N ≈
      (coeffW w (N - 5) * coeffW w N +
        coeffW w (N - 3) * coeffW w N) +
      coeffW w (N - 1) * coeffW w N := by
  let g := fun a => fusionInd a N (2 * N - 5) *
    (coeffW w a * coeffW w N)
  have hsplit : fsum g N =
      (((((fsum g (N - 5) + g (N - 5)) + g (N - 4)) + g (N - 3)) +
        g (N - 2)) + g (N - 1)) := by
    rw [show N = (N - 5) + 5 by omega]
    rfl
  rw [hsplit]
  have hpre : fsum g (N - 5) ≈ (0 : Q') := by
    apply fsum_zero_below
    intro a ha
    dsimp only [g]
    rw [fusionInd_top_five_zero_other N a hN (by omega)
      (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h5 : g (N - 5) ≈ coeffW w (N - 5) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_five_low N hN]
    exact Q'.one_mul_eqv _
  have h4 : g (N - 4) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_five_zero_other N (N - 4) hN (by omega)
      (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h3 : g (N - 3) ≈ coeffW w (N - 3) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_five_mid N hN]
    exact Q'.one_mul_eqv _
  have h2 : g (N - 2) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_five_zero_other N (N - 2) hN (by omega)
      (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h1 : g (N - 1) ≈ coeffW w (N - 1) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_five_high N hN]
    exact Q'.one_mul_eqv _
  let M := (((((0 : Q') + coeffW w (N - 5) * coeffW w N) + 0) +
    coeffW w (N - 3) * coeffW w N) + 0) +
    coeffW w (N - 1) * coeffW w N
  refine Q'.eqv_trans _ M _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr' hpre h5) h4) h3) h2) h1
  · dsimp only [M]
    ring_qeqv

theorem boxSumDelta_top_five (w : Q') (N : Nat) (hN : 5 <= N) :
    boxSumDelta w (N - 1) (2 * N - 5) ≈
      ((coeffW w (N - 5) * coeffW w N +
          coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N) +
      ((coeffW w (N - 5) * coeffW w N +
          coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft := topFiveRow w N hN
  have hright0 := topFiveRow w N hN
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 5) *
        (coeffW w N * coeffW w b)) N ≈
        (coeffW w (N - 5) * coeffW w N +
          coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N := by
    refine Q'.eqv_trans _ _ _ ?_ hright0
    apply CubeRatioBounds.fsum_eqv_congr
    intro b
    rw [fusionInd_comm N b (2 * N - 5)]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
  rw [fusionInd_top_five_diag_zero N hN]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hleft
      (Q'.add_eqv_congr' hright (Q'.zero_mul_eqv _))) ?_
  ring_qeqv

/-- Channel `2*N-5` has exactly twelve Clebsch pairs. -/
theorem boxSum_top_five (w : Q') (N : Nat) (hN : 5 <= N) :
    boxSum w N (2 * N - 5) ≈
      (((coeffW w (N - 3) * coeffW w (N - 2)) +
          (coeffW w (N - 3) * coeffW w (N - 2))) +
        ((coeffW w (N - 4) * coeffW w (N - 1) +
            coeffW w (N - 2) * coeffW w (N - 1)) +
          (coeffW w (N - 4) * coeffW w (N - 1) +
            coeffW w (N - 2) * coeffW w (N - 1)))) +
      (((coeffW w (N - 5) * coeffW w N +
          coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N) +
       ((coeffW w (N - 5) * coeffW w N +
          coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N)) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 5)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold := boxSum_top_three w (N - 1) (by omega)
  rw [show 2 * (N - 1) - 3 = 2 * N - 5 by omega] at hold
  exact Q'.add_eqv_congr' hold (boxSumDelta_top_five w N hN)

/-! ## 2. Reflected sharp `3/4` ratio -/

private def fifthFactorLeft : RingNormaliser.PolyExpr :=
  let F := RingNormaliser.PolyExpr.var 0
  let E := RingNormaliser.PolyExpr.var 1
  let A := RingNormaliser.PolyExpr.var 2
  let X := RingNormaliser.PolyExpr.var 3
  let B := RingNormaliser.PolyExpr.var 4
  let C := RingNormaliser.PolyExpr.var 5
  let V :=
    .add
      (.add (.add (.mul A X) (.mul A X))
        (.add (.add (.mul E B) (.mul X B))
          (.add (.mul E B) (.mul X B))))
      (.add (.add (.add (.mul F C) (.mul A C)) (.mul B C))
        (.add (.add (.mul F C) (.mul A C)) (.mul B C)))
  .mul (.const 3) V

private def fifthFactorRight : RingNormaliser.PolyExpr :=
  let F := RingNormaliser.PolyExpr.var 0
  let E := RingNormaliser.PolyExpr.var 1
  let A := RingNormaliser.PolyExpr.var 2
  let X := RingNormaliser.PolyExpr.var 3
  let B := RingNormaliser.PolyExpr.var 4
  let C := RingNormaliser.PolyExpr.var 5
  let U :=
    .add
      (.add (.mul X X)
        (.add (.mul A B) (.add (.mul A B) (.mul B B))))
      (.add (.add (.mul E C) (.mul X C))
        (.add (.add (.mul E C) (.mul X C)) (.mul C C)))
  let dF := .add F (.neg E)
  let dE := .add E (.neg A)
  let dA := .add A (.neg X)
  let dX := .add X (.neg B)
  let dB := .add B (.neg C)
  let slack :=
    .add (.mul (.mul (.const 6) C) dB)
      (.add (.mul (.mul (.const 4) C) dX)
        (.add (.mul (.mul (.const 8) C) dA)
          (.add (.mul (.mul (.const 4) C) dE)
            (.add (.mul (.mul (.const 6) C) dF)
              (.add (.mul (.const 2) (.mul dB dB))
                (.add (.mul (.mul (.const 8) dB) dX)
                  (.add (.mul (.mul (.const 4) dB) dA)
                    (.add (.mul (.mul (.const 6) dB) dE)
                      (.add (.mul (.const 2) (.mul dX dX))
                        (.mul (.mul (.const 6) dX) dA))))))))))
  .add (.mul (.const 4) U) slack

private theorem fifthFactor_normal :
    RingNormaliser.normalize fifthFactorLeft =
      RingNormaliser.normalize fifthFactorRight := by decide

private theorem fifth_factor_core (F E A X B C : Q') :
    Q'.ofNat 3 *
        (((A * X + A * X) + ((E * B + X * B) + (E * B + X * B))) +
          (((F * C + A * C) + B * C) + ((F * C + A * C) + B * C))) ≈
      Q'.ofNat 4 *
          ((X * X + (A * B + (A * B + B * B))) +
            ((E * C + X * C) + ((E * C + X * C) + C * C))) +
        (Q'.ofNat 6 * C * (B + -C) +
          (Q'.ofNat 4 * C * (X + -B) +
            (Q'.ofNat 8 * C * (A + -X) +
              (Q'.ofNat 4 * C * (E + -A) +
                (Q'.ofNat 6 * C * (F + -E) +
                  (Q'.ofNat 2 * ((B + -C) * (B + -C)) +
                    (Q'.ofNat 8 * (B + -C) * (X + -B) +
                      (Q'.ofNat 4 * (B + -C) * (A + -X) +
                        (Q'.ofNat 6 * (B + -C) * (E + -A) +
                          (Q'.ofNat 2 * ((X + -B) * (X + -B)) +
                            Q'.ofNat 6 * (X + -B) * (A + -X))))))))))) := by
  simpa [fifthFactorLeft, fifthFactorRight, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      fifthFactorLeft fifthFactorRight fifthFactor_normal
      (fun | 0 => F | 1 => E | 2 => A | 3 => X | 4 => B | _ => C))

theorem fifthBoxRatio (F E A X B C : Q')
    (hEF : E <= F) (hAE : A <= E) (hXA : X <= A)
    (hBX : B <= X) (hCB : C <= B) (hC0 : (0 : Q') <= C) :
    (X * X + (A * B + (A * B + B * B))) +
        ((E * C + X * C) + ((E * C + X * C) + C * C)) <=
      threeFourths *
        (((A * X + A * X) + ((E * B + X * B) + (E * B + X * B))) +
          (((F * C + A * C) + B * C) + ((F * C + A * C) + B * C))) := by
  let U := (X * X + (A * B + (A * B + B * B))) +
    ((E * C + X * C) + ((E * C + X * C) + C * C))
  let V := ((A * X + A * X) + ((E * B + X * B) + (E * B + X * B))) +
    (((F * C + A * C) + B * C) + ((F * C + A * C) + B * C))
  let dF := F + -E
  let dE := E + -A
  let dA := A + -X
  let dX := X + -B
  let dB := B + -C
  let slack := Q'.ofNat 6 * C * dB +
    (Q'.ofNat 4 * C * dX +
      (Q'.ofNat 8 * C * dA +
        (Q'.ofNat 4 * C * dE +
          (Q'.ofNat 6 * C * dF +
            (Q'.ofNat 2 * (dB * dB) +
              (Q'.ofNat 8 * dB * dX +
                (Q'.ofNat 4 * dB * dA +
                  (Q'.ofNat 6 * dB * dE +
                    (Q'.ofNat 2 * (dX * dX) +
                      Q'.ofNat 6 * dX * dA)))))))))
  have hdF0 : (0 : Q') <= dF := by simpa only [dF] using Q'.sub_nonneg_of_le hEF
  have hdE0 : (0 : Q') <= dE := by simpa only [dE] using Q'.sub_nonneg_of_le hAE
  have hdA0 : (0 : Q') <= dA := by simpa only [dA] using Q'.sub_nonneg_of_le hXA
  have hdX0 : (0 : Q') <= dX := by simpa only [dX] using Q'.sub_nonneg_of_le hBX
  have hdB0 : (0 : Q') <= dB := by simpa only [dB] using Q'.sub_nonneg_of_le hCB
  have h6CdB : (0 : Q') <= Q'.ofNat 6 * C * dB :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdB0
  have h4CdX : (0 : Q') <= Q'.ofNat 4 * C * dX :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdX0
  have h8CdA : (0 : Q') <= Q'.ofNat 8 * C * dA :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdA0
  have h4CdE : (0 : Q') <= Q'.ofNat 4 * C * dE :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdE0
  have h6CdF : (0 : Q') <= Q'.ofNat 6 * C * dF :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdF0
  have h2dB2 : (0 : Q') <= Q'.ofNat 2 * (dB * dB) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hdB0 hdB0)
  have h8dBdX : (0 : Q') <= Q'.ofNat 8 * dB * dX :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdB0) hdX0
  have h4dBdA : (0 : Q') <= Q'.ofNat 4 * dB * dA :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdB0) hdA0
  have h6dBdE : (0 : Q') <= Q'.ofNat 6 * dB * dE :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdB0) hdE0
  have h2dX2 : (0 : Q') <= Q'.ofNat 2 * (dX * dX) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hdX0 hdX0)
  have h6dXdA : (0 : Q') <= Q'.ofNat 6 * dX * dA :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdX0) hdA0
  have hslack0 : (0 : Q') <= slack := by
    have htail0 := add_nonneg h2dX2 h6dXdA
    have htail1 := add_nonneg h6dBdE htail0
    have htail2 := add_nonneg h4dBdA htail1
    have htail3 := add_nonneg h8dBdX htail2
    have htail4 := add_nonneg h2dB2 htail3
    have htail5 := add_nonneg h6CdF htail4
    have htail6 := add_nonneg h4CdE htail5
    have htail7 := add_nonneg h8CdA htail6
    have htail8 := add_nonneg h4CdX htail7
    exact add_nonneg h6CdB htail8
  have hquarterSlack0 : (0 : Q') <= oneFourth * slack :=
    Q'.mul_nonneg _ _ (by decide) hslack0
  have hfactor : threeFourths * V ≈ U + oneFourth * slack := by
    have h34 : threeFourths ≈ Q'.ofNat 3 * oneFourth := by
      unfold threeFourths oneFourth
      ring_qeqv
    have h14 : oneFourth * Q'.ofNat 4 ≈ (1 : Q') := by
      unfold oneFourth
      ring_qeqv
    have hcore : Q'.ofNat 3 * V ≈ Q'.ofNat 4 * U + slack := by
      simpa only [U, V, slack, dF, dE, dA, dX, dB] using
        fifth_factor_core F E A X B C
    refine Q'.eqv_trans _ ((Q'.ofNat 3 * oneFourth) * V) _
      (Q'.mul_eqv_congr_right _ _ V h34) ?_
    refine Q'.eqv_trans _ (oneFourth * (Q'.ofNat 3 * V)) _ ?_ ?_
    · refine Q'.eqv_trans _ ((oneFourth * Q'.ofNat 3) * V) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ V
          (Q'.mul_comm_eqv (Q'.ofNat 3) oneFourth)
      · exact Q'.mul_assoc_eqv oneFourth (Q'.ofNat 3) V
    · refine Q'.eqv_trans _ (oneFourth * (Q'.ofNat 4 * U + slack)) _
        (Q'.mul_eqv_congr_left oneFourth _ _ hcore) ?_
      refine Q'.eqv_trans _
        (oneFourth * (Q'.ofNat 4 * U) + oneFourth * slack) _
        (Q'.mul_add_eqv oneFourth (Q'.ofNat 4 * U) slack) ?_
      refine Q'.add_eqv_congr_right _ _ (oneFourth * slack) ?_
      refine Q'.eqv_trans _ ((oneFourth * Q'.ofNat 4) * U) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv oneFourth (Q'.ofNat 4) U)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * U) _
        (Q'.mul_eqv_congr_right _ _ U h14) ?_
      exact Q'.one_mul_eqv U
  have hbase : U <= U + oneFourth * slack :=
    Q'.add_le_self_of_nonneg U (oneFourth * slack) hquarterSlack0
  change U <= threeFourths * V
  exact Q'.le_trans' _ _ _ hbase (Q'.ge_of_eqv hfactor)

/-! ## 3. Physical `3/4` floor and fifth endpoint descent -/

private theorem physical_four_times_fifth_exponent_cleared (r : Nat) :
    4 * (2 * blockNcut (r + 4) - 3) <= physicalWeightDen (r + 4) := by
  let N := blockNcut (r + 4)
  let D := physicalWeightDen (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hcoord := physicalWeightDen_cutoff_square (r + 4)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have h17 : 17 <= N := Nat.le_trans (by decide) hN
  have h17N : 17 * N <= N * N := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right N h17
  have hNN : N * N <= (N + 1) * (N + 1) :=
    Nat.mul_le_mul (Nat.le_succ N) (Nat.le_succ N)
  have hpoly : 25 * (4 * (2 * N - 3)) <= 12 * (N + 1) * (N + 1) := by
    calc
      25 * (4 * (2 * N - 3)) <= 200 * N := by omega
      _ <= 204 * N := by omega
      _ = 12 * (17 * N) := by omega
      _ <= 12 * (N * N) := Nat.mul_le_mul_left 12 h17N
      _ <= 12 * ((N + 1) * (N + 1)) := Nat.mul_le_mul_left 12 hNN
      _ = 12 * (N + 1) * (N + 1) := by ac_rfl
  have hscaled : 25 * (4 * (2 * N - 3)) <= 25 * D := by
    rw [hcoord]
    exact hpoly
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

private theorem scaled_recip_le_quarter (n D : Nat) (hD : 0 < D)
    (h : 4 * n <= D) :
    Q'.ofNat n * Q'.mkPos 1 D hD <= oneFourth := by
  show (Q'.ofNat n * Q'.mkPos 1 D hD).num * (oneFourth.den : Int) <=
    oneFourth.num * ((Q'.ofNat n * Q'.mkPos 1 D hD).den : Int)
  unfold oneFourth
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  push_cast
  exact_mod_cast (by simpa only [Nat.mul_comm] using h)

theorem physical_threeFourths_power_floor_fifth (r : Nat) :
    threeFourths <=
      qpow (blockWeight (r + 4)) (2 * blockNcut (r + 4) - 3) := by
  let k := r + 4
  let N := blockNcut k
  let D := physicalWeightDen k
  let n := 2 * N - 3
  let loss := Q'.ofNat n * ((1 : Q') - blockWeight k)
  have hmargin : ((1 : Q') - blockWeight k) ≈
      Q'.mkPos 1 D (physicalWeightDen_pos k) :=
    Q'.eqv_trans _ _ _ (one_sub_blockWeight_eqv_margin k)
      (blockMargin_eqv_closed k)
  have hlossClosed : loss ≈
      Q'.ofNat n * Q'.mkPos 1 D (physicalWeightDen_pos k) :=
    Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hmargin
  have hloss : loss <= oneFourth :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hlossClosed)
      (scaled_recip_le_quarter n D (physicalWeightDen_pos k) (by
        simpa only [k, N, D, n] using
          physical_four_times_fifth_exponent_cleared r))
  have hsum : threeFourths + loss <= (1 : Q') := by
    have h := Q'.add_le_add_left threeFourths _ _ hloss
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by
      unfold threeFourths oneFourth
      decide))
  have hsub : threeFourths <= (1 : Q') - loss := by
    have hs := Q'.add_le_add_right _ _ (-loss) hsum
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hs
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv threeFourths loss (-loss)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left threeFourths _ 0 (Q'.add_neg_self_eqv loss)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' threeFourths)
  have hbern := MovingCutoff.qpow_ge_bernoulli
    (blockWeight_nonneg k) (blockWeight_le_one k) n
  exact Q'.le_trans' _ _ _ hsub (by simpa only [loss] using hbern)

private theorem physical_margin_cleared_fifth (r : Nat) :
    let N := blockNcut (r + 4)
    physicalWeightDen (r + 4) <= (N - 4) * (2 * N - 7) := by
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
  have hsquare : (N + 1) * (N + 1) <= (N - 4) * (2 * N - 7) := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 4 := ⟨N - 4, by omega⟩
    have hM13 : 13 <= M := by omega
    have h13M : 13 * M <= M * M := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right M hM13
    rw [hM]
    have htwo : 2 * (M + 4) - 7 = 2 * M + 1 := by omega
    rw [htwo]
    simp only [Nat.add_sub_cancel, Nat.mul_add,
      Nat.mul_one, Nat.one_mul, Nat.mul_comm]
    have hmm : M * (M * 2) = 2 * (M * M) := by ac_rfl
    rw [hmm]
    omega
  exact Nat.le_trans hD hsquare

theorem physical_fifth_coeff_descending (r : Nat) :
    coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 4) <=
      coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 5) := by
  let N := blockNcut (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hp0 : Q'.ofNat (N - 4 + 1) *
      qpow (blockWeight (r + 4)) (2 * N - 7) <= Q'.ofNat (N - 4) :=
    physical_power_upper_step r (N - 4) (2 * N - 7) (by
      simpa only [N] using physical_margin_cleared_fifth r)
  have hp : Q'.ofNat (N - 3) *
      qpow (blockWeight (r + 4)) (2 * N - 7) <=
        (1 : Q') * Q'.ofNat (N - 4) := by
    have hp1 : Q'.ofNat (N - 3) *
        qpow (blockWeight (r + 4)) (2 * N - 7) <= Q'.ofNat (N - 4) := by
      simpa only [show N - 4 + 1 = N - 3 by omega] using hp0
    exact Q'.le_trans' _ _ _ hp1 (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have hs := coeffW_succ_le_of_cross
    (w := blockWeight (r + 4)) (R := (1 : Q')) (N - 5)
    (blockWeight_nonneg (r + 4)) (by
      simpa only [show N - 5 + 2 = N - 3 by omega,
        show 2 * (N - 5) + 3 = 2 * N - 7 by omega] using hp)
  have hs' : coeffW (blockWeight (r + 4)) (N - 4) <=
      (1 : Q') * coeffW (blockWeight (r + 4)) (N - 5) := by
    simpa only [show N - 5 + 1 = N - 4 by omega] using hs
  exact Q'.le_trans' _ _ _ hs' (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-! ## 4. Physical half-time scalar and exact transport -/

theorem fifthHalfTimeScalar (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 5 <= N)
    (hpow : threeFourths <= qpow w (2 * N - 3))
    (hEF : coeffW w (N - 4) <= coeffW w (N - 5))
    (hAE : coeffW w (N - 3) <= coeffW w (N - 4))
    (hXA : coeffW w (N - 2) <= coeffW w (N - 3))
    (hBX : coeffW w (N - 1) <= coeffW w (N - 2))
    (hCB : coeffW w N <= coeffW w (N - 1)) :
    dimQ (2 * N - 5) *
        (((coeffW w (N - 2) * coeffW w (N - 2)) +
          ((coeffW w (N - 3) * coeffW w (N - 1)) +
            ((coeffW w (N - 3) * coeffW w (N - 1)) +
              coeffW w (N - 1) * coeffW w (N - 1)))) +
        ((coeffW w (N - 4) * coeffW w N +
            coeffW w (N - 2) * coeffW w N) +
          ((coeffW w (N - 4) * coeffW w N +
              coeffW w (N - 2) * coeffW w N) +
            coeffW w N * coeffW w N))) <=
      qpow w (2 * N - 3) *
        (dimQ (2 * N - 4) *
          ((((coeffW w (N - 3) * coeffW w (N - 2)) +
              (coeffW w (N - 3) * coeffW w (N - 2))) +
            ((coeffW w (N - 4) * coeffW w (N - 1) +
                coeffW w (N - 2) * coeffW w (N - 1)) +
              (coeffW w (N - 4) * coeffW w (N - 1) +
                coeffW w (N - 2) * coeffW w (N - 1)))) +
          (((coeffW w (N - 5) * coeffW w N +
                coeffW w (N - 3) * coeffW w N) +
              coeffW w (N - 1) * coeffW w N) +
            ((coeffW w (N - 5) * coeffW w N +
                coeffW w (N - 3) * coeffW w N) +
              coeffW w (N - 1) * coeffW w N)))) := by
  let F := coeffW w (N - 5)
  let E := coeffW w (N - 4)
  let A := coeffW w (N - 3)
  let X := coeffW w (N - 2)
  let B := coeffW w (N - 1)
  let C := coeffW w N
  let U := (X * X + (A * B + (A * B + B * B))) +
    ((E * C + X * C) + ((E * C + X * C) + C * C))
  let V := ((A * X + A * X) + ((E * B + X * B) + (E * B + X * B))) +
    (((F * C + A * C) + B * C) + ((F * C + A * C) + B * C))
  let low := dimQ (2 * N - 5)
  let high := dimQ (2 * N - 4)
  have hF0 : (0 : Q') <= F := coeffW_nonneg hw0 (N - 5)
  have hE0 : (0 : Q') <= E := coeffW_nonneg hw0 (N - 4)
  have hA0 : (0 : Q') <= A := coeffW_nonneg hw0 (N - 3)
  have hX0 : (0 : Q') <= X := coeffW_nonneg hw0 (N - 2)
  have hB0 : (0 : Q') <= B := coeffW_nonneg hw0 (N - 1)
  have hC0 : (0 : Q') <= C := coeffW_nonneg hw0 N
  have hU0 : (0 : Q') <= U := by
    dsimp only [U]
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
  have hV0 : (0 : Q') <= V := by
    dsimp only [V]
    exact add_nonneg
      (add_nonneg
        (add_nonneg (Q'.mul_nonneg _ _ hA0 hX0)
          (Q'.mul_nonneg _ _ hA0 hX0))
        (add_nonneg
          (add_nonneg (Q'.mul_nonneg _ _ hE0 hB0)
            (Q'.mul_nonneg _ _ hX0 hB0))
          (add_nonneg (Q'.mul_nonneg _ _ hE0 hB0)
            (Q'.mul_nonneg _ _ hX0 hB0))))
      (add_nonneg
        (add_nonneg
          (add_nonneg (Q'.mul_nonneg _ _ hF0 hC0)
            (Q'.mul_nonneg _ _ hA0 hC0))
          (Q'.mul_nonneg _ _ hB0 hC0))
        (add_nonneg
          (add_nonneg (Q'.mul_nonneg _ _ hF0 hC0)
            (Q'.mul_nonneg _ _ hA0 hC0))
          (Q'.mul_nonneg _ _ hB0 hC0)))
  have hratio : U <= threeFourths * V := by
    simpa only [F, E, A, X, B, C, U, V] using
      fifthBoxRatio F E A X B C hEF hAE hXA hBX hCB hC0
  have hdim : low <= high := by
    have hnat : 2 * N - 5 + 1 <= 2 * N - 4 + 1 := by omega
    simpa only [low, high, dimQ] using ofNat_le_ofNat hnat
  have hdimScaled : low * U <= high * U :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdim hU0
  have hhigh0 : (0 : Q') <= high := by
    unfold high dimQ
    exact HeatKernelRGStep.zero_le_ofNat _
  have hratioScaled : high * U <= high * (threeFourths * V) :=
    Q'.mul_le_mul_of_nonneg_left _ _ high hratio hhigh0
  have hreorder : high * (threeFourths * V) ≈ threeFourths * (high * V) := by
    ring_qeqv
  have hhighV0 : (0 : Q') <= high * V := Q'.mul_nonneg _ _ hhigh0 hV0
  have hpowScaled : threeFourths * (high * V) <=
      qpow w (2 * N - 3) * (high * V) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hhighV0
  change low * U <= qpow w (2 * N - 3) * (high * V)
  exact Q'.le_trans' _ _ _ hdimScaled
    (Q'.le_trans' _ _ _ hratioScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hpowScaled))

theorem halfTimeBox_fifth_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 5) * boxSum (blockWeight k) N (2 * N - 4) <=
      qpow (blockWeight k) (2 * N - 3) *
        (dimQ (2 * N - 4) * boxSum (blockWeight k) N (2 * N - 5)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hN : 5 <= N := Nat.le_trans (by decide : 5 <= 79) (by
    simpa only [k, N] using blockNcut_ge_79 r)
  have hscalar := fifthHalfTimeScalar w N
    (blockWeight_nonneg k) hN
    (by simpa only [k, N, w] using physical_threeFourths_power_floor_fifth r)
    (by simpa only [k, N, w] using physical_fifth_coeff_descending r)
    (by simpa only [k, N, w] using physical_fourth_coeff_descending r)
    (by simpa only [k, N, w] using physical_prepenultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_penultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_terminal_coeff_descending_from_four r)
  have eleft :
      dimQ (2 * N - 5) * boxSum w N (2 * N - 4) ≈
        dimQ (2 * N - 5) *
          (((coeffW w (N - 2) * coeffW w (N - 2)) +
            ((coeffW w (N - 3) * coeffW w (N - 1)) +
              ((coeffW w (N - 3) * coeffW w (N - 1)) +
                coeffW w (N - 1) * coeffW w (N - 1)))) +
          ((coeffW w (N - 4) * coeffW w N +
              coeffW w (N - 2) * coeffW w N) +
            ((coeffW w (N - 4) * coeffW w N +
                coeffW w (N - 2) * coeffW w N) +
              coeffW w N * coeffW w N))) :=
    Q'.mul_eqv_congr_left _ _ _ (boxSum_top_four w N (by omega))
  have eright :
      qpow w (2 * N - 3) *
          (dimQ (2 * N - 4) *
            ((((coeffW w (N - 3) * coeffW w (N - 2)) +
                (coeffW w (N - 3) * coeffW w (N - 2))) +
              ((coeffW w (N - 4) * coeffW w (N - 1) +
                  coeffW w (N - 2) * coeffW w (N - 1)) +
                (coeffW w (N - 4) * coeffW w (N - 1) +
                  coeffW w (N - 2) * coeffW w (N - 1)))) +
            (((coeffW w (N - 5) * coeffW w N +
                  coeffW w (N - 3) * coeffW w N) +
                coeffW w (N - 1) * coeffW w N) +
              ((coeffW w (N - 5) * coeffW w N +
                  coeffW w (N - 3) * coeffW w N) +
                coeffW w (N - 1) * coeffW w N)))) ≈
        qpow w (2 * N - 3) *
          (dimQ (2 * N - 4) * boxSum w N (2 * N - 5)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (boxSum_top_five w N hN)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hscalar (Q'.le_of_eqv eright))

theorem halfTimeLineSum_fifth_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 5) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 4) <=
      qpow (blockWeight k) (2 * N - 3) *
        (dimQ (2 * N - 4) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 5)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hbox := halfTimeBox_fifth_physical r
  have eleft :
      dimQ (2 * N - 5) * lineSum (lagCorr w N) (2 * N - 4) ≈
        dimQ (2 * N - 5) * boxSum w N (2 * N - 4) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (2 * N - 4)))
  have eright :
      qpow w (2 * N - 3) *
          (dimQ (2 * N - 4) * boxSum w N (2 * N - 5)) ≈
        qpow w (2 * N - 3) *
          (dimQ (2 * N - 4) * lineSum (lagCorr w N) (2 * N - 5)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N (2 * N - 5)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ (by simpa only [k, N, w] using hbox)
      (Q'.le_of_eqv eright))

theorem physical_halfTime_lineSum_fifth_from_four (k : Nat) (hk : 4 <= k) :
    let N := blockNcut k
    dimQ (2 * N - 5) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 4) <=
      qpow (blockWeight k) (2 * N - 3) *
        (dimQ (2 * N - 4) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 5)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using halfTimeLineSum_fifth_physical r

end YMGap.Continuum.P2HalfTimeFifthShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeFifthShell.boxSumDelta_top_five
#print axioms YMGap.Continuum.P2HalfTimeFifthShell.boxSum_top_five
#print axioms YMGap.Continuum.P2HalfTimeFifthShell.fifthBoxRatio
#print axioms YMGap.Continuum.P2HalfTimeFifthShell.physical_threeFourths_power_floor_fifth
#print axioms YMGap.Continuum.P2HalfTimeFifthShell.physical_fifth_coeff_descending
#print axioms YMGap.Continuum.P2HalfTimeFifthShell.fifthHalfTimeScalar
#print axioms YMGap.Continuum.P2HalfTimeFifthShell.halfTimeBox_fifth_physical
#print axioms YMGap.Continuum.P2HalfTimeFifthShell.halfTimeLineSum_fifth_physical
#print axioms YMGap.Continuum.P2HalfTimeFifthShell.physical_halfTime_lineSum_fifth_from_four
