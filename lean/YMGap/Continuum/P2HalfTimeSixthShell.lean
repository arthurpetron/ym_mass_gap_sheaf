/-
Track 11.7-fusion / R4r -- exact sixth half-time boundary shell.

At channel `s = 2*N-6`, the adjacent Clebsch boxes have twelve and
sixteen endpoint pairs.  Their equal-coefficient ratio is sharply `3/4`.
For a descending endpoint string

    G >= F >= E >= A >= X >= B >= C,

the cleared difference `3*W - 4*V` is a sum of fourteen nonnegative
increment products.  This file checks that identity with the reflective
polynomial normalizer, proves the physical heat and coefficient payments,
and transports the result to the exact line-sum carrier.  No growing
convolution is evaluated.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeFifthShell
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.P2HalfTimeSixthShell

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
open YMGap.Continuum.P2HalfTimeFifthShell
open YMGap.Continuum.P2HalfTimeFourthShell
open YMGap.Continuum.P2HalfTimePenultimateShell
open YMGap.Continuum.P2RetunedFenceSecondShell
open YMGap.Continuum.P2RetunedFenceThirdShell
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

/-! ## 1. Exact sixteen-pair endpoint support -/

private theorem fusionInd_comm (a b s : Nat) :
    fusionInd a b s = fusionInd b a s := by
  unfold fusionInd
  rw [fusionOK_symm_ab]

private theorem fusionInd_top_six_low (N : Nat) (hN : 6 <= N) :
    fusionInd (N - 6) N (2 * N - 6) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 6) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 6) N = N - 6 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 6 + N + (2 * N - 6) = 2 * (2 * N - 6) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 6), Nat.mul_mod_left]

private theorem fusionInd_top_six_mid (N : Nat) (hN : 6 <= N) :
    fusionInd (N - 4) N (2 * N - 6) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 4) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 4) N = N - 4 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 4 + N + (2 * N - 6) = 2 * (2 * N - 5) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 5), Nat.mul_mod_left]

private theorem fusionInd_top_six_high (N : Nat) (hN : 6 <= N) :
    fusionInd (N - 2) N (2 * N - 6) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 2) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 2) N = N - 2 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 2 + N + (2 * N - 6) = 2 * (2 * N - 4) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 4), Nat.mul_mod_left]

private theorem fusionInd_top_six_diag (N : Nat) (hN : 6 <= N) :
    fusionInd N N (2 * N - 6) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  simp only [Nat.max_self, Nat.min_self]
  refine ⟨by omega, by omega, ?_⟩
  have he : N + N + (2 * N - 6) = 2 * (2 * N - 3) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 3), Nat.mul_mod_left]

private theorem fusionInd_top_six_zero_other
    (N a : Nat) (hN : 6 <= N) (ha : a < N)
    (hne6 : a ≠ N - 6) (hne4 : a ≠ N - 4) (hne2 : a ≠ N - 2) :
    fusionInd a N (2 * N - 6) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff a N (2 * N - 6)).mp hok with
    ⟨_, hhi, hp⟩
  have halow : N - 6 <= a := by omega
  have hcases : a = N - 6 ∨ a = N - 5 ∨ a = N - 4 ∨
      a = N - 3 ∨ a = N - 2 ∨ a = N - 1 := by omega
  rcases hcases with h | h | h | h | h | h
  · exact hne6 h
  · subst a; omega
  · exact hne4 h
  · subst a; omega
  · exact hne2 h
  · subst a; omega

private theorem topSixRow (w : Q') (N : Nat) (hN : 6 <= N) :
    fsum (fun a => fusionInd a N (2 * N - 6) *
      (coeffW w a * coeffW w N)) N ≈
      (coeffW w (N - 6) * coeffW w N +
        coeffW w (N - 4) * coeffW w N) +
      coeffW w (N - 2) * coeffW w N := by
  let g := fun a => fusionInd a N (2 * N - 6) *
    (coeffW w a * coeffW w N)
  have hsplit : fsum g N =
      ((((((fsum g (N - 6) + g (N - 6)) + g (N - 5)) + g (N - 4)) +
        g (N - 3)) + g (N - 2)) + g (N - 1)) := by
    rw [show N = (N - 6) + 6 by omega]
    rfl
  rw [hsplit]
  have hpre : fsum g (N - 6) ≈ (0 : Q') := by
    apply fsum_zero_below
    intro a ha
    dsimp only [g]
    rw [fusionInd_top_six_zero_other N a hN (by omega)
      (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h6 : g (N - 6) ≈ coeffW w (N - 6) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_six_low N hN]
    exact Q'.one_mul_eqv _
  have h5 : g (N - 5) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_six_zero_other N (N - 5) hN (by omega)
      (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h4 : g (N - 4) ≈ coeffW w (N - 4) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_six_mid N hN]
    exact Q'.one_mul_eqv _
  have h3 : g (N - 3) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_six_zero_other N (N - 3) hN (by omega)
      (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h2 : g (N - 2) ≈ coeffW w (N - 2) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_six_high N hN]
    exact Q'.one_mul_eqv _
  have h1 : g (N - 1) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_six_zero_other N (N - 1) hN (by omega)
      (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  let M := ((((((0 : Q') + coeffW w (N - 6) * coeffW w N) + 0) +
    coeffW w (N - 4) * coeffW w N) + 0) +
    coeffW w (N - 2) * coeffW w N) + 0
  refine Q'.eqv_trans _ M _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr' hpre h6) h5) h4) h3) h2) h1
  · dsimp only [M]
    ring_qeqv

theorem boxSumDelta_top_six (w : Q') (N : Nat) (hN : 6 <= N) :
    boxSumDelta w (N - 1) (2 * N - 6) ≈
      ((coeffW w (N - 6) * coeffW w N +
          coeffW w (N - 4) * coeffW w N) +
        coeffW w (N - 2) * coeffW w N) +
      (((coeffW w (N - 6) * coeffW w N +
          coeffW w (N - 4) * coeffW w N) +
        coeffW w (N - 2) * coeffW w N) +
        coeffW w N * coeffW w N) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft := topSixRow w N hN
  have hright0 := topSixRow w N hN
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 6) *
        (coeffW w N * coeffW w b)) N ≈
        (coeffW w (N - 6) * coeffW w N +
          coeffW w (N - 4) * coeffW w N) +
        coeffW w (N - 2) * coeffW w N := by
    refine Q'.eqv_trans _ _ _ ?_ hright0
    apply CubeRatioBounds.fsum_eqv_congr
    intro b
    rw [fusionInd_comm N b (2 * N - 6)]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
  rw [fusionInd_top_six_diag N hN]
  exact Q'.add_eqv_congr' hleft
    (Q'.add_eqv_congr' hright (Q'.one_mul_eqv _))

/-- Channel `2*N-6` has exactly sixteen Clebsch pairs. -/
theorem boxSum_top_six (w : Q') (N : Nat) (hN : 6 <= N) :
    boxSum w N (2 * N - 6) ≈
      (((coeffW w (N - 3) * coeffW w (N - 3)) +
          ((coeffW w (N - 4) * coeffW w (N - 2)) +
            ((coeffW w (N - 4) * coeffW w (N - 2)) +
              coeffW w (N - 2) * coeffW w (N - 2)))) +
        ((coeffW w (N - 5) * coeffW w (N - 1) +
            coeffW w (N - 3) * coeffW w (N - 1)) +
          ((coeffW w (N - 5) * coeffW w (N - 1) +
              coeffW w (N - 3) * coeffW w (N - 1)) +
            coeffW w (N - 1) * coeffW w (N - 1)))) +
      (((coeffW w (N - 6) * coeffW w N +
          coeffW w (N - 4) * coeffW w N) +
        coeffW w (N - 2) * coeffW w N) +
       (((coeffW w (N - 6) * coeffW w N +
          coeffW w (N - 4) * coeffW w N) +
        coeffW w (N - 2) * coeffW w N) +
        coeffW w N * coeffW w N)) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 6)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold := boxSum_top_four w (N - 1) (by omega)
  rw [show 2 * (N - 1) - 4 = 2 * N - 6 by omega] at hold
  simpa only [
    show N - 1 - 2 = N - 3 by omega,
    show N - 1 - 3 = N - 4 by omega,
    show N - 1 - 1 = N - 2 by omega,
    show N - 1 - 4 = N - 5 by omega] using
    (Q'.add_eqv_congr' hold (boxSumDelta_top_six w N hN))

/-! ## 2. Reflected sharp `3/4` ratio -/

private def sixthFactorLeft : RingNormaliser.PolyExpr :=
  let G := RingNormaliser.PolyExpr.var 0
  let F := RingNormaliser.PolyExpr.var 1
  let E := RingNormaliser.PolyExpr.var 2
  let A := RingNormaliser.PolyExpr.var 3
  let X := RingNormaliser.PolyExpr.var 4
  let B := RingNormaliser.PolyExpr.var 5
  let C := RingNormaliser.PolyExpr.var 6
  let W :=
    .add
      (.add
        (.add (.mul A A)
          (.add (.mul E X) (.add (.mul E X) (.mul X X))))
        (.add (.add (.mul F B) (.mul A B))
          (.add (.add (.mul F B) (.mul A B)) (.mul B B))))
      (.add (.add (.add (.mul G C) (.mul E C)) (.mul X C))
        (.add (.add (.add (.mul G C) (.mul E C)) (.mul X C))
          (.mul C C)))
  .mul (.const 3) W

private def sixthFactorRight : RingNormaliser.PolyExpr :=
  let G := RingNormaliser.PolyExpr.var 0
  let F := RingNormaliser.PolyExpr.var 1
  let E := RingNormaliser.PolyExpr.var 2
  let A := RingNormaliser.PolyExpr.var 3
  let X := RingNormaliser.PolyExpr.var 4
  let B := RingNormaliser.PolyExpr.var 5
  let C := RingNormaliser.PolyExpr.var 6
  let V :=
    .add
      (.add (.add (.mul A X) (.mul A X))
        (.add (.add (.mul E B) (.mul X B))
          (.add (.mul E B) (.mul X B))))
      (.add (.add (.add (.mul F C) (.mul A C)) (.mul B C))
        (.add (.add (.mul F C) (.mul A C)) (.mul B C)))
  let dG := .add G (.neg F)
  let dF := .add F (.neg E)
  let dE := .add E (.neg A)
  let dA := .add A (.neg X)
  let dX := .add X (.neg B)
  let dB := .add B (.neg C)
  let slack :=
    .add (.mul (.mul (.const 6) C) dX)
      (.add (.mul (.mul (.const 4) C) dA)
        (.add (.mul (.mul (.const 8) C) dE)
          (.add (.mul (.mul (.const 4) C) dF)
            (.add (.mul (.mul (.const 6) C) dG)
              (.add (.mul (.const 3) (.mul dB dB))
                (.add (.mul (.mul (.const 4) dB) dX)
                  (.add (.mul (.mul (.const 8) dB) dA)
                    (.add (.mul (.mul (.const 4) dB) dE)
                      (.add (.mul (.mul (.const 6) dB) dF)
                        (.add (.mul (.const 4) (.mul dX dX))
                          (.add (.mul (.mul (.const 4) dX) dA)
                            (.add (.mul (.mul (.const 6) dX) dE)
                              (.mul (.const 3) (.mul dA dA))))))))))))))
  .add (.mul (.const 4) V) slack

private theorem sixthFactor_normal :
    RingNormaliser.normalize sixthFactorLeft =
      RingNormaliser.normalize sixthFactorRight := by decide

private theorem sixth_factor_core (G F E A X B C : Q') :
    Q'.ofNat 3 *
        ((((A * A + (E * X + (E * X + X * X))) +
            ((F * B + A * B) + ((F * B + A * B) + B * B))) +
          (((G * C + E * C) + X * C) +
            (((G * C + E * C) + X * C) + C * C)))) ≈
      Q'.ofNat 4 *
          (((A * X + A * X) + ((E * B + X * B) + (E * B + X * B))) +
            (((F * C + A * C) + B * C) + ((F * C + A * C) + B * C))) +
        (Q'.ofNat 6 * C * (X + -B) +
          (Q'.ofNat 4 * C * (A + -X) +
            (Q'.ofNat 8 * C * (E + -A) +
              (Q'.ofNat 4 * C * (F + -E) +
                (Q'.ofNat 6 * C * (G + -F) +
                  (Q'.ofNat 3 * ((B + -C) * (B + -C)) +
                    (Q'.ofNat 4 * (B + -C) * (X + -B) +
                      (Q'.ofNat 8 * (B + -C) * (A + -X) +
                        (Q'.ofNat 4 * (B + -C) * (E + -A) +
                          (Q'.ofNat 6 * (B + -C) * (F + -E) +
                            (Q'.ofNat 4 * ((X + -B) * (X + -B)) +
                              (Q'.ofNat 4 * (X + -B) * (A + -X) +
                                (Q'.ofNat 6 * (X + -B) * (E + -A) +
                                  Q'.ofNat 3 * ((A + -X) * (A + -X))))))))))))))) := by
  simpa [sixthFactorLeft, sixthFactorRight, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      sixthFactorLeft sixthFactorRight sixthFactor_normal
      (fun | 0 => G | 1 => F | 2 => E | 3 => A | 4 => X | 5 => B | _ => C))

theorem sixthBoxRatio (G F E A X B C : Q')
    (hFG : F <= G) (hEF : E <= F) (hAE : A <= E)
    (hXA : X <= A) (hBX : B <= X) (hCB : C <= B)
    (hC0 : (0 : Q') <= C) :
    ((A * X + A * X) + ((E * B + X * B) + (E * B + X * B))) +
        (((F * C + A * C) + B * C) + ((F * C + A * C) + B * C)) <=
      threeFourths *
        (((A * A + (E * X + (E * X + X * X))) +
            ((F * B + A * B) + ((F * B + A * B) + B * B))) +
          (((G * C + E * C) + X * C) +
            (((G * C + E * C) + X * C) + C * C))) := by
  let V := ((A * X + A * X) + ((E * B + X * B) + (E * B + X * B))) +
    (((F * C + A * C) + B * C) + ((F * C + A * C) + B * C))
  let W := ((A * A + (E * X + (E * X + X * X))) +
      ((F * B + A * B) + ((F * B + A * B) + B * B))) +
    (((G * C + E * C) + X * C) +
      (((G * C + E * C) + X * C) + C * C))
  let dG := G + -F
  let dF := F + -E
  let dE := E + -A
  let dA := A + -X
  let dX := X + -B
  let dB := B + -C
  let slack := Q'.ofNat 6 * C * dX +
    (Q'.ofNat 4 * C * dA +
      (Q'.ofNat 8 * C * dE +
        (Q'.ofNat 4 * C * dF +
          (Q'.ofNat 6 * C * dG +
            (Q'.ofNat 3 * (dB * dB) +
              (Q'.ofNat 4 * dB * dX +
                (Q'.ofNat 8 * dB * dA +
                  (Q'.ofNat 4 * dB * dE +
                    (Q'.ofNat 6 * dB * dF +
                      (Q'.ofNat 4 * (dX * dX) +
                        (Q'.ofNat 4 * dX * dA +
                          (Q'.ofNat 6 * dX * dE +
                            Q'.ofNat 3 * (dA * dA)))))))))))))
  have hdG0 : (0 : Q') <= dG := by simpa only [dG] using Q'.sub_nonneg_of_le hFG
  have hdF0 : (0 : Q') <= dF := by simpa only [dF] using Q'.sub_nonneg_of_le hEF
  have hdE0 : (0 : Q') <= dE := by simpa only [dE] using Q'.sub_nonneg_of_le hAE
  have hdA0 : (0 : Q') <= dA := by simpa only [dA] using Q'.sub_nonneg_of_le hXA
  have hdX0 : (0 : Q') <= dX := by simpa only [dX] using Q'.sub_nonneg_of_le hBX
  have hdB0 : (0 : Q') <= dB := by simpa only [dB] using Q'.sub_nonneg_of_le hCB
  have h6CdX : (0 : Q') <= Q'.ofNat 6 * C * dX :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdX0
  have h4CdA : (0 : Q') <= Q'.ofNat 4 * C * dA :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdA0
  have h8CdE : (0 : Q') <= Q'.ofNat 8 * C * dE :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdE0
  have h4CdF : (0 : Q') <= Q'.ofNat 4 * C * dF :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdF0
  have h6CdG : (0 : Q') <= Q'.ofNat 6 * C * dG :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hdG0
  have h3dB2 : (0 : Q') <= Q'.ofNat 3 * (dB * dB) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hdB0 hdB0)
  have h4dBdX : (0 : Q') <= Q'.ofNat 4 * dB * dX :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdB0) hdX0
  have h8dBdA : (0 : Q') <= Q'.ofNat 8 * dB * dA :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdB0) hdA0
  have h4dBdE : (0 : Q') <= Q'.ofNat 4 * dB * dE :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdB0) hdE0
  have h6dBdF : (0 : Q') <= Q'.ofNat 6 * dB * dF :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdB0) hdF0
  have h4dX2 : (0 : Q') <= Q'.ofNat 4 * (dX * dX) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hdX0 hdX0)
  have h4dXdA : (0 : Q') <= Q'.ofNat 4 * dX * dA :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdX0) hdA0
  have h6dXdE : (0 : Q') <= Q'.ofNat 6 * dX * dE :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hdX0) hdE0
  have h3dA2 : (0 : Q') <= Q'.ofNat 3 * (dA * dA) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hdA0 hdA0)
  have hslack0 : (0 : Q') <= slack := by
    exact add_nonneg h6CdX
      (add_nonneg h4CdA
        (add_nonneg h8CdE
          (add_nonneg h4CdF
            (add_nonneg h6CdG
              (add_nonneg h3dB2
                (add_nonneg h4dBdX
                  (add_nonneg h8dBdA
                    (add_nonneg h4dBdE
                      (add_nonneg h6dBdF
                        (add_nonneg h4dX2
                          (add_nonneg h4dXdA
                            (add_nonneg h6dXdE h3dA2))))))))))))
  have hquarterSlack0 : (0 : Q') <= oneFourth * slack :=
    Q'.mul_nonneg _ _ (by decide) hslack0
  have hfactor : threeFourths * W ≈ V + oneFourth * slack := by
    have h34 : threeFourths ≈ Q'.ofNat 3 * oneFourth := by
      unfold threeFourths oneFourth
      ring_qeqv
    have h14 : oneFourth * Q'.ofNat 4 ≈ (1 : Q') := by
      unfold oneFourth
      ring_qeqv
    have hcore : Q'.ofNat 3 * W ≈ Q'.ofNat 4 * V + slack := by
      simpa only [V, W, slack, dG, dF, dE, dA, dX, dB] using
        sixth_factor_core G F E A X B C
    refine Q'.eqv_trans _ ((Q'.ofNat 3 * oneFourth) * W) _
      (Q'.mul_eqv_congr_right _ _ W h34) ?_
    refine Q'.eqv_trans _ (oneFourth * (Q'.ofNat 3 * W)) _ ?_ ?_
    · refine Q'.eqv_trans _ ((oneFourth * Q'.ofNat 3) * W) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ W
          (Q'.mul_comm_eqv (Q'.ofNat 3) oneFourth)
      · exact Q'.mul_assoc_eqv oneFourth (Q'.ofNat 3) W
    · refine Q'.eqv_trans _ (oneFourth * (Q'.ofNat 4 * V + slack)) _
        (Q'.mul_eqv_congr_left oneFourth _ _ hcore) ?_
      refine Q'.eqv_trans _
        (oneFourth * (Q'.ofNat 4 * V) + oneFourth * slack) _
        (Q'.mul_add_eqv oneFourth (Q'.ofNat 4 * V) slack) ?_
      refine Q'.add_eqv_congr_right _ _ (oneFourth * slack) ?_
      refine Q'.eqv_trans _ ((oneFourth * Q'.ofNat 4) * V) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv oneFourth (Q'.ofNat 4) V)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * V) _
        (Q'.mul_eqv_congr_right _ _ V h14) ?_
      exact Q'.one_mul_eqv V
  have hbase : V <= V + oneFourth * slack :=
    Q'.add_le_self_of_nonneg V (oneFourth * slack) hquarterSlack0
  change V <= threeFourths * W
  exact Q'.le_trans' _ _ _ hbase (Q'.ge_of_eqv hfactor)

/-! ## 3. Physical heat floor and sixth endpoint descent -/

theorem physical_threeFourths_power_floor_sixth (r : Nat) :
    threeFourths <=
      qpow (blockWeight (r + 4)) (2 * blockNcut (r + 4) - 4) := by
  let N := blockNcut (r + 4)
  have hbase := physical_threeFourths_power_floor_fifth r
  have hmono : qpow (blockWeight (r + 4)) (2 * N - 3) <=
      qpow (blockWeight (r + 4)) (2 * N - 4) :=
    qpow_antitone (blockWeight_nonneg (r + 4))
      (blockWeight_le_one (r + 4)) (2 * N - 4) (2 * N - 3) (by
        have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
        omega)
  exact Q'.le_trans' _ _ _ (by simpa only [N] using hbase) hmono

private theorem physical_margin_cleared_sixth (r : Nat) :
    let N := blockNcut (r + 4)
    physicalWeightDen (r + 4) <= (N - 5) * (2 * N - 9) := by
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
  have hsquare : (N + 1) * (N + 1) <= (N - 5) * (2 * N - 9) := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 5 := ⟨N - 5, by omega⟩
    have hM12 : 12 <= M := by omega
    have h12M : 12 * M <= M * M := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right M hM12
    rw [hM]
    have htwo : 2 * (M + 5) - 9 = 2 * M + 1 := by omega
    rw [htwo]
    simp only [Nat.add_sub_cancel, Nat.mul_add,
      Nat.mul_one, Nat.one_mul, Nat.mul_comm]
    have hmm : M * (M * 2) = 2 * (M * M) := by ac_rfl
    rw [hmm]
    omega
  exact Nat.le_trans hD hsquare

theorem physical_sixth_coeff_descending (r : Nat) :
    coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 5) <=
      coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 6) := by
  let N := blockNcut (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hp0 : Q'.ofNat (N - 5 + 1) *
      qpow (blockWeight (r + 4)) (2 * N - 9) <= Q'.ofNat (N - 5) :=
    physical_power_upper_step r (N - 5) (2 * N - 9) (by
      simpa only [N] using physical_margin_cleared_sixth r)
  have hp : Q'.ofNat (N - 4) *
      qpow (blockWeight (r + 4)) (2 * N - 9) <=
        (1 : Q') * Q'.ofNat (N - 5) := by
    have hp1 : Q'.ofNat (N - 4) *
        qpow (blockWeight (r + 4)) (2 * N - 9) <= Q'.ofNat (N - 5) := by
      simpa only [show N - 5 + 1 = N - 4 by omega] using hp0
    exact Q'.le_trans' _ _ _ hp1 (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have hs := coeffW_succ_le_of_cross
    (w := blockWeight (r + 4)) (R := (1 : Q')) (N - 6)
    (blockWeight_nonneg (r + 4)) (by
      simpa only [show N - 6 + 2 = N - 4 by omega,
        show 2 * (N - 6) + 3 = 2 * N - 9 by omega] using hp)
  have hs' : coeffW (blockWeight (r + 4)) (N - 5) <=
      (1 : Q') * coeffW (blockWeight (r + 4)) (N - 6) := by
    simpa only [show N - 6 + 1 = N - 5 by omega] using hs
  exact Q'.le_trans' _ _ _ hs' (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-! ## 4. Physical half-time scalar and exact transport -/

theorem sixthHalfTimeScalar (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 6 <= N)
    (hpow : threeFourths <= qpow w (2 * N - 4))
    (hGF : coeffW w (N - 5) <= coeffW w (N - 6))
    (hFE : coeffW w (N - 4) <= coeffW w (N - 5))
    (hEA : coeffW w (N - 3) <= coeffW w (N - 4))
    (hAX : coeffW w (N - 2) <= coeffW w (N - 3))
    (hXB : coeffW w (N - 1) <= coeffW w (N - 2))
    (hBC : coeffW w N <= coeffW w (N - 1)) :
    dimQ (2 * N - 6) *
        (((coeffW w (N - 3) * coeffW w (N - 2) +
            coeffW w (N - 3) * coeffW w (N - 2)) +
          ((coeffW w (N - 4) * coeffW w (N - 1) +
              coeffW w (N - 2) * coeffW w (N - 1)) +
            (coeffW w (N - 4) * coeffW w (N - 1) +
              coeffW w (N - 2) * coeffW w (N - 1)))) +
        (((coeffW w (N - 5) * coeffW w N +
              coeffW w (N - 3) * coeffW w N) +
            coeffW w (N - 1) * coeffW w N) +
          ((coeffW w (N - 5) * coeffW w N +
              coeffW w (N - 3) * coeffW w N) +
            coeffW w (N - 1) * coeffW w N))) <=
      qpow w (2 * N - 4) *
        (dimQ (2 * N - 5) *
          ((((coeffW w (N - 3) * coeffW w (N - 3) +
              (coeffW w (N - 4) * coeffW w (N - 2) +
                (coeffW w (N - 4) * coeffW w (N - 2) +
                  coeffW w (N - 2) * coeffW w (N - 2)))) +
            ((coeffW w (N - 5) * coeffW w (N - 1) +
                coeffW w (N - 3) * coeffW w (N - 1)) +
              ((coeffW w (N - 5) * coeffW w (N - 1) +
                  coeffW w (N - 3) * coeffW w (N - 1)) +
                coeffW w (N - 1) * coeffW w (N - 1)))) +
          (((coeffW w (N - 6) * coeffW w N +
                coeffW w (N - 4) * coeffW w N) +
              coeffW w (N - 2) * coeffW w N) +
            (((coeffW w (N - 6) * coeffW w N +
                coeffW w (N - 4) * coeffW w N) +
              coeffW w (N - 2) * coeffW w N) +
              coeffW w N * coeffW w N))))) := by
  let G := coeffW w (N - 6)
  let F := coeffW w (N - 5)
  let E := coeffW w (N - 4)
  let A := coeffW w (N - 3)
  let X := coeffW w (N - 2)
  let B := coeffW w (N - 1)
  let C := coeffW w N
  let V := ((A * X + A * X) + ((E * B + X * B) + (E * B + X * B))) +
    (((F * C + A * C) + B * C) + ((F * C + A * C) + B * C))
  let W := ((A * A + (E * X + (E * X + X * X))) +
      ((F * B + A * B) + ((F * B + A * B) + B * B))) +
    (((G * C + E * C) + X * C) +
      (((G * C + E * C) + X * C) + C * C))
  let low := dimQ (2 * N - 6)
  let high := dimQ (2 * N - 5)
  have hA0 : (0 : Q') <= A := coeffW_nonneg hw0 (N - 3)
  have hX0 : (0 : Q') <= X := coeffW_nonneg hw0 (N - 2)
  have hE0 : (0 : Q') <= E := coeffW_nonneg hw0 (N - 4)
  have hF0 : (0 : Q') <= F := coeffW_nonneg hw0 (N - 5)
  have hG0 : (0 : Q') <= G := coeffW_nonneg hw0 (N - 6)
  have hB0 : (0 : Q') <= B := coeffW_nonneg hw0 (N - 1)
  have hC0 : (0 : Q') <= C := coeffW_nonneg hw0 N
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
  have hW0 : (0 : Q') <= W := by
    dsimp only [W]
    exact add_nonneg
      (add_nonneg
        (add_nonneg (Q'.mul_nonneg _ _ hA0 hA0)
          (add_nonneg (Q'.mul_nonneg _ _ hE0 hX0)
            (add_nonneg (Q'.mul_nonneg _ _ hE0 hX0)
              (Q'.mul_nonneg _ _ hX0 hX0))))
        (add_nonneg
          (add_nonneg (Q'.mul_nonneg _ _ hF0 hB0)
            (Q'.mul_nonneg _ _ hA0 hB0))
          (add_nonneg
            (add_nonneg (Q'.mul_nonneg _ _ hF0 hB0)
              (Q'.mul_nonneg _ _ hA0 hB0))
            (Q'.mul_nonneg _ _ hB0 hB0))))
      (add_nonneg
        (add_nonneg
          (add_nonneg (Q'.mul_nonneg _ _ hG0 hC0)
            (Q'.mul_nonneg _ _ hE0 hC0))
          (Q'.mul_nonneg _ _ hX0 hC0))
        (add_nonneg
          (add_nonneg
            (add_nonneg (Q'.mul_nonneg _ _ hG0 hC0)
              (Q'.mul_nonneg _ _ hE0 hC0))
            (Q'.mul_nonneg _ _ hX0 hC0))
          (Q'.mul_nonneg _ _ hC0 hC0)))
  have hratio : V <= threeFourths * W := by
    simpa only [G, F, E, A, X, B, C, V, W] using
      sixthBoxRatio G F E A X B C hGF hFE hEA hAX hXB hBC hC0
  have hdim : low <= high := by
    have hnat : 2 * N - 6 + 1 <= 2 * N - 5 + 1 := by omega
    simpa only [low, high, dimQ] using ofNat_le_ofNat hnat
  have hdimScaled : low * V <= high * V :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdim hV0
  have hhigh0 : (0 : Q') <= high := by
    unfold high dimQ
    exact HeatKernelRGStep.zero_le_ofNat _
  have hratioScaled : high * V <= high * (threeFourths * W) :=
    Q'.mul_le_mul_of_nonneg_left _ _ high hratio hhigh0
  have hreorder : high * (threeFourths * W) ≈ threeFourths * (high * W) := by
    ring_qeqv
  have hhighW0 : (0 : Q') <= high * W := Q'.mul_nonneg _ _ hhigh0 hW0
  have hpowScaled : threeFourths * (high * W) <=
      qpow w (2 * N - 4) * (high * W) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hhighW0
  change low * V <= qpow w (2 * N - 4) * (high * W)
  exact Q'.le_trans' _ _ _ hdimScaled
    (Q'.le_trans' _ _ _ hratioScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hpowScaled))

theorem halfTimeBox_sixth_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 6) * boxSum (blockWeight k) N (2 * N - 5) <=
      qpow (blockWeight k) (2 * N - 4) *
        (dimQ (2 * N - 5) * boxSum (blockWeight k) N (2 * N - 6)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hN : 6 <= N := Nat.le_trans (by decide : 6 <= 79) (by
    simpa only [k, N] using blockNcut_ge_79 r)
  have hscalar := sixthHalfTimeScalar w N
    (blockWeight_nonneg k) hN
    (by simpa only [k, N, w] using physical_threeFourths_power_floor_sixth r)
    (by simpa only [k, N, w] using physical_sixth_coeff_descending r)
    (by simpa only [k, N, w] using physical_fifth_coeff_descending r)
    (by simpa only [k, N, w] using physical_fourth_coeff_descending r)
    (by simpa only [k, N, w] using physical_prepenultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_penultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_terminal_coeff_descending_from_four r)
  have eleft :
      dimQ (2 * N - 6) * boxSum w N (2 * N - 5) ≈
        dimQ (2 * N - 6) *
          ((((coeffW w (N - 3) * coeffW w (N - 2) +
              coeffW w (N - 3) * coeffW w (N - 2)) +
            ((coeffW w (N - 4) * coeffW w (N - 1) +
                coeffW w (N - 2) * coeffW w (N - 1)) +
              (coeffW w (N - 4) * coeffW w (N - 1) +
                coeffW w (N - 2) * coeffW w (N - 1)))) +
          (((coeffW w (N - 5) * coeffW w N +
                coeffW w (N - 3) * coeffW w N) +
              coeffW w (N - 1) * coeffW w N) +
            ((coeffW w (N - 5) * coeffW w N +
                coeffW w (N - 3) * coeffW w N) +
              coeffW w (N - 1) * coeffW w N)))) :=
    Q'.mul_eqv_congr_left _ _ _ (boxSum_top_five w N (by omega))
  have eright :
      qpow w (2 * N - 4) *
          (dimQ (2 * N - 5) *
            ((((coeffW w (N - 3) * coeffW w (N - 3) +
                (coeffW w (N - 4) * coeffW w (N - 2) +
                  (coeffW w (N - 4) * coeffW w (N - 2) +
                    coeffW w (N - 2) * coeffW w (N - 2)))) +
              ((coeffW w (N - 5) * coeffW w (N - 1) +
                  coeffW w (N - 3) * coeffW w (N - 1)) +
                ((coeffW w (N - 5) * coeffW w (N - 1) +
                    coeffW w (N - 3) * coeffW w (N - 1)) +
                  coeffW w (N - 1) * coeffW w (N - 1)))) +
            (((coeffW w (N - 6) * coeffW w N +
                  coeffW w (N - 4) * coeffW w N) +
                coeffW w (N - 2) * coeffW w N) +
              (((coeffW w (N - 6) * coeffW w N +
                  coeffW w (N - 4) * coeffW w N) +
                coeffW w (N - 2) * coeffW w N) +
                coeffW w N * coeffW w N))))) ≈
        qpow w (2 * N - 4) *
          (dimQ (2 * N - 5) * boxSum w N (2 * N - 6)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (boxSum_top_six w N hN)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hscalar (Q'.le_of_eqv eright))

theorem halfTimeLineSum_sixth_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 6) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 5) <=
      qpow (blockWeight k) (2 * N - 4) *
        (dimQ (2 * N - 5) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 6)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hbox := halfTimeBox_sixth_physical r
  have eleft :
      dimQ (2 * N - 6) * lineSum (lagCorr w N) (2 * N - 5) ≈
        dimQ (2 * N - 6) * boxSum w N (2 * N - 5) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (2 * N - 5)))
  have eright :
      qpow w (2 * N - 4) *
          (dimQ (2 * N - 5) * boxSum w N (2 * N - 6)) ≈
        qpow w (2 * N - 4) *
          (dimQ (2 * N - 5) * lineSum (lagCorr w N) (2 * N - 6)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N (2 * N - 6)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ (by simpa only [k, N, w] using hbox)
      (Q'.le_of_eqv eright))

theorem physical_halfTime_lineSum_sixth_from_four (k : Nat) (hk : 4 <= k) :
    let N := blockNcut k
    dimQ (2 * N - 6) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 5) <=
      qpow (blockWeight k) (2 * N - 4) *
        (dimQ (2 * N - 5) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 6)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using halfTimeLineSum_sixth_physical r

end YMGap.Continuum.P2HalfTimeSixthShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeSixthShell.boxSumDelta_top_six
#print axioms YMGap.Continuum.P2HalfTimeSixthShell.boxSum_top_six
#print axioms YMGap.Continuum.P2HalfTimeSixthShell.sixthBoxRatio
#print axioms YMGap.Continuum.P2HalfTimeSixthShell.physical_threeFourths_power_floor_sixth
#print axioms YMGap.Continuum.P2HalfTimeSixthShell.physical_sixth_coeff_descending
#print axioms YMGap.Continuum.P2HalfTimeSixthShell.sixthHalfTimeScalar
#print axioms YMGap.Continuum.P2HalfTimeSixthShell.halfTimeBox_sixth_physical
#print axioms YMGap.Continuum.P2HalfTimeSixthShell.halfTimeLineSum_sixth_physical
#print axioms YMGap.Continuum.P2HalfTimeSixthShell.physical_halfTime_lineSum_sixth_from_four
