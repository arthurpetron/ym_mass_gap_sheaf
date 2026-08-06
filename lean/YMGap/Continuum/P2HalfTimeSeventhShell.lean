/-
Track 11.7-fusion / R4s -- exact seventh half-time boundary shell.

At channel `s = 2*N-7`, the adjacent Clebsch boxes have sixteen and
twenty endpoint pairs.  Their equal-coefficient ratio is sharply `4/5`.
For a descending endpoint string

    H >= G >= F >= E >= A >= X >= B >= C,

the cleared difference `4*Z - 5*W` is a sum of nineteen nonnegative
increment products.  The reflective polynomial normalizer checks that
identity without evaluating a growing rational convolution.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeSixthShell
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.P2HalfTimeSeventhShell

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

private theorem add_nonneg {a b : Q'} (ha : (0 : Q') <= a)
    (hb : (0 : Q') <= b) : (0 : Q') <= a + b :=
  Q'.le_trans' _ ((0 : Q') + 0) _ (by decide) (Q'.add_le_add ha hb)

private theorem ofNat_le_ofNat {a b : Nat} (h : a <= b) :
    Q'.ofNat a <= Q'.ofNat b := by
  show (Int.ofNat a) * (1 : Int) <= (Int.ofNat b) * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr h

/-! ## 1. Exact twenty-pair endpoint support -/

private theorem fusionInd_comm (a b s : Nat) :
    fusionInd a b s = fusionInd b a s := by
  unfold fusionInd
  rw [fusionOK_symm_ab]

private theorem fusionInd_top_seven_low (N : Nat) (hN : 7 <= N) :
    fusionInd (N - 7) N (2 * N - 7) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 7) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 7) N = N - 7 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 7 + N + (2 * N - 7) = 2 * (2 * N - 7) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 7), Nat.mul_mod_left]

private theorem fusionInd_top_seven_lowMid (N : Nat) (hN : 7 <= N) :
    fusionInd (N - 5) N (2 * N - 7) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 5) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 5) N = N - 5 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 5 + N + (2 * N - 7) = 2 * (2 * N - 6) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 6), Nat.mul_mod_left]

private theorem fusionInd_top_seven_highMid (N : Nat) (hN : 7 <= N) :
    fusionInd (N - 3) N (2 * N - 7) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 3) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 3) N = N - 3 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 3 + N + (2 * N - 7) = 2 * (2 * N - 5) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 5), Nat.mul_mod_left]

private theorem fusionInd_top_seven_high (N : Nat) (hN : 7 <= N) :
    fusionInd (N - 1) N (2 * N - 7) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 1) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 1) N = N - 1 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 1 + N + (2 * N - 7) = 2 * (2 * N - 4) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 4), Nat.mul_mod_left]

private theorem fusionInd_top_seven_diag_zero (N : Nat) (hN : 7 <= N) :
    fusionInd N N (2 * N - 7) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff N N (2 * N - 7)).mp hok with
    ⟨_, _, hp⟩
  omega

private theorem fusionInd_top_seven_zero_other
    (N a : Nat) (hN : 7 <= N) (ha : a < N)
    (hne7 : a ≠ N - 7) (hne5 : a ≠ N - 5)
    (hne3 : a ≠ N - 3) (hne1 : a ≠ N - 1) :
    fusionInd a N (2 * N - 7) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff a N (2 * N - 7)).mp hok with
    ⟨_, hhi, hp⟩
  have halow : N - 7 <= a := by omega
  have hcases : a = N - 7 ∨ a = N - 6 ∨ a = N - 5 ∨
      a = N - 4 ∨ a = N - 3 ∨ a = N - 2 ∨ a = N - 1 := by omega
  rcases hcases with h | h | h | h | h | h | h
  · exact hne7 h
  · subst a; omega
  · exact hne5 h
  · subst a; omega
  · exact hne3 h
  · subst a; omega
  · exact hne1 h

private theorem topSevenRow (w : Q') (N : Nat) (hN : 7 <= N) :
    fsum (fun a => fusionInd a N (2 * N - 7) *
      (coeffW w a * coeffW w N)) N ≈
      (((coeffW w (N - 7) * coeffW w N +
        coeffW w (N - 5) * coeffW w N) +
        coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N) := by
  let g := fun a => fusionInd a N (2 * N - 7) *
    (coeffW w a * coeffW w N)
  have hsplit : fsum g N =
      (((((((fsum g (N - 7) + g (N - 7)) + g (N - 6)) + g (N - 5)) +
        g (N - 4)) + g (N - 3)) + g (N - 2)) + g (N - 1)) := by
    rw [show N = (N - 7) + 7 by omega]
    rfl
  rw [hsplit]
  have hpre : fsum g (N - 7) ≈ (0 : Q') := by
    apply fsum_zero_below
    intro a ha
    dsimp only [g]
    rw [fusionInd_top_seven_zero_other N a hN (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h7 : g (N - 7) ≈ coeffW w (N - 7) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_seven_low N hN]
    exact Q'.one_mul_eqv _
  have h6 : g (N - 6) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_seven_zero_other N (N - 6) hN (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h5 : g (N - 5) ≈ coeffW w (N - 5) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_seven_lowMid N hN]
    exact Q'.one_mul_eqv _
  have h4 : g (N - 4) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_seven_zero_other N (N - 4) hN (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h3 : g (N - 3) ≈ coeffW w (N - 3) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_seven_highMid N hN]
    exact Q'.one_mul_eqv _
  have h2 : g (N - 2) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_seven_zero_other N (N - 2) hN (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    exact Q'.zero_mul_eqv _
  have h1 : g (N - 1) ≈ coeffW w (N - 1) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_seven_high N hN]
    exact Q'.one_mul_eqv _
  let M := (((((((0 : Q') + coeffW w (N - 7) * coeffW w N) + 0) +
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
                (Q'.add_eqv_congr' hpre h7) h6) h5) h4) h3) h2) h1
  · dsimp only [M]
    ring_qeqv

theorem boxSumDelta_top_seven (w : Q') (N : Nat) (hN : 7 <= N) :
    boxSumDelta w (N - 1) (2 * N - 7) ≈
      ((((coeffW w (N - 7) * coeffW w N +
          coeffW w (N - 5) * coeffW w N) +
        coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N) +
      (((coeffW w (N - 7) * coeffW w N +
          coeffW w (N - 5) * coeffW w N) +
        coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N)) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft := topSevenRow w N hN
  have hright0 := topSevenRow w N hN
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 7) *
        (coeffW w N * coeffW w b)) N ≈
        (((coeffW w (N - 7) * coeffW w N +
            coeffW w (N - 5) * coeffW w N) +
          coeffW w (N - 3) * coeffW w N) +
          coeffW w (N - 1) * coeffW w N) := by
    refine Q'.eqv_trans _ _ _ ?_ hright0
    apply CubeRatioBounds.fsum_eqv_congr
    intro b
    rw [fusionInd_comm N b (2 * N - 7)]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
  rw [fusionInd_top_seven_diag_zero N hN]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hleft
      (Q'.add_eqv_congr' hright (Q'.zero_mul_eqv _))) ?_
  ring_qeqv

/-- Channel `2*N-7` has exactly twenty Clebsch pairs. -/
theorem boxSum_top_seven (w : Q') (N : Nat) (hN : 7 <= N) :
    boxSum w N (2 * N - 7) ≈
      (((((coeffW w (N - 4) * coeffW w (N - 3) +
            coeffW w (N - 4) * coeffW w (N - 3)) +
          ((coeffW w (N - 5) * coeffW w (N - 2) +
              coeffW w (N - 3) * coeffW w (N - 2)) +
            (coeffW w (N - 5) * coeffW w (N - 2) +
              coeffW w (N - 3) * coeffW w (N - 2)))) +
        (((coeffW w (N - 6) * coeffW w (N - 1) +
              coeffW w (N - 4) * coeffW w (N - 1)) +
            coeffW w (N - 2) * coeffW w (N - 1)) +
          ((coeffW w (N - 6) * coeffW w (N - 1) +
              coeffW w (N - 4) * coeffW w (N - 1)) +
            coeffW w (N - 2) * coeffW w (N - 1)))) +
      ((((coeffW w (N - 7) * coeffW w N +
            coeffW w (N - 5) * coeffW w N) +
          coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N) +
       (((coeffW w (N - 7) * coeffW w N +
            coeffW w (N - 5) * coeffW w N) +
          coeffW w (N - 3) * coeffW w N) +
        coeffW w (N - 1) * coeffW w N)))) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 7)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold := boxSum_top_five w (N - 1) (by omega)
  rw [show 2 * (N - 1) - 5 = 2 * N - 7 by omega] at hold
  simpa only [
    show N - 1 - 3 = N - 4 by omega,
    show N - 1 - 2 = N - 3 by omega,
    show N - 1 - 4 = N - 5 by omega,
    show N - 1 - 1 = N - 2 by omega,
    show N - 1 - 5 = N - 6 by omega] using
    (Q'.add_eqv_congr' hold (boxSumDelta_top_seven w N hN))

/-! ## 2. Reflected sharp `4/5` ratio -/

private def seventhFactorLeft : RingNormaliser.PolyExpr :=
  let H := RingNormaliser.PolyExpr.var 0
  let G := RingNormaliser.PolyExpr.var 1
  let F := RingNormaliser.PolyExpr.var 2
  let E := RingNormaliser.PolyExpr.var 3
  let A := RingNormaliser.PolyExpr.var 4
  let X := RingNormaliser.PolyExpr.var 5
  let B := RingNormaliser.PolyExpr.var 6
  let C := RingNormaliser.PolyExpr.var 7
  let Z :=
    .add
      (.add
        (.add (.mul E A) (.mul E A))
        (.add (.add (.mul F X) (.mul A X))
          (.add (.mul F X) (.mul A X))))
      (.add
        (.add (.add (.mul G B) (.mul E B)) (.mul X B))
        (.add (.add (.mul G B) (.mul E B)) (.mul X B)))
      |> fun base =>
        .add base
          (.add
            (.add (.add (.add (.mul H C) (.mul F C)) (.mul A C)) (.mul B C))
            (.add (.add (.add (.mul H C) (.mul F C)) (.mul A C)) (.mul B C)))
  .mul (.const 4) Z

private def seventhFactorRight : RingNormaliser.PolyExpr :=
  let H := RingNormaliser.PolyExpr.var 0
  let G := RingNormaliser.PolyExpr.var 1
  let F := RingNormaliser.PolyExpr.var 2
  let E := RingNormaliser.PolyExpr.var 3
  let A := RingNormaliser.PolyExpr.var 4
  let X := RingNormaliser.PolyExpr.var 5
  let B := RingNormaliser.PolyExpr.var 6
  let C := RingNormaliser.PolyExpr.var 7
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
  let dH := .add H (.neg G)
  let dG := .add G (.neg F)
  let dF := .add F (.neg E)
  let dE := .add E (.neg A)
  let dA := .add A (.neg X)
  let dX := .add X (.neg B)
  let dB := .add B (.neg C)
  let slack :=
    .add (.mul (.mul (.const 8) C) dB)
      (.add (.mul (.mul (.const 6) C) dX)
        (.add (.mul (.mul (.const 12) C) dA)
          (.add (.mul (.mul (.const 8) C) dE)
            (.add (.mul (.mul (.const 12) C) dF)
              (.add (.mul (.mul (.const 6) C) dG)
                (.add (.mul (.mul (.const 8) C) dH)
                  (.add (.mul (.const 3) (.mul dB dB))
                    (.add (.mul (.mul (.const 12) dB) dX)
                      (.add (.mul (.mul (.const 8) dB) dA)
                        (.add (.mul (.mul (.const 12) dB) dE)
                          (.add (.mul (.mul (.const 6) dB) dF)
                            (.add (.mul (.mul (.const 8) dB) dG)
                              (.add (.mul (.const 4) (.mul dX dX))
                                (.add (.mul (.mul (.const 12) dX) dA)
                                  (.add (.mul (.mul (.const 6) dX) dE)
                                    (.add (.mul (.mul (.const 8) dX) dF)
                                      (.add (.mul (.const 3) (.mul dA dA))
                                        (.mul (.mul (.const 8) dA) dE))))))))))))))))))
  .add (.mul (.const 5) W) slack

private theorem seventhFactor_normal :
    RingNormaliser.normalize seventhFactorLeft =
      RingNormaliser.normalize seventhFactorRight := by decide

private theorem seventh_factor_core (H G F E A X B C : Q') :
    Q'.ofNat 4 *
        (((((E * A + E * A) +
              ((F * X + A * X) + (F * X + A * X))) +
            (((G * B + E * B) + X * B) +
              ((G * B + E * B) + X * B))) +
          ((((H * C + F * C) + A * C) + B * C) +
            (((H * C + F * C) + A * C) + B * C)))) ≈
      Q'.ofNat 5 *
          ((((A * A + (E * X + (E * X + X * X))) +
              ((F * B + A * B) + ((F * B + A * B) + B * B))) +
            (((G * C + E * C) + X * C) +
              (((G * C + E * C) + X * C) + C * C)))) +
        (Q'.ofNat 8 * C * (B + -C) +
          (Q'.ofNat 6 * C * (X + -B) +
            (Q'.ofNat 12 * C * (A + -X) +
              (Q'.ofNat 8 * C * (E + -A) +
                (Q'.ofNat 12 * C * (F + -E) +
                  (Q'.ofNat 6 * C * (G + -F) +
                    (Q'.ofNat 8 * C * (H + -G) +
                      (Q'.ofNat 3 * ((B + -C) * (B + -C)) +
                        (Q'.ofNat 12 * (B + -C) * (X + -B) +
                          (Q'.ofNat 8 * (B + -C) * (A + -X) +
                            (Q'.ofNat 12 * (B + -C) * (E + -A) +
                              (Q'.ofNat 6 * (B + -C) * (F + -E) +
                                (Q'.ofNat 8 * (B + -C) * (G + -F) +
                                  (Q'.ofNat 4 * ((X + -B) * (X + -B)) +
                                    (Q'.ofNat 12 * (X + -B) * (A + -X) +
                                      (Q'.ofNat 6 * (X + -B) * (E + -A) +
                                        (Q'.ofNat 8 * (X + -B) * (F + -E) +
                                          (Q'.ofNat 3 * ((A + -X) * (A + -X)) +
                                            Q'.ofNat 8 * (A + -X) *
                                              (E + -A))))))))))))))))))) := by
  simpa [seventhFactorLeft, seventhFactorRight, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      seventhFactorLeft seventhFactorRight seventhFactor_normal
      (fun | 0 => H | 1 => G | 2 => F | 3 => E | 4 => A | 5 => X |
        6 => B | _ => C))

/-- For eight descending nonnegative endpoint coefficients, the sixteen-pair
depth-six box is at most `4/5` of the adjacent twenty-pair depth-seven box. -/
theorem seventhBoxRatio (H G F E A X B C : Q')
    (hGH : G <= H) (hFG : F <= G) (hEF : E <= F)
    (hAE : A <= E) (hXA : X <= A) (hBX : B <= X)
    (hCB : C <= B) (hC0 : (0 : Q') <= C) :
    (((A * A + (E * X + (E * X + X * X))) +
        ((F * B + A * B) + ((F * B + A * B) + B * B))) +
      (((G * C + E * C) + X * C) +
        (((G * C + E * C) + X * C) + C * C))) <=
      fourFifths *
        ((((E * A + E * A) +
            ((F * X + A * X) + (F * X + A * X))) +
          (((G * B + E * B) + X * B) +
            ((G * B + E * B) + X * B))) +
        ((((H * C + F * C) + A * C) + B * C) +
          (((H * C + F * C) + A * C) + B * C))) := by
  let W := (((A * A + (E * X + (E * X + X * X))) +
      ((F * B + A * B) + ((F * B + A * B) + B * B))) +
    (((G * C + E * C) + X * C) +
      (((G * C + E * C) + X * C) + C * C)))
  let Z := ((((E * A + E * A) +
      ((F * X + A * X) + (F * X + A * X))) +
    (((G * B + E * B) + X * B) +
      ((G * B + E * B) + X * B))) +
    ((((H * C + F * C) + A * C) + B * C) +
      (((H * C + F * C) + A * C) + B * C)))
  let dH := H + -G
  let dG := G + -F
  let dF := F + -E
  let dE := E + -A
  let dA := A + -X
  let dX := X + -B
  let dB := B + -C
  let slack := Q'.ofNat 8 * C * dB +
    (Q'.ofNat 6 * C * dX +
      (Q'.ofNat 12 * C * dA +
        (Q'.ofNat 8 * C * dE +
          (Q'.ofNat 12 * C * dF +
            (Q'.ofNat 6 * C * dG +
              (Q'.ofNat 8 * C * dH +
                (Q'.ofNat 3 * (dB * dB) +
                  (Q'.ofNat 12 * dB * dX +
                    (Q'.ofNat 8 * dB * dA +
                      (Q'.ofNat 12 * dB * dE +
                        (Q'.ofNat 6 * dB * dF +
                          (Q'.ofNat 8 * dB * dG +
                            (Q'.ofNat 4 * (dX * dX) +
                              (Q'.ofNat 12 * dX * dA +
                                (Q'.ofNat 6 * dX * dE +
                                  (Q'.ofNat 8 * dX * dF +
                                    (Q'.ofNat 3 * (dA * dA) +
                                      Q'.ofNat 8 * dA * dE)))))))))))))))))
  have hdH0 : (0 : Q') <= dH := by simpa only [dH] using Q'.sub_nonneg_of_le hGH
  have hdG0 : (0 : Q') <= dG := by simpa only [dG] using Q'.sub_nonneg_of_le hFG
  have hdF0 : (0 : Q') <= dF := by simpa only [dF] using Q'.sub_nonneg_of_le hEF
  have hdE0 : (0 : Q') <= dE := by simpa only [dE] using Q'.sub_nonneg_of_le hAE
  have hdA0 : (0 : Q') <= dA := by simpa only [dA] using Q'.sub_nonneg_of_le hXA
  have hdX0 : (0 : Q') <= dX := by simpa only [dX] using Q'.sub_nonneg_of_le hBX
  have hdB0 : (0 : Q') <= dB := by simpa only [dB] using Q'.sub_nonneg_of_le hCB
  have term {n : Nat} {a b : Q'} (ha : (0 : Q') <= a) (hb : (0 : Q') <= b) :
      (0 : Q') <= Q'.ofNat n * a * b :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat n) ha) hb
  have square {n : Nat} {a : Q'} (ha : (0 : Q') <= a) :
      (0 : Q') <= Q'.ofNat n * (a * a) :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat n) (Q'.mul_nonneg _ _ ha ha)
  have hslack0 : (0 : Q') <= slack := by
    exact add_nonneg (term hC0 hdB0)
      (add_nonneg (term hC0 hdX0)
        (add_nonneg (term hC0 hdA0)
          (add_nonneg (term hC0 hdE0)
            (add_nonneg (term hC0 hdF0)
              (add_nonneg (term hC0 hdG0)
                (add_nonneg (term hC0 hdH0)
                  (add_nonneg (square hdB0)
                    (add_nonneg (term hdB0 hdX0)
                      (add_nonneg (term hdB0 hdA0)
                        (add_nonneg (term hdB0 hdE0)
                          (add_nonneg (term hdB0 hdF0)
                            (add_nonneg (term hdB0 hdG0)
                              (add_nonneg (square hdX0)
                                (add_nonneg (term hdX0 hdA0)
                                  (add_nonneg (term hdX0 hdE0)
                                    (add_nonneg (term hdX0 hdF0)
                                      (add_nonneg (square hdA0)
                                        (term hdA0 hdE0))))))))))))))))))
  have hfifthSlack0 : (0 : Q') <= oneFifth * slack :=
    Q'.mul_nonneg _ _ (by decide) hslack0
  have hfactor : fourFifths * Z ≈ W + oneFifth * slack := by
    have h45 : fourFifths ≈ Q'.ofNat 4 * oneFifth := by
      unfold fourFifths oneFifth
      ring_qeqv
    have h15 : oneFifth * Q'.ofNat 5 ≈ (1 : Q') := by
      unfold oneFifth
      ring_qeqv
    have hcore : Q'.ofNat 4 * Z ≈ Q'.ofNat 5 * W + slack := by
      simpa only [W, Z, slack, dH, dG, dF, dE, dA, dX, dB] using
        seventh_factor_core H G F E A X B C
    refine Q'.eqv_trans _ ((Q'.ofNat 4 * oneFifth) * Z) _
      (Q'.mul_eqv_congr_right _ _ Z h45) ?_
    refine Q'.eqv_trans _ (oneFifth * (Q'.ofNat 4 * Z)) _ ?_ ?_
    · refine Q'.eqv_trans _ ((oneFifth * Q'.ofNat 4) * Z) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ Z
          (Q'.mul_comm_eqv (Q'.ofNat 4) oneFifth)
      · exact Q'.mul_assoc_eqv oneFifth (Q'.ofNat 4) Z
    · refine Q'.eqv_trans _ (oneFifth * (Q'.ofNat 5 * W + slack)) _
        (Q'.mul_eqv_congr_left oneFifth _ _ hcore) ?_
      refine Q'.eqv_trans _
        (oneFifth * (Q'.ofNat 5 * W) + oneFifth * slack) _
        (Q'.mul_add_eqv oneFifth (Q'.ofNat 5 * W) slack) ?_
      refine Q'.add_eqv_congr_right _ _ (oneFifth * slack) ?_
      refine Q'.eqv_trans _ ((oneFifth * Q'.ofNat 5) * W) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv oneFifth (Q'.ofNat 5) W)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * W) _
        (Q'.mul_eqv_congr_right _ _ W h15) ?_
      exact Q'.one_mul_eqv W
  have hbase : W <= W + oneFifth * slack :=
    Q'.add_le_self_of_nonneg W (oneFifth * slack) hfifthSlack0
  change W <= fourFifths * Z
  exact Q'.le_trans' _ _ _ hbase (Q'.ge_of_eqv hfactor)

/-! ## 3. Physical heat floor and seventh endpoint descent -/

private theorem physical_five_times_seventh_exponent_cleared (r : Nat) :
    5 * (2 * blockNcut (r + 4) - 5) <= physicalWeightDen (r + 4) := by
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
  have hpoly : 25 * (5 * (2 * N - 5)) <= 12 * (N + 1) * (N + 1) := by
    calc
      25 * (5 * (2 * N - 5)) <= 250 * N := by omega
      _ <= 252 * N := by omega
      _ = 12 * (21 * N) := by omega
      _ <= 12 * (N * N) := Nat.mul_le_mul_left 12 h21N
      _ <= 12 * ((N + 1) * (N + 1)) := Nat.mul_le_mul_left 12 hNN
      _ = 12 * (N + 1) * (N + 1) := by ac_rfl
  have hscaled : 25 * (5 * (2 * N - 5)) <= 25 * D := by
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

theorem physical_fourFifths_power_floor_seventh (r : Nat) :
    fourFifths <=
      qpow (blockWeight (r + 4)) (2 * blockNcut (r + 4) - 5) := by
  let k := r + 4
  let N := blockNcut k
  let D := physicalWeightDen k
  let n := 2 * N - 5
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
          physical_five_times_seventh_exponent_cleared r))
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

private theorem physical_margin_cleared_seventh (r : Nat) :
    let N := blockNcut (r + 4)
    physicalWeightDen (r + 4) <= (N - 6) * (2 * N - 11) := by
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
  have hsquare : (N + 1) * (N + 1) <= (N - 6) * (2 * N - 11) := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 6 := ⟨N - 6, by omega⟩
    have hM14 : 14 <= M := by omega
    have h14M : 14 * M <= M * M := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right M hM14
    rw [hM]
    have htwo : 2 * (M + 6) - 11 = 2 * M + 1 := by omega
    rw [htwo]
    simp only [Nat.add_sub_cancel, Nat.mul_add,
      Nat.mul_one, Nat.one_mul, Nat.mul_comm]
    have hmm : M * (M * 2) = 2 * (M * M) := by ac_rfl
    rw [hmm]
    omega
  exact Nat.le_trans hD hsquare

theorem physical_seventh_coeff_descending (r : Nat) :
    coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 6) <=
      coeffW (blockWeight (r + 4)) (blockNcut (r + 4) - 7) := by
  let N := blockNcut (r + 4)
  have hN : 79 <= N := by simpa only [N] using blockNcut_ge_79 r
  have hp0 : Q'.ofNat (N - 6 + 1) *
      qpow (blockWeight (r + 4)) (2 * N - 11) <= Q'.ofNat (N - 6) :=
    physical_power_upper_step r (N - 6) (2 * N - 11) (by
      simpa only [N] using physical_margin_cleared_seventh r)
  have hp : Q'.ofNat (N - 5) *
      qpow (blockWeight (r + 4)) (2 * N - 11) <=
        (1 : Q') * Q'.ofNat (N - 6) := by
    have hp1 : Q'.ofNat (N - 5) *
        qpow (blockWeight (r + 4)) (2 * N - 11) <= Q'.ofNat (N - 6) := by
      simpa only [show N - 6 + 1 = N - 5 by omega] using hp0
    exact Q'.le_trans' _ _ _ hp1 (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have hs := coeffW_succ_le_of_cross
    (w := blockWeight (r + 4)) (R := (1 : Q')) (N - 7)
    (blockWeight_nonneg (r + 4)) (by
      simpa only [show N - 7 + 2 = N - 5 by omega,
        show 2 * (N - 7) + 3 = 2 * N - 11 by omega] using hp)
  have hs' : coeffW (blockWeight (r + 4)) (N - 6) <=
      (1 : Q') * coeffW (blockWeight (r + 4)) (N - 7) := by
    simpa only [show N - 7 + 1 = N - 6 by omega] using hs
  exact Q'.le_trans' _ _ _ hs' (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-! ## 4. Physical box and line-sum transport -/

theorem seventhHalfTimeBoxScalar (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 7 <= N)
    (hpow : fourFifths <= qpow w (2 * N - 5))
    (hHG : coeffW w (N - 6) <= coeffW w (N - 7))
    (hGF : coeffW w (N - 5) <= coeffW w (N - 6))
    (hFE : coeffW w (N - 4) <= coeffW w (N - 5))
    (hEA : coeffW w (N - 3) <= coeffW w (N - 4))
    (hAX : coeffW w (N - 2) <= coeffW w (N - 3))
    (hXB : coeffW w (N - 1) <= coeffW w (N - 2))
    (hBC : coeffW w N <= coeffW w (N - 1)) :
    dimQ (2 * N - 7) * boxSum w N (2 * N - 6) <=
      qpow w (2 * N - 5) *
        (dimQ (2 * N - 6) * boxSum w N (2 * N - 7)) := by
  let H := coeffW w (N - 7)
  let G := coeffW w (N - 6)
  let F := coeffW w (N - 5)
  let E := coeffW w (N - 4)
  let A := coeffW w (N - 3)
  let X := coeffW w (N - 2)
  let B := coeffW w (N - 1)
  let C := coeffW w N
  let W := (((A * A + (E * X + (E * X + X * X))) +
      ((F * B + A * B) + ((F * B + A * B) + B * B))) +
    (((G * C + E * C) + X * C) +
      (((G * C + E * C) + X * C) + C * C)))
  let Z := ((((E * A + E * A) +
      ((F * X + A * X) + (F * X + A * X))) +
    (((G * B + E * B) + X * B) +
      ((G * B + E * B) + X * B))) +
    ((((H * C + F * C) + A * C) + B * C) +
      (((H * C + F * C) + A * C) + B * C)))
  have hC0 : (0 : Q') <= C := coeffW_nonneg hw0 N
  have hratioExpr : W <= fourFifths * Z := by
    simpa only [H, G, F, E, A, X, B, C, W, Z] using
      seventhBoxRatio H G F E A X B C hHG hGF hFE hEA hAX hXB hBC hC0
  have eW : boxSum w N (2 * N - 6) ≈ W := by
    simpa only [G, F, E, A, X, B, C, W] using boxSum_top_six w N (by omega)
  have eZ : boxSum w N (2 * N - 7) ≈ Z := by
    simpa only [H, G, F, E, A, X, B, C, Z] using boxSum_top_seven w N hN
  have hratio : boxSum w N (2 * N - 6) <=
      fourFifths * boxSum w N (2 * N - 7) := by
    refine Q'.le_trans' _ W _ (Q'.le_of_eqv eW) ?_
    refine Q'.le_trans' _ (fourFifths * Z) _ hratioExpr ?_
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left fourFifths Z _ (Q'.eqv_symm eZ))
  let low := dimQ (2 * N - 7)
  let high := dimQ (2 * N - 6)
  have hboxLeft0 : (0 : Q') <= boxSum w N (2 * N - 6) :=
    boxSum_nonneg hw0 N (2 * N - 6)
  have hboxRight0 : (0 : Q') <= boxSum w N (2 * N - 7) :=
    boxSum_nonneg hw0 N (2 * N - 7)
  have hdim : low <= high := by
    have hnat : 2 * N - 7 + 1 <= 2 * N - 6 + 1 := by omega
    simpa only [low, high, dimQ] using ofNat_le_ofNat hnat
  have hdimScaled : low * boxSum w N (2 * N - 6) <=
      high * boxSum w N (2 * N - 6) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdim hboxLeft0
  have hhigh0 : (0 : Q') <= high := by
    unfold high dimQ
    exact HeatKernelRGStep.zero_le_ofNat _
  have hratioScaled : high * boxSum w N (2 * N - 6) <=
      high * (fourFifths * boxSum w N (2 * N - 7)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ high hratio hhigh0
  have hreorder :
      high * (fourFifths * boxSum w N (2 * N - 7)) ≈
        fourFifths * (high * boxSum w N (2 * N - 7)) := by
    ring_qeqv
  have hhighBox0 : (0 : Q') <= high * boxSum w N (2 * N - 7) :=
    Q'.mul_nonneg _ _ hhigh0 hboxRight0
  have hpowScaled : fourFifths * (high * boxSum w N (2 * N - 7)) <=
      qpow w (2 * N - 5) * (high * boxSum w N (2 * N - 7)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hhighBox0
  change low * boxSum w N (2 * N - 6) <=
    qpow w (2 * N - 5) * (high * boxSum w N (2 * N - 7))
  exact Q'.le_trans' _ _ _ hdimScaled
    (Q'.le_trans' _ _ _ hratioScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hpowScaled))

theorem halfTimeBox_seventh_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 7) * boxSum (blockWeight k) N (2 * N - 6) <=
      qpow (blockWeight k) (2 * N - 5) *
        (dimQ (2 * N - 6) * boxSum (blockWeight k) N (2 * N - 7)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hN : 7 <= N := Nat.le_trans (by decide : 7 <= 79) (by
    simpa only [k, N] using blockNcut_ge_79 r)
  exact seventhHalfTimeBoxScalar w N
    (by simpa only [k, w] using blockWeight_nonneg k) hN
    (by simpa only [k, N, w] using physical_fourFifths_power_floor_seventh r)
    (by simpa only [k, N, w] using physical_seventh_coeff_descending r)
    (by simpa only [k, N, w] using physical_sixth_coeff_descending r)
    (by simpa only [k, N, w] using physical_fifth_coeff_descending r)
    (by simpa only [k, N, w] using physical_fourth_coeff_descending r)
    (by simpa only [k, N, w] using physical_prepenultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_penultimate_coeff_descending r)
    (by simpa only [k, N, w] using physical_terminal_coeff_descending_from_four r)

theorem halfTimeLineSum_seventh_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 7) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 6) <=
      qpow (blockWeight k) (2 * N - 5) *
        (dimQ (2 * N - 6) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 7)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hbox := halfTimeBox_seventh_physical r
  have eleft :
      dimQ (2 * N - 7) * lineSum (lagCorr w N) (2 * N - 6) ≈
        dimQ (2 * N - 7) * boxSum w N (2 * N - 6) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (2 * N - 6)))
  have eright :
      qpow w (2 * N - 5) *
          (dimQ (2 * N - 6) * boxSum w N (2 * N - 7)) ≈
        qpow w (2 * N - 5) *
          (dimQ (2 * N - 6) * lineSum (lagCorr w N) (2 * N - 7)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N (2 * N - 7)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ (by simpa only [k, N, w] using hbox)
      (Q'.le_of_eqv eright))

theorem physical_halfTime_lineSum_seventh_from_four (k : Nat) (hk : 4 <= k) :
    let N := blockNcut k
    dimQ (2 * N - 7) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 6) <=
      qpow (blockWeight k) (2 * N - 5) *
        (dimQ (2 * N - 6) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 7)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using halfTimeLineSum_seventh_physical r

end YMGap.Continuum.P2HalfTimeSeventhShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeSeventhShell.boxSumDelta_top_seven
#print axioms YMGap.Continuum.P2HalfTimeSeventhShell.boxSum_top_seven
#print axioms YMGap.Continuum.P2HalfTimeSeventhShell.seventhBoxRatio
#print axioms YMGap.Continuum.P2HalfTimeSeventhShell.physical_fourFifths_power_floor_seventh
#print axioms YMGap.Continuum.P2HalfTimeSeventhShell.physical_seventh_coeff_descending
#print axioms YMGap.Continuum.P2HalfTimeSeventhShell.seventhHalfTimeBoxScalar
#print axioms YMGap.Continuum.P2HalfTimeSeventhShell.halfTimeBox_seventh_physical
#print axioms YMGap.Continuum.P2HalfTimeSeventhShell.halfTimeLineSum_seventh_physical
#print axioms YMGap.Continuum.P2HalfTimeSeventhShell.physical_halfTime_lineSum_seventh_from_four
