/-
Track 11.7-fusion / R4t -- reflected algebra for the eighth half-time shell.

The depth-seven and depth-eight endpoint boxes have respectively twenty and
twenty-five Clebsch pairs.  For a descending endpoint string

    I >= H >= G >= F >= E >= A >= X >= B >= C,

their sharp equal-coefficient comparison is `5*B7 <= 4*B8`.  This module
proves that comparison abstractly: the cleared slack is a sum of twenty-three
nonnegative products in the eight successive coefficient increments.  The
exact Clebsch support and physical heat transport remain separate steps.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeSeventhShell
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.P2HalfTimeEighthRatio

set_option maxHeartbeats 360000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.HeatKernelRGStep

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

/-! ## 1. Reusable endpoint-box polynomials -/

def qSum : List Q' -> Q'
  | [] => 0
  | [x] => x
  | x :: xs => x + qSum xs

/-- The twenty-pair depth-seven endpoint box, written only in its eight
endpoint coefficients. -/
def endpointBoxSevenExpr (H G F E A X B C : Q') : Q' :=
  qSum [
    E * A, E * A,
    F * X, A * X, F * X, A * X,
    G * B, E * B, X * B, G * B, E * B, X * B,
    H * C, F * C, A * C, B * C, H * C, F * C, A * C, B * C]

/-- The twenty-five-pair depth-eight endpoint box. -/
def endpointBoxEightExpr (I H G F E A X B C : Q') : Q' :=
  qSum [
    E * E, F * A, F * A, A * A,
    G * X, E * X, G * X, E * X, X * X,
    H * B, F * B, A * B, H * B, F * B, A * B, B * B,
    I * C, G * C, E * C, X * C, I * C, G * C, E * C, X * C, C * C]

private def eighthRatioSlack (I H G F E A X B C : Q') : Q' :=
  let dI := I + -H
  let dH := H + -G
  let dG := G + -F
  let dF := F + -E
  let dE := E + -A
  let dA := A + -X
  let dX := X + -B
  let dB := B + -C
  Q'.ofNat 6 * C * dA +
    (Q'.ofNat 12 * C * dE +
      (Q'.ofNat 8 * C * dF +
        (Q'.ofNat 12 * C * dG +
          (Q'.ofNat 6 * C * dH +
            (Q'.ofNat 8 * C * dI +
              (Q'.ofNat 8 * C * dX +
                (Q'.ofNat 6 * (dA * dA) +
                  (Q'.ofNat 12 * dA * dB +
                    (Q'.ofNat 6 * dA * dE +
                      (Q'.ofNat 8 * dA * dF +
                        (Q'.ofNat 8 * dA * dX +
                          (Q'.ofNat 4 * (dB * dB) +
                            (Q'.ofNat 8 * dB * dE +
                              (Q'.ofNat 12 * dB * dF +
                                (Q'.ofNat 6 * dB * dG +
                                  (Q'.ofNat 8 * dB * dH +
                                    (Q'.ofNat 6 * dB * dX +
                                      (Q'.ofNat 4 * (dE * dE) +
                                        (Q'.ofNat 12 * dE * dX +
                                          (Q'.ofNat 6 * dF * dX +
                                            (Q'.ofNat 8 * dG * dX +
                                              Q'.ofNat 6 *
                                                (dX * dX))))))))))))))))))))))

/-! ## 2. Reflected polynomial identity -/

private def pSum : List RingNormaliser.PolyExpr -> RingNormaliser.PolyExpr
  | [] => .const 0
  | [x] => x
  | x :: xs => .add x (pSum xs)

private def pTerm (n : Int) (a b : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := .mul (.mul (.const n) a) b

private def pSquare (n : Int) (a : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := .mul (.const n) (.mul a a)

private def eighthFactorLeft : RingNormaliser.PolyExpr :=
  let I := RingNormaliser.PolyExpr.var 0
  let H := RingNormaliser.PolyExpr.var 1
  let G := RingNormaliser.PolyExpr.var 2
  let F := RingNormaliser.PolyExpr.var 3
  let E := RingNormaliser.PolyExpr.var 4
  let A := RingNormaliser.PolyExpr.var 5
  let X := RingNormaliser.PolyExpr.var 6
  let B := RingNormaliser.PolyExpr.var 7
  let C := RingNormaliser.PolyExpr.var 8
  let Y := pSum [
    .mul E E, .mul F A, .mul F A, .mul A A,
    .mul G X, .mul E X, .mul G X, .mul E X, .mul X X,
    .mul H B, .mul F B, .mul A B,
    .mul H B, .mul F B, .mul A B, .mul B B,
    .mul I C, .mul G C, .mul E C, .mul X C,
    .mul I C, .mul G C, .mul E C, .mul X C, .mul C C]
  .mul (.const 4) Y

private def eighthFactorRight : RingNormaliser.PolyExpr :=
  let I := RingNormaliser.PolyExpr.var 0
  let H := RingNormaliser.PolyExpr.var 1
  let G := RingNormaliser.PolyExpr.var 2
  let F := RingNormaliser.PolyExpr.var 3
  let E := RingNormaliser.PolyExpr.var 4
  let A := RingNormaliser.PolyExpr.var 5
  let X := RingNormaliser.PolyExpr.var 6
  let B := RingNormaliser.PolyExpr.var 7
  let C := RingNormaliser.PolyExpr.var 8
  let Z := pSum [
    .mul E A, .mul E A,
    .mul F X, .mul A X, .mul F X, .mul A X,
    .mul G B, .mul E B, .mul X B,
    .mul G B, .mul E B, .mul X B,
    .mul H C, .mul F C, .mul A C, .mul B C,
    .mul H C, .mul F C, .mul A C, .mul B C]
  let dI := .add I (.neg H)
  let dH := .add H (.neg G)
  let dG := .add G (.neg F)
  let dF := .add F (.neg E)
  let dE := .add E (.neg A)
  let dA := .add A (.neg X)
  let dX := .add X (.neg B)
  let dB := .add B (.neg C)
  let slack := pSum [
    pTerm 6 C dA, pTerm 12 C dE, pTerm 8 C dF,
    pTerm 12 C dG, pTerm 6 C dH, pTerm 8 C dI,
    pTerm 8 C dX,
    pSquare 6 dA, pTerm 12 dA dB, pTerm 6 dA dE,
    pTerm 8 dA dF, pTerm 8 dA dX,
    pSquare 4 dB, pTerm 8 dB dE, pTerm 12 dB dF,
    pTerm 6 dB dG, pTerm 8 dB dH, pTerm 6 dB dX,
    pSquare 4 dE, pTerm 12 dE dX, pTerm 6 dF dX,
    pTerm 8 dG dX, pSquare 6 dX]
  .add (.mul (.const 5) Z) slack

private theorem eighthFactor_normal :
    RingNormaliser.normalize eighthFactorLeft =
      RingNormaliser.normalize eighthFactorRight := by decide

private theorem eighth_factor_core (I H G F E A X B C : Q') :
    Q'.ofNat 4 * endpointBoxEightExpr I H G F E A X B C ≈
      Q'.ofNat 5 * endpointBoxSevenExpr H G F E A X B C +
        eighthRatioSlack I H G F E A X B C := by
  simpa [endpointBoxEightExpr, endpointBoxSevenExpr, eighthRatioSlack, qSum,
    eighthFactorLeft, eighthFactorRight, pSum, pTerm, pSquare,
    RingNormaliser.eval,
    show Q'.ofInt 4 = Q'.ofNat 4 from rfl,
    show Q'.ofInt 5 = Q'.ofNat 5 from rfl,
    show Q'.ofInt 6 = Q'.ofNat 6 from rfl,
    show Q'.ofInt 8 = Q'.ofNat 8 from rfl,
    show Q'.ofInt 12 = Q'.ofNat 12 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      eighthFactorLeft eighthFactorRight eighthFactor_normal
      (fun | 0 => I | 1 => H | 2 => G | 3 => F | 4 => E |
        5 => A | 6 => X | 7 => B | _ => C))

/-! ## 3. Sharp ratio from descending endpoint coefficients -/

/-- For nine descending nonnegative endpoint coefficients, the twenty-pair
depth-seven box is at most `4/5` of the adjacent twenty-five-pair depth-eight
box. -/
theorem eighthBoxRatio (I H G F E A X B C : Q')
    (hHI : H <= I) (hGH : G <= H) (hFG : F <= G)
    (hEF : E <= F) (hAE : A <= E) (hXA : X <= A)
    (hBX : B <= X) (hCB : C <= B) (hC0 : (0 : Q') <= C) :
    endpointBoxSevenExpr H G F E A X B C <=
      fourFifths * endpointBoxEightExpr I H G F E A X B C := by
  let dI := I + -H
  let dH := H + -G
  let dG := G + -F
  let dF := F + -E
  let dE := E + -A
  let dA := A + -X
  let dX := X + -B
  let dB := B + -C
  let slack := eighthRatioSlack I H G F E A X B C
  have hdI0 : (0 : Q') <= dI := by
    simpa only [dI] using Q'.sub_nonneg_of_le hHI
  have hdH0 : (0 : Q') <= dH := by
    simpa only [dH] using Q'.sub_nonneg_of_le hGH
  have hdG0 : (0 : Q') <= dG := by
    simpa only [dG] using Q'.sub_nonneg_of_le hFG
  have hdF0 : (0 : Q') <= dF := by
    simpa only [dF] using Q'.sub_nonneg_of_le hEF
  have hdE0 : (0 : Q') <= dE := by
    simpa only [dE] using Q'.sub_nonneg_of_le hAE
  have hdA0 : (0 : Q') <= dA := by
    simpa only [dA] using Q'.sub_nonneg_of_le hXA
  have hdX0 : (0 : Q') <= dX := by
    simpa only [dX] using Q'.sub_nonneg_of_le hBX
  have hdB0 : (0 : Q') <= dB := by
    simpa only [dB] using Q'.sub_nonneg_of_le hCB
  have term {n : Nat} {a b : Q'} (ha : (0 : Q') <= a)
      (hb : (0 : Q') <= b) :
      (0 : Q') <= Q'.ofNat n * a * b :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (zero_le_ofNat n) ha) hb
  have square {n : Nat} {a : Q'} (ha : (0 : Q') <= a) :
      (0 : Q') <= Q'.ofNat n * (a * a) :=
    Q'.mul_nonneg _ _ (zero_le_ofNat n) (Q'.mul_nonneg _ _ ha ha)
  have hslack0 : (0 : Q') <= slack := by
    dsimp only [slack, eighthRatioSlack, dI, dH, dG, dF, dE, dA, dX, dB]
    exact add_nonneg (term hC0 hdA0)
      (add_nonneg (term hC0 hdE0)
        (add_nonneg (term hC0 hdF0)
          (add_nonneg (term hC0 hdG0)
            (add_nonneg (term hC0 hdH0)
              (add_nonneg (term hC0 hdI0)
                (add_nonneg (term hC0 hdX0)
                  (add_nonneg (square hdA0)
                    (add_nonneg (term hdA0 hdB0)
                      (add_nonneg (term hdA0 hdE0)
                        (add_nonneg (term hdA0 hdF0)
                          (add_nonneg (term hdA0 hdX0)
                            (add_nonneg (square hdB0)
                              (add_nonneg (term hdB0 hdE0)
                                (add_nonneg (term hdB0 hdF0)
                                  (add_nonneg (term hdB0 hdG0)
                                    (add_nonneg (term hdB0 hdH0)
                                      (add_nonneg (term hdB0 hdX0)
                                        (add_nonneg (square hdE0)
                                          (add_nonneg (term hdE0 hdX0)
                                            (add_nonneg (term hdF0 hdX0)
                                              (add_nonneg (term hdG0 hdX0)
                                                (square hdX0))))))))))))))))))))))
  have hfifthSlack0 : (0 : Q') <= oneFifth * slack :=
    Q'.mul_nonneg _ _ (by decide) hslack0
  let W := endpointBoxSevenExpr H G F E A X B C
  let Y := endpointBoxEightExpr I H G F E A X B C
  have hfactor : fourFifths * Y ≈ W + oneFifth * slack := by
    have h45 : fourFifths ≈ Q'.ofNat 4 * oneFifth := by
      unfold fourFifths oneFifth
      ring_qeqv
    have h15 : oneFifth * Q'.ofNat 5 ≈ (1 : Q') := by
      unfold oneFifth
      ring_qeqv
    have hcore : Q'.ofNat 4 * Y ≈ Q'.ofNat 5 * W + slack := by
      simpa only [W, Y, slack] using
        eighth_factor_core I H G F E A X B C
    refine Q'.eqv_trans _ ((Q'.ofNat 4 * oneFifth) * Y) _
      (Q'.mul_eqv_congr_right _ _ Y h45) ?_
    refine Q'.eqv_trans _ (oneFifth * (Q'.ofNat 4 * Y)) _ ?_ ?_
    · refine Q'.eqv_trans _ ((oneFifth * Q'.ofNat 4) * Y) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ Y
          (Q'.mul_comm_eqv (Q'.ofNat 4) oneFifth)
      · exact Q'.mul_assoc_eqv oneFifth (Q'.ofNat 4) Y
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
  change W <= fourFifths * Y
  exact Q'.le_trans' _ _ _ hbase (Q'.ge_of_eqv hfactor)

end YMGap.Continuum.P2HalfTimeEighthRatio

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeEighthRatio.eighthBoxRatio
