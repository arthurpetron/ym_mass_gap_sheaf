/-
Track 11.7-fusion / R4v -- reflected algebra for the ninth half-time shell.

The depth-eight and depth-nine endpoint boxes have respectively twenty-five
and thirty Clebsch pairs.  For a descending endpoint string

    J >= I >= H >= G >= F >= E >= A >= X >= B >= C,

their sharp equal-coefficient comparison is `6*B8 <= 5*B9`.  The cleared
slack is a sum of twenty-nine nonnegative products in the nine successive
coefficient increments.  The reflective normalizer verifies the polynomial
identity without evaluating a growing physical rational convolution.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeEighthShell
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.P2HalfTimeNinthRatio

set_option maxHeartbeats 360000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2HalfTimeEighthRatio

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

private theorem add_nonneg {a b : Q'} (ha : (0 : Q') <= a)
    (hb : (0 : Q') <= b) : (0 : Q') <= a + b :=
  Q'.le_trans' _ ((0 : Q') + 0) _ (by decide) (Q'.add_le_add ha hb)

private inductive AllNonneg : List Q' -> Prop where
  | nil : AllNonneg []
  | cons {x : Q'} {xs : List Q'} :
      (0 : Q') <= x -> AllNonneg xs -> AllNonneg (x :: xs)

private theorem qSum_nonneg : ∀ xs : List Q',
    AllNonneg xs -> (0 : Q') <= qSum xs
  | [], .nil => by decide
  | [x], .cons hx .nil => hx
  | x :: y :: xs, .cons hx hxs =>
      add_nonneg hx (qSum_nonneg (y :: xs) hxs)

/-! ## 1. Endpoint polynomial and positive slack -/

/-- The thirty-pair depth-nine endpoint box. -/
def endpointBoxNineExpr (J I H G F E A X B C : Q') : Q' :=
  qSum [
    F * E, F * E,
    G * A, E * A, G * A, E * A,
    H * X, F * X, A * X, H * X, F * X, A * X,
    I * B, G * B, E * B, X * B,
    I * B, G * B, E * B, X * B,
    J * C, H * C, F * C, A * C, B * C,
    J * C, H * C, F * C, A * C, B * C]

private def ninthRatioSlack (J I H G F E A X B C : Q') : Q' :=
  let dJ := J + -I
  let dI := I + -H
  let dH := H + -G
  let dG := G + -F
  let dF := F + -E
  let dE := E + -A
  let dA := A + -X
  let dX := X + -B
  let dB := B + -C
  qSum [
    Q'.ofNat 10 * C * dJ,
    Q'.ofNat 8 * C * dI,
    Q'.ofNat 16 * C * dH,
    Q'.ofNat 12 * C * dG,
    Q'.ofNat 18 * C * dF,
    Q'.ofNat 12 * C * dE,
    Q'.ofNat 16 * C * dA,
    Q'.ofNat 8 * C * dX,
    Q'.ofNat 10 * C * dB,
    Q'.ofNat 10 * dI * dB,
    Q'.ofNat 10 * dH * dX,
    Q'.ofNat 8 * dH * dB,
    Q'.ofNat 10 * dG * dA,
    Q'.ofNat 8 * dG * dX,
    Q'.ofNat 16 * dG * dB,
    Q'.ofNat 10 * dF * dE,
    Q'.ofNat 8 * dF * dA,
    Q'.ofNat 16 * dF * dX,
    Q'.ofNat 12 * dF * dB,
    Q'.ofNat 4 * (dE * dE),
    Q'.ofNat 16 * dE * dA,
    Q'.ofNat 12 * dE * dX,
    Q'.ofNat 18 * dE * dB,
    Q'.ofNat 6 * (dA * dA),
    Q'.ofNat 18 * dA * dX,
    Q'.ofNat 12 * dA * dB,
    Q'.ofNat 6 * (dX * dX),
    Q'.ofNat 16 * dX * dB,
    Q'.ofNat 4 * (dB * dB)]

/-! ## 2. Reflected polynomial identity -/

private def pSum : List RingNormaliser.PolyExpr -> RingNormaliser.PolyExpr
  | [] => .const 0
  | [x] => x
  | x :: xs => .add x (pSum xs)

private def pTerm (n : Int) (a b : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := .mul (.mul (.const n) a) b

private def pSquare (n : Int) (a : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := .mul (.const n) (.mul a a)

private def ninthFactorLeft : RingNormaliser.PolyExpr :=
  let J := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let H := RingNormaliser.PolyExpr.var 2
  let G := RingNormaliser.PolyExpr.var 3
  let F := RingNormaliser.PolyExpr.var 4
  let E := RingNormaliser.PolyExpr.var 5
  let A := RingNormaliser.PolyExpr.var 6
  let X := RingNormaliser.PolyExpr.var 7
  let B := RingNormaliser.PolyExpr.var 8
  let C := RingNormaliser.PolyExpr.var 9
  let Y := pSum [
    .mul F E, .mul F E,
    .mul G A, .mul E A, .mul G A, .mul E A,
    .mul H X, .mul F X, .mul A X,
    .mul H X, .mul F X, .mul A X,
    .mul I B, .mul G B, .mul E B, .mul X B,
    .mul I B, .mul G B, .mul E B, .mul X B,
    .mul J C, .mul H C, .mul F C, .mul A C, .mul B C,
    .mul J C, .mul H C, .mul F C, .mul A C, .mul B C]
  .mul (.const 5) Y

private def ninthFactorRight : RingNormaliser.PolyExpr :=
  let J := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let H := RingNormaliser.PolyExpr.var 2
  let G := RingNormaliser.PolyExpr.var 3
  let F := RingNormaliser.PolyExpr.var 4
  let E := RingNormaliser.PolyExpr.var 5
  let A := RingNormaliser.PolyExpr.var 6
  let X := RingNormaliser.PolyExpr.var 7
  let B := RingNormaliser.PolyExpr.var 8
  let C := RingNormaliser.PolyExpr.var 9
  let Z := pSum [
    .mul E E, .mul F A, .mul F A, .mul A A,
    .mul G X, .mul E X, .mul G X, .mul E X, .mul X X,
    .mul H B, .mul F B, .mul A B,
    .mul H B, .mul F B, .mul A B, .mul B B,
    .mul I C, .mul G C, .mul E C, .mul X C,
    .mul I C, .mul G C, .mul E C, .mul X C, .mul C C]
  let dJ := .add J (.neg I)
  let dI := .add I (.neg H)
  let dH := .add H (.neg G)
  let dG := .add G (.neg F)
  let dF := .add F (.neg E)
  let dE := .add E (.neg A)
  let dA := .add A (.neg X)
  let dX := .add X (.neg B)
  let dB := .add B (.neg C)
  let slack := pSum [
    pTerm 10 C dJ, pTerm 8 C dI, pTerm 16 C dH,
    pTerm 12 C dG, pTerm 18 C dF, pTerm 12 C dE,
    pTerm 16 C dA, pTerm 8 C dX, pTerm 10 C dB,
    pTerm 10 dI dB, pTerm 10 dH dX, pTerm 8 dH dB,
    pTerm 10 dG dA, pTerm 8 dG dX, pTerm 16 dG dB,
    pTerm 10 dF dE, pTerm 8 dF dA, pTerm 16 dF dX,
    pTerm 12 dF dB, pSquare 4 dE, pTerm 16 dE dA,
    pTerm 12 dE dX, pTerm 18 dE dB, pSquare 6 dA,
    pTerm 18 dA dX, pTerm 12 dA dB, pSquare 6 dX,
    pTerm 16 dX dB, pSquare 4 dB]
  .add (.mul (.const 6) Z) slack

private theorem ninthFactor_normal :
    RingNormaliser.normalize ninthFactorLeft =
      RingNormaliser.normalize ninthFactorRight := by decide

private theorem ninth_factor_core (J I H G F E A X B C : Q') :
    Q'.ofNat 5 * endpointBoxNineExpr J I H G F E A X B C ≈
      Q'.ofNat 6 * endpointBoxEightExpr I H G F E A X B C +
        ninthRatioSlack J I H G F E A X B C := by
  simpa [endpointBoxNineExpr, endpointBoxEightExpr, ninthRatioSlack, qSum,
    ninthFactorLeft, ninthFactorRight, pSum, pTerm, pSquare,
    RingNormaliser.eval,
    show Q'.ofInt 4 = Q'.ofNat 4 from rfl,
    show Q'.ofInt 5 = Q'.ofNat 5 from rfl,
    show Q'.ofInt 6 = Q'.ofNat 6 from rfl,
    show Q'.ofInt 8 = Q'.ofNat 8 from rfl,
    show Q'.ofInt 10 = Q'.ofNat 10 from rfl,
    show Q'.ofInt 12 = Q'.ofNat 12 from rfl,
    show Q'.ofInt 16 = Q'.ofNat 16 from rfl,
    show Q'.ofInt 18 = Q'.ofNat 18 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      ninthFactorLeft ninthFactorRight ninthFactor_normal
      (fun | 0 => J | 1 => I | 2 => H | 3 => G | 4 => F |
        5 => E | 6 => A | 7 => X | 8 => B | _ => C))

/-! ## 3. Sharp ratio from descending endpoint coefficients -/

/-- For ten descending nonnegative endpoint coefficients, the twenty-five-pair
depth-eight box is at most `5/6` of the adjacent thirty-pair depth-nine box. -/
theorem ninthBoxRatio (J I H G F E A X B C : Q')
    (hIJ : I <= J) (hHI : H <= I) (hGH : G <= H)
    (hFG : F <= G) (hEF : E <= F) (hAE : A <= E)
    (hXA : X <= A) (hBX : B <= X) (hCB : C <= B)
    (hC0 : (0 : Q') <= C) :
    endpointBoxEightExpr I H G F E A X B C <=
      fiveSixths * endpointBoxNineExpr J I H G F E A X B C := by
  let dJ := J + -I
  let dI := I + -H
  let dH := H + -G
  let dG := G + -F
  let dF := F + -E
  let dE := E + -A
  let dA := A + -X
  let dX := X + -B
  let dB := B + -C
  let slack := ninthRatioSlack J I H G F E A X B C
  have hdJ0 : (0 : Q') <= dJ := by
    simpa only [dJ] using Q'.sub_nonneg_of_le hIJ
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
    dsimp only [slack, ninthRatioSlack, dJ, dI, dH, dG, dF, dE, dA, dX, dB]
    apply qSum_nonneg
    exact .cons (term hC0 hdJ0)
      (.cons (term hC0 hdI0)
        (.cons (term hC0 hdH0)
          (.cons (term hC0 hdG0)
            (.cons (term hC0 hdF0)
              (.cons (term hC0 hdE0)
                (.cons (term hC0 hdA0)
                  (.cons (term hC0 hdX0)
                    (.cons (term hC0 hdB0)
                      (.cons (term hdI0 hdB0)
                        (.cons (term hdH0 hdX0)
                          (.cons (term hdH0 hdB0)
                            (.cons (term hdG0 hdA0)
                              (.cons (term hdG0 hdX0)
                                (.cons (term hdG0 hdB0)
                                  (.cons (term hdF0 hdE0)
                                    (.cons (term hdF0 hdA0)
                                      (.cons (term hdF0 hdX0)
                                        (.cons (term hdF0 hdB0)
                                          (.cons (square hdE0)
                                            (.cons (term hdE0 hdA0)
                                              (.cons (term hdE0 hdX0)
                                                (.cons (term hdE0 hdB0)
                                                  (.cons (square hdA0)
                                                    (.cons (term hdA0 hdX0)
                                                      (.cons (term hdA0 hdB0)
                                                        (.cons (square hdX0)
                                                          (.cons (term hdX0 hdB0)
                                                            (.cons (square hdB0)
                                                              .nil))))))))))))))))))))))))))))
  have hsixthSlack0 : (0 : Q') <= oneSixth * slack :=
    Q'.mul_nonneg _ _ (by decide) hslack0
  let W := endpointBoxEightExpr I H G F E A X B C
  let Y := endpointBoxNineExpr J I H G F E A X B C
  have hfactor : fiveSixths * Y ≈ W + oneSixth * slack := by
    have h56 : fiveSixths ≈ Q'.ofNat 5 * oneSixth := by
      unfold fiveSixths oneSixth
      ring_qeqv
    have h16 : oneSixth * Q'.ofNat 6 ≈ (1 : Q') := by
      unfold oneSixth
      ring_qeqv
    have hcore : Q'.ofNat 5 * Y ≈ Q'.ofNat 6 * W + slack := by
      simpa only [W, Y, slack] using
        ninth_factor_core J I H G F E A X B C
    refine Q'.eqv_trans _ ((Q'.ofNat 5 * oneSixth) * Y) _
      (Q'.mul_eqv_congr_right _ _ Y h56) ?_
    refine Q'.eqv_trans _ (oneSixth * (Q'.ofNat 5 * Y)) _ ?_ ?_
    · refine Q'.eqv_trans _ ((oneSixth * Q'.ofNat 5) * Y) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ Y
          (Q'.mul_comm_eqv (Q'.ofNat 5) oneSixth)
      · exact Q'.mul_assoc_eqv oneSixth (Q'.ofNat 5) Y
    · refine Q'.eqv_trans _ (oneSixth * (Q'.ofNat 6 * W + slack)) _
        (Q'.mul_eqv_congr_left oneSixth _ _ hcore) ?_
      refine Q'.eqv_trans _
        (oneSixth * (Q'.ofNat 6 * W) + oneSixth * slack) _
        (Q'.mul_add_eqv oneSixth (Q'.ofNat 6 * W) slack) ?_
      refine Q'.add_eqv_congr_right _ _ (oneSixth * slack) ?_
      refine Q'.eqv_trans _ ((oneSixth * Q'.ofNat 6) * W) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv oneSixth (Q'.ofNat 6) W)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * W) _
        (Q'.mul_eqv_congr_right _ _ W h16) ?_
      exact Q'.one_mul_eqv W
  have hbase : W <= W + oneSixth * slack :=
    Q'.add_le_self_of_nonneg W (oneSixth * slack) hsixthSlack0
  change W <= fiveSixths * Y
  exact Q'.le_trans' _ _ _ hbase (Q'.ge_of_eqv hfactor)

end YMGap.Continuum.P2HalfTimeNinthRatio

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeNinthRatio.ninthBoxRatio
