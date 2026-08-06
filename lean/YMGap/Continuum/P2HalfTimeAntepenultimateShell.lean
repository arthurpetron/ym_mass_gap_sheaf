/-
Track 11.7-fusion / R4o -- exact antepenultimate half-time shell.

At channel `s = 2*N-3`, the adjacent Clebsch boxes have four and six
endpoint pairs.  For descending endpoint coefficients `A >= X >= B >= C`,
their scalar difference has the manifest sum-of-products factorization

  2*T - 3*E
    = 4*(A-X)*C + (B-C)^2 + 4*(B-C)*C
      + 4*(B-C)*(X-B) + 2*C*(X-B).

Thus `E <= (2/3)*T`.  The same physical Bernoulli floor used by the
penultimate shell pays the factor `2/3`, while dimension monotonicity pays
the adjacent channel.  No growing convolution is evaluated.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimePenultimateShell
import YMGap.Continuum.P2RetunedFenceSecondShell
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.P2HalfTimeAntepenultimateShell

set_option maxHeartbeats 200000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2HalfTimePenultimateShell
open YMGap.Continuum.P2RetunedFenceSecondShell
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

/-! The nonlinear shell identity is certified at the polynomial-syntax level.
This keeps the kernel computation on sparse integer coefficients instead of
expanding the unnormalised denominators of four arbitrary `Q'` variables. -/

private def shellFactorLeft : RingNormaliser.PolyExpr :=
  let A := RingNormaliser.PolyExpr.var 0
  let X := RingNormaliser.PolyExpr.var 1
  let B := RingNormaliser.PolyExpr.var 2
  let C := RingNormaliser.PolyExpr.var 3
  let T :=
    .add (.add (.mul X B) (.mul X B))
      (.add (.add (.mul A C) (.mul B C))
        (.add (.mul A C) (.mul B C)))
  .mul (.const 2) T

private def shellFactorRight : RingNormaliser.PolyExpr :=
  let A := RingNormaliser.PolyExpr.var 0
  let X := RingNormaliser.PolyExpr.var 1
  let B := RingNormaliser.PolyExpr.var 2
  let C := RingNormaliser.PolyExpr.var 3
  let E :=
    .add (.mul B B)
      (.add (.mul X C) (.add (.mul X C) (.mul C C)))
  let dA := .add A (.neg X)
  let dX := .add X (.neg B)
  let dB := .add B (.neg C)
  let slack :=
    .add (.mul (.mul (.const 4) dA) C)
      (.add (.mul dB dB)
        (.add (.mul (.mul (.const 4) dB) C)
          (.add (.mul (.mul (.const 4) dB) dX)
            (.mul (.mul (.const 2) C) dX))))
  .add (.mul (.const 3) E) slack

private theorem shellFactor_normal :
    RingNormaliser.normalize shellFactorLeft =
      RingNormaliser.normalize shellFactorRight := by decide

private theorem shell_factor_core (A X B C : Q') :
    Q'.ofNat 2 *
        (((X * B) + (X * B)) +
          ((A * C + B * C) + (A * C + B * C))) ≈
      Q'.ofNat 3 *
          (B * B + (X * C + (X * C + C * C))) +
        (Q'.ofNat 4 * (A + -X) * C +
          ((B + -C) * (B + -C) +
            (Q'.ofNat 4 * (B + -C) * C +
              (Q'.ofNat 4 * (B + -C) * (X + -B) +
                Q'.ofNat 2 * C * (X + -B))))) := by
  simpa [shellFactorLeft, shellFactorRight, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      shellFactorLeft shellFactorRight shellFactor_normal
      (fun | 0 => A | 1 => X | 2 => B | _ => C))

/-! ## 1. Constant-size six-pair scalar -/

/-- The four endpoint box is at most two thirds of the adjacent six-pair
box whenever the four terminal heat coefficients are descending. -/
theorem antepenultimateBoxRatio (A X B C : Q')
    (hXA : X <= A) (hBX : B <= X) (hCB : C <= B)
    (hC0 : (0 : Q') <= C) :
    B * B + (X * C + (X * C + C * C)) <=
      twoThirds *
        (((X * B) + (X * B)) +
          ((A * C + B * C) + (A * C + B * C))) := by
  let E := B * B + (X * C + (X * C + C * C))
  let T := ((X * B) + (X * B)) +
    ((A * C + B * C) + (A * C + B * C))
  let dA := A + -X
  let dX := X + -B
  let dB := B + -C
  let slack :=
    Q'.ofNat 4 * dA * C +
      (dB * dB +
        (Q'.ofNat 4 * dB * C +
          (Q'.ofNat 4 * dB * dX + Q'.ofNat 2 * C * dX)))
  have hdA0 : (0 : Q') <= dA := by
    simpa only [dA] using Q'.sub_nonneg_of_le hXA
  have hdX0 : (0 : Q') <= dX := by
    simpa only [dX] using Q'.sub_nonneg_of_le hBX
  have hdB0 : (0 : Q') <= dB := by
    simpa only [dB] using Q'.sub_nonneg_of_le hCB
  have h4dAC0 : (0 : Q') <= Q'.ofNat 4 * dA * C :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) hdA0) hC0
  have hdBsq0 : (0 : Q') <= dB * dB := Q'.mul_nonneg _ _ hdB0 hdB0
  have h4dBC0 : (0 : Q') <= Q'.ofNat 4 * dB * C :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) hdB0) hC0
  have h4dBdX0 : (0 : Q') <= Q'.ofNat 4 * dB * dX :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) hdB0) hdX0
  have h2CdX0 : (0 : Q') <= Q'.ofNat 2 * C * dX :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) hC0) hdX0
  have hslack0 : (0 : Q') <= slack := by
    exact add_nonneg h4dAC0
      (add_nonneg hdBsq0
        (add_nonneg h4dBC0 (add_nonneg h4dBdX0 h2CdX0)))
  have hthirdSlack0 : (0 : Q') <= oneThird * slack :=
    Q'.mul_nonneg _ _ (by decide) hslack0
  have hfactor : twoThirds * T ≈ E + oneThird * slack := by
    have h23 : twoThirds ≈ Q'.ofNat 2 * oneThird := by
      unfold twoThirds oneThird
      ring_qeqv
    have h13 : oneThird * Q'.ofNat 3 ≈ (1 : Q') := by
      unfold oneThird
      ring_qeqv
    have hcore : Q'.ofNat 2 * T ≈ Q'.ofNat 3 * E + slack := by
      simpa only [E, T, slack, dA, dX, dB] using
        shell_factor_core A X B C
    refine Q'.eqv_trans _ ((Q'.ofNat 2 * oneThird) * T) _
      (Q'.mul_eqv_congr_right _ _ T h23) ?_
    refine Q'.eqv_trans _ (oneThird * (Q'.ofNat 2 * T)) _ ?_ ?_
    · refine Q'.eqv_trans _ ((oneThird * Q'.ofNat 2) * T) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ T
          (Q'.mul_comm_eqv (Q'.ofNat 2) oneThird)
      · exact Q'.mul_assoc_eqv oneThird (Q'.ofNat 2) T
    · refine Q'.eqv_trans _ (oneThird * (Q'.ofNat 3 * E + slack)) _
        (Q'.mul_eqv_congr_left oneThird _ _ hcore) ?_
      refine Q'.eqv_trans _
        (oneThird * (Q'.ofNat 3 * E) + oneThird * slack) _
        (Q'.mul_add_eqv oneThird (Q'.ofNat 3 * E) slack) ?_
      refine Q'.add_eqv_congr_right _ _ (oneThird * slack) ?_
      refine Q'.eqv_trans _ ((oneThird * Q'.ofNat 3) * E) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv oneThird (Q'.ofNat 3) E)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * E) _
        (Q'.mul_eqv_congr_right _ _ E h13) ?_
      exact Q'.one_mul_eqv E
  have hbase : E <= E + oneThird * slack :=
    Q'.add_le_self_of_nonneg E (oneThird * slack) hthirdSlack0
  change E <= twoThirds * T
  exact Q'.le_trans' _ _ _ hbase (Q'.ge_of_eqv hfactor)

/-- The `2/3` box comparison, adjacent dimension monotonicity, and heat floor
prove the abstract antepenultimate half-time cell. -/
theorem antepenultimateHalfTimeScalar (w : Q') (N : Nat)
    (hw0 : (0 : Q') <= w) (hN : 3 <= N)
    (hpow : twoThirds <= qpow w (2 * N - 1))
    (hXA : coeffW w (N - 2) <= coeffW w (N - 3))
    (hBX : coeffW w (N - 1) <= coeffW w (N - 2))
    (hCB : coeffW w N <= coeffW w (N - 1)) :
    dimQ (2 * N - 3) *
        ((coeffW w (N - 1) * coeffW w (N - 1)) +
          ((coeffW w (N - 2) * coeffW w N) +
            ((coeffW w (N - 2) * coeffW w N) +
              coeffW w N * coeffW w N))) <=
      qpow w (2 * N - 1) *
        (dimQ (2 * N - 2) *
          (((coeffW w (N - 2) * coeffW w (N - 1)) +
              (coeffW w (N - 2) * coeffW w (N - 1))) +
            (((coeffW w (N - 3) * coeffW w N +
                coeffW w (N - 1) * coeffW w N) +
              (coeffW w (N - 3) * coeffW w N +
                coeffW w (N - 1) * coeffW w N))))) := by
  let A := coeffW w (N - 3)
  let X := coeffW w (N - 2)
  let B := coeffW w (N - 1)
  let C := coeffW w N
  let E := B * B + (X * C + (X * C + C * C))
  let T := ((X * B) + (X * B)) +
    ((A * C + B * C) + (A * C + B * C))
  let low := dimQ (2 * N - 3)
  let high := dimQ (2 * N - 2)
  have hA0 : (0 : Q') <= A := coeffW_nonneg hw0 (N - 3)
  have hX0 : (0 : Q') <= X := coeffW_nonneg hw0 (N - 2)
  have hB0 : (0 : Q') <= B := coeffW_nonneg hw0 (N - 1)
  have hC0 : (0 : Q') <= C := coeffW_nonneg hw0 N
  have hE0 : (0 : Q') <= E := by
    exact add_nonneg (Q'.mul_nonneg _ _ hB0 hB0)
      (add_nonneg (Q'.mul_nonneg _ _ hX0 hC0)
        (add_nonneg (Q'.mul_nonneg _ _ hX0 hC0)
          (Q'.mul_nonneg _ _ hC0 hC0)))
  have hT0 : (0 : Q') <= T := by
    exact add_nonneg
      (add_nonneg (Q'.mul_nonneg _ _ hX0 hB0)
        (Q'.mul_nonneg _ _ hX0 hB0))
      (add_nonneg
        (add_nonneg (Q'.mul_nonneg _ _ hA0 hC0)
          (Q'.mul_nonneg _ _ hB0 hC0))
        (add_nonneg (Q'.mul_nonneg _ _ hA0 hC0)
          (Q'.mul_nonneg _ _ hB0 hC0)))
  have hratio : E <= twoThirds * T := by
    simpa only [A, X, B, C, E, T] using
      antepenultimateBoxRatio A X B C hXA hBX hCB hC0
  have hdim : low <= high := by
    have hnat : 2 * N - 3 + 1 <= 2 * N - 2 + 1 := by omega
    simpa only [low, high, dimQ] using ofNat_le_ofNat hnat
  have hdimScaled : low * E <= high * E :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdim hE0
  have hhigh0 : (0 : Q') <= high := by
    unfold high dimQ
    exact HeatKernelRGStep.zero_le_ofNat _
  have hratioScaled : high * E <= high * (twoThirds * T) :=
    Q'.mul_le_mul_of_nonneg_left _ _ high hratio hhigh0
  have hreorder : high * (twoThirds * T) ≈ twoThirds * (high * T) := by
    ring_qeqv
  have hhighT0 : (0 : Q') <= high * T := Q'.mul_nonneg _ _ hhigh0 hT0
  have hpowScaled : twoThirds * (high * T) <=
      qpow w (2 * N - 1) * (high * T) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hhighT0
  change low * E <= qpow w (2 * N - 1) * (high * T)
  exact Q'.le_trans' _ _ _ hdimScaled
    (Q'.le_trans' _ _ _ hratioScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hpowScaled))

/-! ## 2. Physical schedule and exact box transport -/

theorem physical_twoThirds_power_floor_antepenultimate (r : Nat) :
    twoThirds <=
      qpow (blockWeight (r + 4)) (2 * blockNcut (r + 4) - 1) := by
  have hfloor := physical_twoThirds_power_floor r
  have hmono := HeatKernelRGStep.qpow_antitone
    (blockWeight_nonneg (r + 4)) (blockWeight_le_one (r + 4))
    (2 * blockNcut (r + 4) - 1) (2 * blockNcut (r + 4)) (by
      have := blockNcut_pos (r + 4)
      omega)
  exact Q'.le_trans' _ _ _ hfloor hmono

theorem halfTimeBox_antepenultimate_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 3) * boxSum (blockWeight k) N (2 * N - 2) <=
      qpow (blockWeight k) (2 * N - 1) *
        (dimQ (2 * N - 2) * boxSum (blockWeight k) N (2 * N - 3)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hN : 3 <= N := Nat.le_trans (by decide : 3 <= 79) (by
    simpa only [k, N] using P2HalfTimePenultimateShell.blockNcut_ge_79 r)
  have hscalar := antepenultimateHalfTimeScalar w N
    (blockWeight_nonneg k) hN
    (by simpa only [k, N, w] using
      physical_twoThirds_power_floor_antepenultimate r)
    (by simpa only [k, N, w] using
      physical_prepenultimate_coeff_descending r)
    (by simpa only [k, N, w] using
      physical_penultimate_coeff_descending r)
    (by simpa only [k, N, w] using
      physical_terminal_coeff_descending_from_four r)
  have eleft :
      dimQ (2 * N - 3) * boxSum w N (2 * N - 2) ≈
        dimQ (2 * N - 3) *
          ((coeffW w (N - 1) * coeffW w (N - 1)) +
            ((coeffW w (N - 2) * coeffW w N) +
              ((coeffW w (N - 2) * coeffW w N) +
                coeffW w N * coeffW w N))) :=
    Q'.mul_eqv_congr_left _ _ _
      (P2RetunedFenceTopShell.boxSum_top_even w N (by omega))
  have eright :
      qpow w (2 * N - 1) *
          (dimQ (2 * N - 2) *
            (((coeffW w (N - 2) * coeffW w (N - 1)) +
                (coeffW w (N - 2) * coeffW w (N - 1))) +
              (((coeffW w (N - 3) * coeffW w N +
                  coeffW w (N - 1) * coeffW w N) +
                (coeffW w (N - 3) * coeffW w N +
                  coeffW w (N - 1) * coeffW w N))))) ≈
        qpow w (2 * N - 1) *
          (dimQ (2 * N - 2) * boxSum w N (2 * N - 3)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm
        (boxSum_top_three w N hN)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hscalar (Q'.le_of_eqv eright))

theorem halfTimeLineSum_antepenultimate_physical (r : Nat) :
    let k := r + 4
    let N := blockNcut k
    dimQ (2 * N - 3) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 2) <=
      qpow (blockWeight k) (2 * N - 1) *
        (dimQ (2 * N - 2) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 3)) := by
  let k := r + 4
  let N := blockNcut k
  let w := blockWeight k
  have hbox := halfTimeBox_antepenultimate_physical r
  have eleft :
      dimQ (2 * N - 3) * lineSum (lagCorr w N) (2 * N - 2) ≈
        dimQ (2 * N - 3) * boxSum w N (2 * N - 2) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (2 * N - 2)))
  have eright :
      qpow w (2 * N - 1) *
          (dimQ (2 * N - 2) * boxSum w N (2 * N - 3)) ≈
        qpow w (2 * N - 1) *
          (dimQ (2 * N - 2) * lineSum (lagCorr w N) (2 * N - 3)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N (2 * N - 3)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ (by simpa only [k, N, w] using hbox)
      (Q'.le_of_eqv eright))

/-- Every physical scale `k >= 4` inherits the constant-cost
antepenultimate-shell proof. -/
theorem physical_halfTime_lineSum_antepenultimate_from_four
    (k : Nat) (hk : 4 <= k) :
    let N := blockNcut k
    dimQ (2 * N - 3) *
        lineSum (lagCorr (blockWeight k) N) (2 * N - 2) <=
      qpow (blockWeight k) (2 * N - 1) *
        (dimQ (2 * N - 2) *
          lineSum (lagCorr (blockWeight k) N) (2 * N - 3)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm] using halfTimeLineSum_antepenultimate_physical r

end YMGap.Continuum.P2HalfTimeAntepenultimateShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeAntepenultimateShell.antepenultimateBoxRatio
#print axioms YMGap.Continuum.P2HalfTimeAntepenultimateShell.antepenultimateHalfTimeScalar
#print axioms YMGap.Continuum.P2HalfTimeAntepenultimateShell.physical_twoThirds_power_floor_antepenultimate
#print axioms YMGap.Continuum.P2HalfTimeAntepenultimateShell.halfTimeBox_antepenultimate_physical
#print axioms YMGap.Continuum.P2HalfTimeAntepenultimateShell.halfTimeLineSum_antepenultimate_physical
#print axioms YMGap.Continuum.P2HalfTimeAntepenultimateShell.physical_halfTime_lineSum_antepenultimate_from_four
