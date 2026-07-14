/-
Constructive discrete-Gaussian decrement bounds for the cubic moment reserve.

The eighth-moment envelope is obtained by summation by parts.  Its local
engine is a quantitative reciprocal-Bernoulli estimate: while
`m * (1-b) <= 1/4`, at least four fifths of the linear decrement is realized
by `1-b^m`.  This file derives that estimate inside `Q'`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem envelope_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "envelope_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               envelope_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

def fourFifths : Q' := Q'.mkPos 4 5 (by decide)
def oneFifth : Q' := Q'.mkPos 1 5 (by decide)
def oneFourth : Q' := Q'.mkPos 1 4 (by decide)

private theorem one_sub_four_mul_nonnegative {x : Q'}
    (hx : x ≤ oneFourth) :
    (0 : Q') ≤ (1 : Q') + -(Q'.ofNat 4 * x) := by
  have h4 : (0 : Q') ≤ Q'.ofNat 4 := by decide
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4) hx h4
  have hquarter : Q'.ofNat 4 * oneFourth ≈ (1 : Q') := by
    unfold oneFourth
    envelope_ring
  have h4x : Q'.ofNat 4 * x ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hquarter)
  exact Q'.sub_nonneg_of_le h4x

private theorem q_le_total_local (a b : Q') : a ≤ b ∨ b ≤ a := by
  rcases Int.le_total (a.num * (b.den : Int))
      (b.num * (a.den : Int)) with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem neg_add_eqv_local (a b : Q') :
    -(a + b) ≈ (-a) + (-b) := by
  envelope_ring

private theorem left_add_cancel (p x : Q') :
    (p + fourFifths * x) + -p ≈ fourFifths * x := by
  let y := fourFifths * x
  refine Q'.eqv_trans _ (p + (y + -p)) _
    (Q'.add_assoc_eqv p y (-p)) ?_
  refine Q'.eqv_trans _ (p + ((-p) + y)) _
    (Q'.add_eqv_congr_left p _ _ (Q'.add_comm_eqv y (-p))) ?_
  refine Q'.eqv_trans _ ((p + -p) + y) _
    (Q'.eqv_symm (Q'.add_assoc_eqv p (-p) y)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + y) _
    (Q'.add_eqv_congr_right _ _ y (Q'.add_neg_self_eqv p)) ?_
  exact Q'.eqv_trans _ y (fourFifths * x)
    (Q'.eqv_of_eq (Q'.zero_add' y)) (Q'.eqv_refl _)

/-- Quantitative reciprocal Bernoulli.  On a quarter-sized exponent window,
the exact power decrement realizes at least four fifths of its linear term. -/
theorem qpow_decrement_ge_fourFifths_linear
    {b : Q'} (hb0 : (0 : Q') ≤ b) (hb1 : b ≤ (1 : Q'))
    (m : Nat)
    (hsmall : Q'.ofNat m * ((1 : Q') + -b) ≤ oneFourth) :
    fourFifths * (Q'.ofNat m * ((1 : Q') + -b)) ≤
      (1 : Q') + -(qpow b m) := by
  let u := (1 : Q') + -b
  let x := Q'.ofNat m * u
  let p := qpow b m
  have hu0 : (0 : Q') ≤ u := Q'.sub_nonneg_of_le hb1
  have hu1 : u ≤ (1 : Q') := by
    have hn : -b ≤ (0 : Q') := Q'.neg_le_neg hb0
    have h := Q'.add_le_add_left (1 : Q') _ _ hn
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hx0 : (0 : Q') ≤ x :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) hu0
  have hxsmall : x ≤ oneFourth := by
    dsimp only [x, u]
    exact hsmall
  have hbase : oneSub u ≈ b := by
    unfold oneSub
    dsimp only [u]
    refine Q'.eqv_trans _ ((1 : Q') + ((-1 : Q') + (-(-b)))) _
      (Q'.add_eqv_congr_left 1 _ _ (neg_add_eqv_local 1 (-b))) ?_
    refine Q'.eqv_trans _ ((1 : Q') + ((-1 : Q') + b)) _
      (Q'.add_eqv_congr_left 1 _ _
        (Q'.add_eqv_congr_left (-1) _ _ (Q'.neg_neg_eqv b))) ?_
    refine Q'.eqv_trans _ (((1 : Q') + (-1)) + b) _
      (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) b)) ?_
    refine Q'.eqv_trans _ ((0 : Q') + b) _
      (Q'.add_eqv_congr_right _ _ b (Q'.add_neg_self_eqv 1)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' b)
  have hpow : qpow (oneSub u) m ≈ p := by
    dsimp only [p]
    exact qpow_eqv_congr_base hbase m
  have hrecip0 := oneSub_pow_mul_bernDen_le hu0 hu1 m
  have hrecip : p * ((1 : Q') + x) ≤ (1 : Q') := by
    have heq : p * ((1 : Q') + x) ≈
        qpow (oneSub u) m * bernDen u m := by
      unfold bernDen
      dsimp only [x]
      exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hpow)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hrecip0
  have hc0 : (0 : Q') ≤ fourFifths := by
    unfold fourFifths
    decide
  have hsum : p + fourFifths * x ≤ (1 : Q') :=
    by
    rcases q_le_total_local fourFifths p with hcp | hp
    ·
      have hcx : fourFifths * x ≤ p * x :=
        Q'.mul_le_mul_of_nonneg_right _ _ x hcp hx0
      have hadd := Q'.add_le_add_left p _ _ hcx
      have hexpand : p + p * x ≈ p * ((1 : Q') + x) := by
        refine Q'.eqv_trans _ (p * 1 + p * x) _ ?_ ?_
        · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv p))
        · exact Q'.eqv_symm (Q'.mul_add_eqv p 1 x)
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand) hrecip)
    ·
      have hcx0 := Q'.mul_le_mul_of_nonneg_left _ _ fourFifths hxsmall hc0
      have hcx : fourFifths * x ≤ oneFifth :=
        Q'.le_trans' _ _ _ hcx0 (by
          unfold fourFifths oneFourth oneFifth
          decide)
      have hadd := Q'.add_le_add hp hcx
      exact Q'.le_trans' _ _ _ hadd (by
        unfold fourFifths oneFifth
        decide)
  have hshift := Q'.add_le_add_right _ _ (-p) hsum
  have hleft : (p + fourFifths * x) + -p ≈ fourFifths * x :=
    left_add_cancel p x
  have hright : (1 : Q') + -p ≈ (1 : Q') + -p := Q'.eqv_refl _
  dsimp only [x, u, p] at hleft hright hshift ⊢
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv hright))

/-- Squared base of the next-scale Gaussian moment. -/
def lowerSixNextGaussianBase (k : Nat) : Q' :=
  harmW (k + 1) * harmW (k + 1)

def lowerSixNextGaussianSeparation (k : Nat) : Q' :=
  (1 : Q') + -lowerSixNextGaussianBase k

theorem lowerSixNextGaussianBase_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixNextGaussianBase k := by
  unfold lowerSixNextGaussianBase
  exact Q'.mul_nonneg _ _ (harmW_nonneg (k + 1)) (harmW_nonneg (k + 1))

theorem lowerSixNextGaussianBase_le_one (k : Nat) :
    lowerSixNextGaussianBase k ≤ (1 : Q') := by
  unfold lowerSixNextGaussianBase
  have hmul := Q'.mul_le_mul_of_nonneg
    (harmW_le_one (k + 1)) (harmW_le_one (k + 1))
    (by decide) (harmW_nonneg (k + 1))
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv 1))

theorem lowerSixNextGaussianSeparation_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixNextGaussianSeparation k := by
  unfold lowerSixNextGaussianSeparation
  exact Q'.sub_nonneg_of_le (lowerSixNextGaussianBase_le_one k)

private abbrev PE := RingNormaliser.PolyExpr

private def pSquareSeparationL : PE :=
  let u : PE := .var 0
  .add (.const 1)
    (.neg (.mul (.add (.const 1) (.neg u))
      (.add (.const 1) (.neg u))))

private def pSquareSeparationR : PE :=
  let u : PE := .var 0
  .mul u (.add (.const 2) (.neg u))

private theorem pSquareSeparation_normal :
    RingNormaliser.normalize pSquareSeparationL =
      RingNormaliser.normalize pSquareSeparationR := by decide

private theorem square_separation_algebra (u : Q') :
    (1 : Q') + -(((1 : Q') + -u) * ((1 : Q') + -u)) ≈
      u * (Q'.ofNat 2 + -u) := by
  simpa [pSquareSeparationL, pSquareSeparationR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSquareSeparationL pSquareSeparationR pSquareSeparation_normal
      (fun _ => u))

private def pFifteenSeparationL : PE :=
  let u : PE := .var 0
  .mul (.const 8) (.mul u (.add (.const 2) (.neg u)))

private def pFifteenSeparationR : PE :=
  let u : PE := .var 0
  .add (.mul (.const 15) u)
    (.mul u (.add (.const 1) (.neg (.mul (.const 8) u))))

private theorem pFifteenSeparation_normal :
    RingNormaliser.normalize pFifteenSeparationL =
      RingNormaliser.normalize pFifteenSeparationR := by decide

private theorem fifteen_separation_algebra (u : Q') :
    Q'.ofNat 8 * (u * (Q'.ofNat 2 + -u)) ≈
      Q'.ofNat 15 * u +
        u * ((1 : Q') + -(Q'.ofNat 8 * u)) := by
  simpa [pFifteenSeparationL, pFifteenSeparationR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pFifteenSeparationL pFifteenSeparationR
      pFifteenSeparation_normal (fun _ => u))

private theorem eight_mul_unit_le_one_local (n : Nat) (hn : 8 ≤ n) :
    Q'.ofNat 8 * unit n (by omega) ≤ (1 : Q') := by
  unfold unit
  show (Q'.ofNat 8 * Q'.mkPos 1 n (by omega)).num *
      ((1 : Q').den : Int) ≤
    (1 : Q').num *
      ((Q'.ofNat 8 * Q'.mkPos 1 n (by omega)).den : Int)
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d]
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  exact_mod_cast hn

/-- The exact squared-harmonic separation is `(2D-1)/D²`; after clearing
one denominator it is at least `15/8` on every scale used by the campaign. -/
theorem fifteen_harmU_le_eight_nextGaussianSeparation
    {k : Nat} (hk : 5 ≤ k) :
    Q'.ofNat 15 * harmU (k + 1) ≤
      Q'.ofNat 8 * lowerSixNextGaussianSeparation k := by
  let u := harmU (k + 1)
  have hu0 : (0 : Q') ≤ u := harmU_nonneg (k + 1)
  have h8u : Q'.ofNat 8 * u ≤ (1 : Q') := by
    dsimp only [u]
    unfold harmU
    simpa only [show k + 1 + 2 = k + 3 by omega] using
      eight_mul_unit_le_one_local (k + 3) (by omega)
  have htail0 : (0 : Q') ≤ (1 : Q') + -(Q'.ofNat 8 * u) :=
    Q'.sub_nonneg_of_le h8u
  have hprod0 : (0 : Q') ≤
      u * ((1 : Q') + -(Q'.ofNat 8 * u)) :=
    Q'.mul_nonneg _ _ hu0 htail0
  have hadd : Q'.ofNat 15 * u ≤
      Q'.ofNat 15 * u +
        u * ((1 : Q') + -(Q'.ofNat 8 * u)) :=
    Q'.add_le_self_of_nonneg _ _ hprod0
  have hsep : lowerSixNextGaussianSeparation k ≈
      u * (Q'.ofNat 2 + -u) := by
    unfold lowerSixNextGaussianSeparation lowerSixNextGaussianBase
      harmW oneSub
    dsimp only [u]
    exact square_separation_algebra _
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (fifteen_separation_algebra u))
        (Q'.mul_eqv_congr_left (Q'.ofNat 8) _ _ (Q'.eqv_symm hsep))))

/-- Exact one-step factorization of the next-scale Gaussian weight. -/
theorem lowerSixNextGaussianWeight_step_eqv (k n : Nat) :
    lowerSixModeWeight (k + 1) (n + 1) ≈
      lowerSixModeWeight (k + 1) n *
        qpow (lowerSixNextGaussianBase k) (2 * n + 1) := by
  have hidx : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  unfold lowerSixModeWeight lowerSixNextGaussianBase
  rw [hidx]
  exact HeatKernelRGStep.qpow_add _ _ _

private theorem next_harmU_mul_den_eqv_one (k : Nat) :
    Q'.ofNat (k + 3) * harmU (k + 1) ≈ (1 : Q') := by
  unfold harmU unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

/-- Cleared scalar form of the harmonic decrement.  The constants are exact:
`(4/5) * (2n+1) * (2D-1)/D²`, after multiplying by `D`, dominates `3n`. -/
theorem three_mode_le_scaled_fourFifths_separation
    {k : Nat} (hk : 5 ≤ k) (n : Nat) :
    Q'.ofNat 3 * Q'.ofNat n ≤
      Q'.ofNat (k + 3) *
        (fourFifths *
          (Q'.ofNat (2 * n + 1) * lowerSixNextGaussianSeparation k)) := by
  let D := Q'.ofNat (k + 3)
  let N := Q'.ofNat n
  let M := Q'.ofNat (2 * n + 1)
  let U := harmU (k + 1)
  let S := lowerSixNextGaussianSeparation k
  have hS0 : (0 : Q') ≤ S := lowerSixNextGaussianSeparation_nonnegative k
  have h8S0 : (0 : Q') ≤ Q'.ofNat 8 * S :=
    Q'.mul_nonneg _ _ (by decide) hS0
  have h2nM : Q'.ofNat (2 * n) ≤ M := by
    dsimp only [M]
    exact CReal.ofNat_le_ofNat (by omega)
  have hsep : Q'.ofNat 15 * U ≤ Q'.ofNat 8 * S := by
    dsimp only [U, S]
    exact fifteen_harmU_le_eight_nextGaussianSeparation hk
  have hmul1 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (2 * n))
    hsep (HeatKernelRGStep.zero_le_ofNat _)
  have hmul2 := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.ofNat 8 * S)
    h2nM h8S0
  have h30_8M : (Q'.ofNat 30 * N) * U ≤
      M * (Q'.ofNat 8 * S) := by
    have hleft : Q'.ofNat (2 * n) * (Q'.ofNat 15 * U) ≈
        (Q'.ofNat 30 * N) * U := by
      dsimp only [N]
      have hcast := HeatKernelRGStep.ofNat_mul_eqv 2 n
      refine Q'.eqv_trans _ ((Q'.ofNat 2 * Q'.ofNat n) *
        (Q'.ofNat 15 * U)) _
        (Q'.mul_eqv_congr_right _ _ _ hcast) ?_
      envelope_ring
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hmul1 hmul2)
  have hDmul := Q'.mul_le_mul_of_nonneg_left _ _ D h30_8M
    (HeatKernelRGStep.zero_le_ofNat _)
  have h30_8DM : Q'.ofNat 30 * N ≤
      Q'.ofNat 8 * (D * (M * S)) := by
    have hdu : D * U ≈ (1 : Q') := by
      dsimp only [D, U]
      exact next_harmU_mul_den_eqv_one k
    have hleft : D * ((Q'.ofNat 30 * N) * U) ≈
        Q'.ofNat 30 * N := by
      refine Q'.eqv_trans _ ((Q'.ofNat 30 * N) * (D * U)) _ ?_ ?_
      · envelope_ring
      · refine Q'.eqv_trans _ ((Q'.ofNat 30 * N) * 1) _
          (Q'.mul_eqv_congr_left _ _ _ hdu) ?_
        exact Q'.mul_one_eqv _
    have hright : D * (M * (Q'.ofNat 8 * S)) ≈
        Q'.ofNat 8 * (D * (M * S)) := by envelope_ring
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hDmul (Q'.le_of_eqv hright))
  have h15_4DM : Q'.ofNat 15 * N ≤
      Q'.ofNat 4 * (D * (M * S)) := by
    have htwo : (0 : Q') < Q'.ofNat 2 := by decide
    have hscaled : Q'.ofNat 2 * (Q'.ofNat 15 * N) ≤
        Q'.ofNat 2 * (Q'.ofNat 4 * (D * (M * S))) := by
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by envelope_ring))
        (Q'.le_trans' _ _ _ h30_8DM (Q'.le_of_eqv (by envelope_ring)))
    exact Q'.le_of_mul_le_mul_left hscaled htwo
  have hc : Q'.ofNat 5 * fourFifths ≈ Q'.ofNat 4 := by
    unfold fourFifths
    envelope_ring
  have hfive : (0 : Q') < Q'.ofNat 5 := by decide
  have hscaled : Q'.ofNat 5 * (Q'.ofNat 3 * N) ≤
      Q'.ofNat 5 * (D * (fourFifths * (M * S))) := by
    have hleft : Q'.ofNat 5 * (Q'.ofNat 3 * N) ≈
        Q'.ofNat 15 * N := by envelope_ring
    have hright : Q'.ofNat 5 * (D * (fourFifths * (M * S))) ≈
        Q'.ofNat 4 * (D * (M * S)) := by
      refine Q'.eqv_trans _ ((Q'.ofNat 5 * fourFifths) *
        (D * (M * S))) _ ?_ ?_
      · envelope_ring
      · exact Q'.mul_eqv_congr_right _ _ _ hc
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ h15_4DM (Q'.ge_of_eqv hright))
  dsimp only [D, N, M, S] at hscaled ⊢
  exact Q'.le_of_mul_le_mul_left hscaled hfive

/-- Weighted Gaussian decrement in the exact form used by finite summation by
parts.  No asymptotic exponential estimate enters: this is reciprocal
Bernoulli plus the exact harmonic separation. -/
theorem three_mode_weight_le_scaled_nextDifference
    {k : Nat} (hk : 5 ≤ k) (n : Nat)
    (hsmall :
      Q'.ofNat (2 * n + 1) * lowerSixNextGaussianSeparation k ≤
        oneFourth) :
    (Q'.ofNat 3 * Q'.ofNat n) * lowerSixModeWeight (k + 1) n ≤
      Q'.ofNat (k + 3) *
        (lowerSixModeWeight (k + 1) n +
          -lowerSixModeWeight (k + 1) (n + 1)) := by
  let b := lowerSixNextGaussianBase k
  let S := lowerSixNextGaussianSeparation k
  let m := 2 * n + 1
  let W := lowerSixModeWeight (k + 1) n
  let W1 := lowerSixModeWeight (k + 1) (n + 1)
  let r := qpow b m
  let A := fourFifths * (Q'.ofNat m * S)
  let D := Q'.ofNat (k + 3)
  let N3 := Q'.ofNat 3 * Q'.ofNat n
  have hW0 : (0 : Q') ≤ W := lowerSixModeWeight_nonnegative (k + 1) n
  have hscalar : N3 ≤ D * A := by
    dsimp only [N3, D, A, m, S]
    exact three_mode_le_scaled_fourFifths_separation hk n
  have hdec : A ≤ (1 : Q') + -r := by
    dsimp only [A, m, S, r, b]
    exact qpow_decrement_ge_fourFifths_linear
      (lowerSixNextGaussianBase_nonnegative k)
      (lowerSixNextGaussianBase_le_one k) (2 * n + 1) hsmall
  have hmul1 := Q'.mul_le_mul_of_nonneg_left _ _ W hscalar hW0
  have hDA0 : (0 : Q') ≤ D := HeatKernelRGStep.zero_le_ofNat _
  have hmul2raw := Q'.mul_le_mul_of_nonneg_left _ _ D hdec hDA0
  have hmul2 := Q'.mul_le_mul_of_nonneg_left _ _ W hmul2raw hW0
  have hchain : W * N3 ≤ W * (D * ((1 : Q') + -r)) :=
    Q'.le_trans' _ _ _ hmul1 hmul2
  have hstep : W1 ≈ W * r := by
    dsimp only [W1, W, r, b, m]
    exact lowerSixNextGaussianWeight_step_eqv k n
  have hright : W * (D * ((1 : Q') + -r)) ≈
      D * (W + -W1) := by
    refine Q'.eqv_trans _ (D * (W * ((1 : Q') + -r))) _ ?_ ?_
    · envelope_ring
    refine Q'.eqv_trans _ (D * (W + -(W * r))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left D _ _ (by
        refine Q'.eqv_trans _ (W * 1 + W * (-r)) _
          (Q'.mul_add_eqv W 1 (-r)) ?_
        refine Q'.eqv_trans _ (W + W * (-r)) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv W)) ?_
        exact Q'.add_eqv_congr_left W _ _ (Q'.mul_neg_eqv W r))
    · exact Q'.mul_eqv_congr_left D _ _
        (Q'.add_eqv_congr_left W _ _
          (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hstep)))
  dsimp only [W, W1, D, N3] at hchain hright ⊢
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hchain)
    (Q'.le_of_eqv hright)

#print axioms qpow_decrement_ge_fourFifths_linear
#print axioms lowerSixNextGaussianBase_nonnegative
#print axioms lowerSixNextGaussianBase_le_one
#print axioms fifteen_harmU_le_eight_nextGaussianSeparation
#print axioms lowerSixNextGaussianWeight_step_eqv
#print axioms three_mode_le_scaled_fourFifths_separation
#print axioms three_mode_weight_le_scaled_nextDifference

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope
