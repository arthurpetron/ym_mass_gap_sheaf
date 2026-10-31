/-
Exact Dirichlet form of the remaining six-unit growing-head lower bound.

Writing `x_n = n w^(n^2)`, the cubic margin is exactly

  4 * sum_{n=1}^N (x_n-x_(n+1))^2
    + 4*x_1^2 - 4*x_(N+1)^2
    - (12u+u^3) * sum_{n=1}^N x_n^2.

Thus the remaining all-scale statement is a finite, cancellation-preserving
Poincare payment.  The pointwise version is false already at `k=10,n=3`,
while the full payment at `k=10` is true.  This rules out local allocation
without refuting the target.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixCoefficientFence
import YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet

namespace YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossPascalReduction
open YMGap.Continuum.HarmonicMassCrossResidualSandwich
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem lower_dirichlet_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "lower_dirichlet_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               lower_dirichlet_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private def lowerComplementL : RingNormaliser.PolyExpr :=
  let R := RingNormaliser.PolyExpr.var 0
  let U := RingNormaliser.PolyExpr.var 1
  let I := RingNormaliser.PolyExpr.var 2
  .add R (.neg (.mul (.mul (.const 6) U) I))

private def lowerComplementR : RingNormaliser.PolyExpr :=
  let R := RingNormaliser.PolyExpr.var 0
  let U := RingNormaliser.PolyExpr.var 1
  let I := RingNormaliser.PolyExpr.var 2
  .add (.mul U I)
    (.neg (.add (.mul (.mul (.const 7) U) I) (.neg R)))

private theorem lowerComplement_normal :
    RingNormaliser.normalize lowerComplementL =
      RingNormaliser.normalize lowerComplementR := by decide

private theorem lower_complement_algebra (R U I : Q') :
    R + -((Q'.ofNat 6 * U) * I) ≈
      U * I + -((Q'.ofNat 7 * U) * I + -R) := by
  simpa [lowerComplementL, lowerComplementR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      lowerComplementL lowerComplementR lowerComplement_normal
      (fun | 0 => R | 1 => U | _ => I))

private def lowerRearrangeL : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let E := RingNormaliser.PolyExpr.var 2
  let B := RingNormaliser.PolyExpr.var 3
  let D := RingNormaliser.PolyExpr.var 4
  let P := .mul u (.add (.add (.const 12) u) (.mul u u))
  .add (.mul (.mul u u) I)
    (.neg (.add (.add (.mul P I) (.mul (.const 4) (.add E (.neg B))))
      (.neg (.mul (.const 4) D))))

private def lowerRearrangeR : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let E := RingNormaliser.PolyExpr.var 2
  let B := RingNormaliser.PolyExpr.var 3
  let D := RingNormaliser.PolyExpr.var 4
  let p := .mul u (.add (.const 12) (.mul u u))
  .add
    (.add (.add (.mul (.const 4) D) (.neg (.mul p I)))
      (.mul (.const 4) B))
    (.neg (.mul (.const 4) E))

private theorem lowerRearrange_normal :
    RingNormaliser.normalize lowerRearrangeL =
      RingNormaliser.normalize lowerRearrangeR := by decide

private theorem lower_rearrange_algebra (u I E B D : Q') :
    (u * u) * I +
        -((u * ((Q'.ofNat 12 + u) + u * u)) * I +
          Q'.ofNat 4 * (E + -B) + -(Q'.ofNat 4 * D)) ≈
      (Q'.ofNat 4 * D +
          -((u * (Q'.ofNat 12 + u * u)) * I)) +
        Q'.ofNat 4 * B + -(Q'.ofNat 4 * E) := by
  simpa [lowerRearrangeL, lowerRearrangeR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      lowerRearrangeL lowerRearrangeR lowerRearrange_normal
      (fun | 0 => u | 1 => I | 2 => E | 3 => B | _ => D))

/-- The exact Poincare coefficient in the lower-six gap. -/
def lowerSixDirichletProfile (k : Nat) : Q' :=
  harmU k * (Q'.ofNat 12 + harmU k * harmU k)

/-- A single signed Poincare cell.  It is deliberately not asserted
nonnegative: cancellation between its central negative band and both tails
is essential. -/
def lowerSixDirichletIncrement (k n : Nat) : Q' :=
  Q'.ofNat 4 * thetaDirichletCell (harmW k) n +
    -(lowerSixDirichletProfile k * integerThetaTerm (harmW k) n)

/-- The complete retained Dirichlet block, including every half-edge in the
growing head. -/
def lowerSixDirichletSum (k : Nat) : Q' :=
  finSum (fun j => lowerSixDirichletIncrement k (j + 1))
    (growingAnchor k + 1)

private theorem finSum_lowerSixDirichletIncrement (k : Nat) : ∀ N,
    finSum (fun j => lowerSixDirichletIncrement k (j + 1)) N ≈
      Q'.ofNat 4 *
          finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) N +
        -(lowerSixDirichletProfile k *
          finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N)
  | 0 => by
      simp only [finSum_zero]
      have hfour : Q'.ofNat 4 * (0 : Q') ≈ 0 :=
        Q'.mul_zero_eqv _
      have hprofile :
          -(lowerSixDirichletProfile k * (0 : Q')) ≈ 0 := by
        exact Q'.eqv_trans _ (-(0 : Q')) _
          (Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv _)) (by decide)
      have hr := Q'.add_eqv_congr' hfour hprofile
      exact Q'.eqv_trans _ ((0 : Q') + 0) _ (by decide)
        (Q'.eqv_symm hr)
  | N + 1 => by
      simp only [finSum_succ]
      refine Q'.eqv_trans _
        ((Q'.ofNat 4 *
              finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) N +
            -(lowerSixDirichletProfile k *
              finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N)) +
          lowerSixDirichletIncrement k (N + 1)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (finSum_lowerSixDirichletIncrement k N)
      · unfold lowerSixDirichletIncrement
        lower_dirichlet_ring

/-- Sum-level expansion of the signed Poincare cells. -/
theorem lowerSixDirichletSum_eqv (k : Nat) :
    lowerSixDirichletSum k ≈
      Q'.ofNat 4 *
          finSum (fun j => thetaDirichletCell (harmW k) (j + 1))
            (growingAnchor k + 1) +
        -(lowerSixDirichletProfile k *
          integerThetaSum (harmW k) (growingAnchor k)) := by
  unfold lowerSixDirichletSum integerThetaSum
  exact finSum_lowerSixDirichletIncrement k (growingAnchor k + 1)

/-- Exact cancellation-preserving identity for the lower-six gap.  It is the
complement of the already-proved seven-unit Dirichlet identity, with no
division and no discarded endpoint. -/
theorem growingLowerSixGap_eqv_dirichlet (k : Nat) :
    growingPascalResidual k +
        -((Q'.ofNat 6 * (harmU k * harmU k)) *
          integerThetaSum (harmW k) (growingAnchor k)) ≈
      lowerSixDirichletSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1 +
        -(Q'.ofNat 4 *
          integerThetaTerm (harmW k) (growingAnchor k + 2)) := by
  let u := harmU k
  let I := integerThetaSum (harmW k) (growingAnchor k)
  let E := integerThetaTerm (harmW k) (growingAnchor k + 2)
  let B := integerThetaTerm (harmW k) 1
  let D := finSum (fun j => thetaDirichletCell (harmW k) (j + 1))
    (growingAnchor k + 1)
  have hseven := sevenUnitResidualGap_dirichlet k
  have hsum := lowerSixDirichletSum_eqv k
  have hcomp :
      growingPascalResidual k + -((Q'.ofNat 6 * (u * u)) * I) ≈
        (u * u) * I + -sevenUnitResidualGap k := by
    unfold sevenUnitResidualGap
    exact lower_complement_algebra (growingPascalResidual k) (u * u) I
  refine Q'.eqv_trans _ ((u * u) * I + -sevenUnitResidualGap k) _
    hcomp ?_
  refine Q'.eqv_trans _
    ((u * u) * I +
      -(sevenDirichletProfile k * I + Q'.ofNat 4 * (E + -B) +
        -(Q'.ofNat 4 * D))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left ((u * u) * I) _ _
      (Q'.neg_eqv_congr _ _ (by
        dsimp only [I, E, B, D]
        exact hseven))
  · have hsum' : lowerSixDirichletSum k ≈
        Q'.ofNat 4 * D + -(lowerSixDirichletProfile k * I) := by
      dsimp only [I, D]
      exact hsum
    refine Q'.eqv_trans _
      ((Q'.ofNat 4 * D + -(lowerSixDirichletProfile k * I)) +
        Q'.ofNat 4 * B + -(Q'.ofNat 4 * E)) _ ?_ ?_
    · unfold lowerSixDirichletProfile sevenDirichletProfile
      dsimp only [u]
      exact lower_rearrange_algebra (harmU k) I E B D
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsum'))

/-- A boundary-aware Dirichlet payment closes the actual lower-six envelope.
This is a strict reduction: the hypothesis mentions the explicit finite
Dirichlet sum, not the desired residual itself. -/
theorem growingResidualLowerSix_of_dirichletPayment {k : Nat}
    (hpay :
      Q'.ofNat 4 *
          integerThetaTerm (harmW k) (growingAnchor k + 2) ≤
        lowerSixDirichletSum k +
          Q'.ofNat 4 * integerThetaTerm (harmW k) 1) :
    GrowingResidualLowerSix k := by
  have hgap : (0 : Q') ≤
      lowerSixDirichletSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1 +
        -(Q'.ofNat 4 *
          integerThetaTerm (harmW k) (growingAnchor k + 2)) :=
    Q'.sub_nonneg_of_le hpay
  have hgap' : (0 : Q') ≤
      growingPascalResidual k +
        -((Q'.ofNat 6 * (harmU k * harmU k)) *
          integerThetaSum (harmW k) (growingAnchor k)) :=
    Q'.le_trans' _ _ _ hgap
      (Q'.le_of_eqv (Q'.eqv_symm (growingLowerSixGap_eqv_dirichlet k)))
  unfold GrowingResidualLowerSix
  exact Q'.le_of_sub_nonneg hgap'

/-- The tempting pointwise allocation is false at the first residual scale:
the modal cell `n=3` is strictly adverse. -/
theorem lowerSix_pointwise_fails_k10_n3 :
    ¬ (lowerSixDirichletProfile 10 * integerThetaTerm (harmW 10) 3 ≤
      Q'.ofNat 4 * thetaDirichletCell (harmW 10) 3) := by
  unfold lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm harmW harmU oneSub unit qpow
  decide

/-- The full boundary-aware payment nevertheless succeeds at the same exact
rational scale, so the pointwise fence does not refute the target. -/
theorem lowerSix_dirichletPayment_k10 :
    Q'.ofNat 4 *
        integerThetaTerm (harmW 10) (growingAnchor 10 + 2) ≤
      lowerSixDirichletSum 10 +
        Q'.ofNat 4 * integerThetaTerm (harmW 10) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide

theorem growingResidualLowerSix_k10 : GrowingResidualLowerSix 10 :=
  growingResidualLowerSix_of_dirichletPayment lowerSix_dirichletPayment_k10

/-! Per-scale exact payments, one small kernel check each (proof split). -/

theorem lowerSix_dirichletPayment_at_11 :
    Q'.ofNat 4 * integerThetaTerm (harmW 11) (growingAnchor 11 + 2) ≤
      lowerSixDirichletSum 11 + Q'.ofNat 4 * integerThetaTerm (harmW 11) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_12 :
    Q'.ofNat 4 * integerThetaTerm (harmW 12) (growingAnchor 12 + 2) ≤
      lowerSixDirichletSum 12 + Q'.ofNat 4 * integerThetaTerm (harmW 12) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_13 :
    Q'.ofNat 4 * integerThetaTerm (harmW 13) (growingAnchor 13 + 2) ≤
      lowerSixDirichletSum 13 + Q'.ofNat 4 * integerThetaTerm (harmW 13) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_14 :
    Q'.ofNat 4 * integerThetaTerm (harmW 14) (growingAnchor 14 + 2) ≤
      lowerSixDirichletSum 14 + Q'.ofNat 4 * integerThetaTerm (harmW 14) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_15 :
    Q'.ofNat 4 * integerThetaTerm (harmW 15) (growingAnchor 15 + 2) ≤
      lowerSixDirichletSum 15 + Q'.ofNat 4 * integerThetaTerm (harmW 15) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_16 :
    Q'.ofNat 4 * integerThetaTerm (harmW 16) (growingAnchor 16 + 2) ≤
      lowerSixDirichletSum 16 + Q'.ofNat 4 * integerThetaTerm (harmW 16) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_17 :
    Q'.ofNat 4 * integerThetaTerm (harmW 17) (growingAnchor 17 + 2) ≤
      lowerSixDirichletSum 17 + Q'.ofNat 4 * integerThetaTerm (harmW 17) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_18 :
    Q'.ofNat 4 * integerThetaTerm (harmW 18) (growingAnchor 18 + 2) ≤
      lowerSixDirichletSum 18 + Q'.ofNat 4 * integerThetaTerm (harmW 18) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_19 :
    Q'.ofNat 4 * integerThetaTerm (harmW 19) (growingAnchor 19 + 2) ≤
      lowerSixDirichletSum 19 + Q'.ofNat 4 * integerThetaTerm (harmW 19) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_20 :
    Q'.ofNat 4 * integerThetaTerm (harmW 20) (growingAnchor 20 + 2) ≤
      lowerSixDirichletSum 20 + Q'.ofNat 4 * integerThetaTerm (harmW 20) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_21 :
    Q'.ofNat 4 * integerThetaTerm (harmW 21) (growingAnchor 21 + 2) ≤
      lowerSixDirichletSum 21 + Q'.ofNat 4 * integerThetaTerm (harmW 21) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_22 :
    Q'.ofNat 4 * integerThetaTerm (harmW 22) (growingAnchor 22 + 2) ≤
      lowerSixDirichletSum 22 + Q'.ofNat 4 * integerThetaTerm (harmW 22) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_23 :
    Q'.ofNat 4 * integerThetaTerm (harmW 23) (growingAnchor 23 + 2) ≤
      lowerSixDirichletSum 23 + Q'.ofNat 4 * integerThetaTerm (harmW 23) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_24 :
    Q'.ofNat 4 * integerThetaTerm (harmW 24) (growingAnchor 24 + 2) ≤
      lowerSixDirichletSum 24 + Q'.ofNat 4 * integerThetaTerm (harmW 24) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_25 :
    Q'.ofNat 4 * integerThetaTerm (harmW 25) (growingAnchor 25 + 2) ≤
      lowerSixDirichletSum 25 + Q'.ofNat 4 * integerThetaTerm (harmW 25) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_26 :
    Q'.ofNat 4 * integerThetaTerm (harmW 26) (growingAnchor 26 + 2) ≤
      lowerSixDirichletSum 26 + Q'.ofNat 4 * integerThetaTerm (harmW 26) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_27 :
    Q'.ofNat 4 * integerThetaTerm (harmW 27) (growingAnchor 27 + 2) ≤
      lowerSixDirichletSum 27 + Q'.ofNat 4 * integerThetaTerm (harmW 27) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_28 :
    Q'.ofNat 4 * integerThetaTerm (harmW 28) (growingAnchor 28 + 2) ≤
      lowerSixDirichletSum 28 + Q'.ofNat 4 * integerThetaTerm (harmW 28) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_29 :
    Q'.ofNat 4 * integerThetaTerm (harmW 29) (growingAnchor 29 + 2) ≤
      lowerSixDirichletSum 29 + Q'.ofNat 4 * integerThetaTerm (harmW 29) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_30 :
    Q'.ofNat 4 * integerThetaTerm (harmW 30) (growingAnchor 30 + 2) ≤
      lowerSixDirichletSum 30 + Q'.ofNat 4 * integerThetaTerm (harmW 30) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_31 :
    Q'.ofNat 4 * integerThetaTerm (harmW 31) (growingAnchor 31 + 2) ≤
      lowerSixDirichletSum 31 + Q'.ofNat 4 * integerThetaTerm (harmW 31) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_32 :
    Q'.ofNat 4 * integerThetaTerm (harmW 32) (growingAnchor 32 + 2) ≤
      lowerSixDirichletSum 32 + Q'.ofNat 4 * integerThetaTerm (harmW 32) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_33 :
    Q'.ofNat 4 * integerThetaTerm (harmW 33) (growingAnchor 33 + 2) ≤
      lowerSixDirichletSum 33 + Q'.ofNat 4 * integerThetaTerm (harmW 33) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_34 :
    Q'.ofNat 4 * integerThetaTerm (harmW 34) (growingAnchor 34 + 2) ≤
      lowerSixDirichletSum 34 + Q'.ofNat 4 * integerThetaTerm (harmW 34) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_35 :
    Q'.ofNat 4 * integerThetaTerm (harmW 35) (growingAnchor 35 + 2) ≤
      lowerSixDirichletSum 35 + Q'.ofNat 4 * integerThetaTerm (harmW 35) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_36 :
    Q'.ofNat 4 * integerThetaTerm (harmW 36) (growingAnchor 36 + 2) ≤
      lowerSixDirichletSum 36 + Q'.ofNat 4 * integerThetaTerm (harmW 36) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_37 :
    Q'.ofNat 4 * integerThetaTerm (harmW 37) (growingAnchor 37 + 2) ≤
      lowerSixDirichletSum 37 + Q'.ofNat 4 * integerThetaTerm (harmW 37) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_39 :
    Q'.ofNat 4 * integerThetaTerm (harmW 39) (growingAnchor 39 + 2) ≤
      lowerSixDirichletSum 39 + Q'.ofNat 4 * integerThetaTerm (harmW 39) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_40 :
    Q'.ofNat 4 * integerThetaTerm (harmW 40) (growingAnchor 40 + 2) ≤
      lowerSixDirichletSum 40 + Q'.ofNat 4 * integerThetaTerm (harmW 40) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_41 :
    Q'.ofNat 4 * integerThetaTerm (harmW 41) (growingAnchor 41 + 2) ≤
      lowerSixDirichletSum 41 + Q'.ofNat 4 * integerThetaTerm (harmW 41) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_42 :
    Q'.ofNat 4 * integerThetaTerm (harmW 42) (growingAnchor 42 + 2) ≤
      lowerSixDirichletSum 42 + Q'.ofNat 4 * integerThetaTerm (harmW 42) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_43 :
    Q'.ofNat 4 * integerThetaTerm (harmW 43) (growingAnchor 43 + 2) ≤
      lowerSixDirichletSum 43 + Q'.ofNat 4 * integerThetaTerm (harmW 43) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_44 :
    Q'.ofNat 4 * integerThetaTerm (harmW 44) (growingAnchor 44 + 2) ≤
      lowerSixDirichletSum 44 + Q'.ofNat 4 * integerThetaTerm (harmW 44) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_45 :
    Q'.ofNat 4 * integerThetaTerm (harmW 45) (growingAnchor 45 + 2) ≤
      lowerSixDirichletSum 45 + Q'.ofNat 4 * integerThetaTerm (harmW 45) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_46 :
    Q'.ofNat 4 * integerThetaTerm (harmW 46) (growingAnchor 46 + 2) ≤
      lowerSixDirichletSum 46 + Q'.ofNat 4 * integerThetaTerm (harmW 46) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_47 :
    Q'.ofNat 4 * integerThetaTerm (harmW 47) (growingAnchor 47 + 2) ≤
      lowerSixDirichletSum 47 + Q'.ofNat 4 * integerThetaTerm (harmW 47) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide
theorem lowerSix_dirichletPayment_at_38 :
    Q'.ofNat 4 * integerThetaTerm (harmW 38) (growingAnchor 38 + 2) ≤
      lowerSixDirichletSum 38 + Q'.ofNat 4 * integerThetaTerm (harmW 38) 1 := by
  unfold lowerSixDirichletSum lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm growingAnchor harmW harmU oneSub unit finSum qpow
  decide

/-- Exact derived prefix.  This is not the all-scale argument; it moves the
symbolic Dirichlet/Abel residual to the first scale where the existing
square-root-window infrastructure is available. -/
theorem lowerSix_dirichletPayment_below_thirty_eight {k : Nat}
    (hk0 : 10 ≤ k) (hk1 : k < 38) :
    Q'.ofNat 4 *
        integerThetaTerm (harmW k) (growingAnchor k + 2) ≤
      lowerSixDirichletSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1 := by
  rcases Nat.eq_or_lt_of_le hk0 with rfl | h
  · exact lowerSix_dirichletPayment_k10
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_11
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_12
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_13
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_14
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_15
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_16
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_17
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_18
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_19
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_20
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_21
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_22
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_23
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_24
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_25
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_26
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_27
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_28
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_29
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_30
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_31
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_32
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_33
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_34
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_35
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_36
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_37
  exact absurd (Nat.lt_of_le_of_lt h hk1) (by decide)

theorem growingResidualLowerSix_below_thirty_eight {k : Nat}
    (hk0 : 10 ≤ k) (hk1 : k < 38) : GrowingResidualLowerSix k :=
  growingResidualLowerSix_of_dirichletPayment
    (lowerSix_dirichletPayment_below_thirty_eight hk0 hk1)

/-- Exact transition band before the symbolic square-root bands stabilize. -/
theorem lowerSix_dirichletPayment_firstBand {k : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47) :
    Q'.ofNat 4 *
        integerThetaTerm (harmW k) (growingAnchor k + 2) ≤
      lowerSixDirichletSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1 := by
  rcases Nat.eq_or_lt_of_le hk0 with rfl | h
  · exact lowerSix_dirichletPayment_at_38
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_39
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_40
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_41
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_42
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_43
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_44
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_45
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_46
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact lowerSix_dirichletPayment_at_47
  exact absurd (Nat.le_trans h hk1) (by decide)

theorem growingResidualLowerSix_firstBand {k : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47) : GrowingResidualLowerSix k :=
  growingResidualLowerSix_of_dirichletPayment
    (lowerSix_dirichletPayment_firstBand hk0 hk1)

/-- Complete exact prefix consumed by the all-scale residual.  Only the
generic `k ≥ 48` boundary-aware Abel payment remains. -/
theorem growingResidualLowerSix_below_forty_eight {k : Nat}
    (hk0 : 10 ≤ k) (hk1 : k < 48) : GrowingResidualLowerSix k := by
  by_cases hk38 : k < 38
  · exact growingResidualLowerSix_below_thirty_eight hk0 hk38
  · exact growingResidualLowerSix_firstBand (Nat.le_of_not_lt hk38)
      (Nat.le_of_lt_succ hk1)

#print axioms lowerSixDirichletSum_eqv
#print axioms growingLowerSixGap_eqv_dirichlet
#print axioms growingResidualLowerSix_of_dirichletPayment
#print axioms lowerSix_pointwise_fails_k10_n3
#print axioms lowerSix_dirichletPayment_k10
#print axioms growingResidualLowerSix_k10
#print axioms lowerSix_dirichletPayment_below_thirty_eight
#print axioms growingResidualLowerSix_below_thirty_eight
#print axioms lowerSix_dirichletPayment_firstBand
#print axioms growingResidualLowerSix_firstBand
#print axioms growingResidualLowerSix_below_forty_eight

end YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
