/-
Transport the cleared raw suffix slack to the actual lower-six Dirichlet
cells.  This discharges the far-tail signs unconditionally; it does not
confuse their positivity with the quantitatively stronger prefix payment.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit

namespace YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixFirstCell
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotone
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixEndpoint
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicThetaRepresentation

local infix:50 " ≈ " => Q'.eqv

private theorem suffix_actual_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "suffix_actual_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               suffix_actual_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem ofNat_two_mul_add_one_eqv (n : Nat) :
    Q'.ofNat 2 * Q'.ofNat n + 1 ≈ Q'.ofNat (2 * n + 1) := by
  refine Q'.eqv_trans _
    (Q'.ofNat (2 * n) + Q'.ofNat 1) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 2 n)) (by decide)
  · exact Q'.eqv_symm (Q'.ofNat_add_eqv (2 * n) 1)

private theorem ofNat_succ_eqv (n : Nat) :
    Q'.ofNat n + 1 ≈ Q'.ofNat (n + 1) := by
  refine Q'.eqv_trans _ (Q'.ofNat n + Q'.ofNat 1) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ (by decide)
  · exact Q'.eqv_symm (Q'.ofNat_add_eqv n 1)

private theorem rawDen_eqv_actual (k n : Nat) :
    lowerSixRightRawDen (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      lowerSixRightDen k n := by
  unfold lowerSixRightRawDen lowerSixRightDen
  exact Q'.add_eqv_congr_left _ _ _ (ofNat_two_mul_add_one_eqv n)

private theorem rawNum_eqv_actual (k n : Nat) :
    lowerSixRightRawNum (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      lowerSixRightNum k n := by
  unfold lowerSixRightRawNum lowerSixRightNum
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _ (rawDen_eqv_actual k n))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_right _ _ _ (ofNat_succ_eqv n)))

private theorem qpow_two_eqv_mul (a : Q') :
    RingNormaliser.qpow a 2 ≈ a * a := by
  change ((1 : Q') * a) * a ≈ a * a
  exact Q'.mul_eqv_congr_right _ _ a (Q'.one_mul_eqv a)

private theorem qpow_three_eqv_mul (a : Q') :
    RingNormaliser.qpow a 3 ≈ a * a * a := by
  change (((1 : Q') * a) * a) * a ≈ a * a * a
  exact Q'.mul_eqv_congr_right _ _ a
    (Q'.mul_eqv_congr_right _ _ a (Q'.one_mul_eqv a))

private def suffixNumPolyL : RingNormaliser.PolyExpr :=
  let N := RingNormaliser.PolyExpr.var 0
  let D := RingNormaliser.PolyExpr.var 1
  .add
    (.mul N (.add D (.add (.mul (.const 2) N) (.const 1))))
    (.neg (.mul (.add N (.const 1)) D))

private def suffixNumPolyR : RingNormaliser.PolyExpr :=
  let N := RingNormaliser.PolyExpr.var 0
  let D := RingNormaliser.PolyExpr.var 1
  .add (.mul N (.add (.mul (.const 2) N) (.const 1))) (.neg D)

private theorem suffixNumPoly_normal :
    RingNormaliser.normalize suffixNumPolyL =
      RingNormaliser.normalize suffixNumPolyR := by
  decide

private theorem suffix_num_algebra (N D : Q') :
    N * (D + (Q'.ofNat 2 * N + 1)) + -((N + 1) * D) ≈
      N * (Q'.ofNat 2 * N + 1) + -D := by
  simpa [suffixNumPolyL, suffixNumPolyR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      suffixNumPolyL suffixNumPolyR suffixNumPoly_normal
      (fun | 0 => N | _ => D))

/-- The raw polynomial is exactly the cleared-certificate right side minus
its left side. -/
theorem lowerSixRightRawSlack_eqv_clearedDifference (k n : Nat) :
    lowerSixRightRawSlack (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      (Q'.ofNat 4 *
          (lowerSixRightNum k n * lowerSixRightNum k n)) *
          (Q'.ofNat (k + 2) * Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) +
        -((Q'.ofNat 12 *
              (Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) + 1) *
          Q'.ofNat (n * n) *
          (lowerSixRightDen k n * lowerSixRightDen k n)) := by
  have hA := rawNum_eqv_actual k n
  have hB := rawDen_eqv_actual k n
  have hA2 := Q'.eqv_trans _ _ _
    (qpow_two_eqv_mul
      (lowerSixRightRawNum (Q'.ofNat (k + 2)) (Q'.ofNat n)))
    (mul_eqv_both hA hA)
  have hB2 := Q'.eqv_trans _ _ _
    (qpow_two_eqv_mul
      (lowerSixRightRawDen (Q'.ofNat (k + 2)) (Q'.ofNat n)))
    (mul_eqv_both hB hB)
  have hD2 := qpow_two_eqv_mul (Q'.ofNat (k + 2))
  have hD3 := qpow_three_eqv_mul (Q'.ofNat (k + 2))
  have hN2 := ofNat_square_eqv n
  unfold lowerSixRightRawSlack
  exact Q'.add_eqv_congr'
    (mul_eqv_both
      (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hA2) hD3)
    (Q'.neg_eqv_congr _ _
      (mul_eqv_both
        (mul_eqv_both
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left (Q'.ofNat 12) _ _ hD2)
            (Q'.eqv_refl 1)) hN2) hB2))

private theorem center_square_ge_harmonicDen {k : Nat} (hk : 48 ≤ k) :
    k + 2 ≤ thetaWindowCenter k * thetaWindowCenter k := by
  let c := thetaWindowCenter k
  have hc10 : 10 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hnext : 2 * (k + 2) + 1 < (c + 1) * (c + 1) := by
    rcases Nat.lt_or_ge (2 * (k + 2) + 1) ((c + 1) * (c + 1)) with h | h
    · exact h
    · have hbad : c + 1 ≤ c := by
        dsimp only [c, thetaWindowCenter, thetaWindowLength] at h ⊢
        exact ChebOrthoMidpointEst.isqrt_ge h
      omega
  have htwoc : 2 * c ≤ c * c := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right c (show 2 ≤ c by omega)
  dsimp only [c] at hnext htwoc ⊢
  have hexpand : (thetaWindowCenter k + 1) *
      (thetaWindowCenter k + 1) =
        thetaWindowCenter k * thetaWindowCenter k +
          2 * thetaWindowCenter k + 1 := by
    rw [Nat.add_mul, Nat.mul_add]
    omega
  rw [hexpand] at hnext
  omega

private theorem suffix_num_nonnegative {k j : Nat} (hk : 48 ≤ k) :
    (0 : Q') ≤ lowerSixRightNum k (thetaWindowRight k + 1 + j) := by
  let n := thetaWindowRight k + 1 + j
  let D := k + 2
  have hcn : thetaWindowCenter k ≤ n := by
    dsimp only [n]
    unfold thetaWindowRight
    omega
  have hDsq : D ≤ thetaWindowCenter k * thetaWindowCenter k := by
    dsimp only [D]
    exact center_square_ge_harmonicDen hk
  have hsq : thetaWindowCenter k * thetaWindowCenter k ≤ n * n :=
    Nat.mul_le_mul hcn hcn
  have hn : n ≤ 2 * n + 1 := by omega
  have hprod : n * n ≤ n * (2 * n + 1) :=
    Nat.mul_le_mul_left n hn
  have hnat : D ≤ n * (2 * n + 1) :=
    Nat.le_trans hDsq (Nat.le_trans hsq hprod)
  have hcast := CReal.ofNat_le_ofNat hnat
  have hrearr : lowerSixRightNum k n ≈
      Q'.ofNat (n * (2 * n + 1)) + -Q'.ofNat D := by
    unfold lowerSixRightNum lowerSixRightDen
    dsimp only [D]
    refine Q'.eqv_trans _
      (Q'.ofNat n *
          (Q'.ofNat (k + 2) +
            (Q'.ofNat 2 * Q'.ofNat n + 1)) +
        -((Q'.ofNat n + 1) * Q'.ofNat (k + 2))) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (ofNat_two_mul_add_one_eqv n))))
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm (ofNat_succ_eqv n))))
    · refine Q'.eqv_trans _
        (Q'.ofNat n * (Q'.ofNat 2 * Q'.ofNat n + 1) +
          -Q'.ofNat (k + 2)) _ ?_ ?_
      · exact suffix_num_algebra _ _
      · exact Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_trans _
            (Q'.ofNat n * Q'.ofNat (2 * n + 1)) _
            (Q'.mul_eqv_congr_left _ _ _
              (ofNat_two_mul_add_one_eqv n))
            (Q'.eqv_symm
              (HeatKernelRGStep.ofNat_mul_eqv n (2 * n + 1))))
  have hsub : (0 : Q') ≤
      Q'.ofNat (n * (2 * n + 1)) + -Q'.ofNat D :=
    Q'.sub_nonneg_of_le hcast
  exact Q'.le_trans' _ _ _ hsub (Q'.le_of_eqv (Q'.eqv_symm hrearr))

/-- Every raw suffix certificate is an actual cleared cell certificate. -/
theorem lowerSixSuffixClearedCertificate {k : Nat} (hk : 48 ≤ k)
    (j : Nat) :
    LowerSixRightClearedCertificate k (thetaWindowRight k + 1 + j) := by
  let n := thetaWindowRight k + 1 + j
  have hraw := lowerSixSuffixRawSlack_nonnegative hk j
  have heq := lowerSixRightRawSlack_eqv_clearedDifference k n
  have hdiff : (0 : Q') ≤
      (Q'.ofNat 4 *
          (lowerSixRightNum k n * lowerSixRightNum k n)) *
          (Q'.ofNat (k + 2) * Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) +
        -((Q'.ofNat 12 *
              (Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) + 1) *
          Q'.ofNat (n * n) *
          (lowerSixRightDen k n * lowerSixRightDen k n)) :=
    Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv heq)
  refine ⟨suffix_num_nonnegative hk, ?_⟩
  exact Q'.le_of_sub_nonneg hdiff

/-- The full actual suffix consists of nonnegative Dirichlet cells. -/
theorem lowerSixSuffixIncrement_nonnegative {k : Nat} (hk : 48 ≤ k)
    (j : Nat) :
    (0 : Q') ≤ lowerSixDirichletIncrement k
      (thetaWindowRight k + 1 + j) := by
  exact lowerSixDirichletIncrement_nonnegative_of_rightCertificate
    (lowerSixRightCertificate_of_cleared
      (lowerSixSuffixClearedCertificate hk j))

/-- The far-tail side condition in the reserve/deficit consumer is now
discharged uniformly. -/
theorem lowerSixFarIncrement_nonnegative {k : Nat} (hk : 48 ≤ k)
    (j : Nat) :
    (0 : Q') ≤ lowerSixDirichletIncrement k
      (2 * thetaWindowCenter k + 1 + j) := by
  have hR : thetaWindowRight k ≤ 2 * thetaWindowCenter k := by
    unfold thetaWindowRight
    have h := Nat.div_le_self (thetaWindowCenter k) 4
    omega
  let s := 2 * thetaWindowCenter k - thetaWindowRight k + j
  have hidx : thetaWindowRight k + 1 + s =
      2 * thetaWindowCenter k + 1 + j := by
    dsimp only [s]
    omega
  rw [← hidx]
  exact lowerSixSuffixIncrement_nonnegative hk s

/-- With signs wired through, only the quantitative recovery payment remains
in this consumer. -/
theorem lowerSixInterior_nonnegative_of_recovery_payment_actual
    {k : Nat} (hk : 48 ≤ k)
    (hpay : -lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k) :
    (0 : Q') ≤ lowerSixInteriorSum k +
      Q'.ofNat 4 * integerThetaTerm (harmW k) 1 := by
  exact lowerSixInterior_nonnegative_of_recovery_payment hk hpay
    (fun j _ => lowerSixFarIncrement_nonnegative hk j)

#print axioms lowerSixRightRawSlack_eqv_clearedDifference
#print axioms lowerSixSuffixClearedCertificate
#print axioms lowerSixSuffixIncrement_nonnegative
#print axioms lowerSixFarIncrement_nonnegative
#print axioms lowerSixInterior_nonnegative_of_recovery_payment_actual

end YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
