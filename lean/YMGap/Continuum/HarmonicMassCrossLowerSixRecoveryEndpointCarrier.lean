/-
# Endpoint carriers for the lower-six recovery traversal

The alternating center changes advance the scale by many one-step drops and
then enlarge the fixed theta block by exactly two modes.  This module exposes
that structure without a sampled constant: each endpoint sign is the
cumulative within-center payment minus one explicit two-mode expansion debt.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryEndpointCarrier

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicThetaRepresentation

local infix:50 " ≈ " => Q'.eqv

private theorem endpoint_reassoc_cancel
    (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem endpoint_add_right_neg_left_cancel (a b : Q') :
    (a + b) + -a ≈ b := by
  refine Q'.eqv_trans _ ((a + b) + (-a + (0 : Q'))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (a + b) _ _
      (Q'.eqv_symm (YMGap.Constructive.QPoly.q_add_zero_eqv (-a)))
  refine Q'.eqv_trans _ ((a + -a) + (b + (0 : Q'))) _
    (Q'.add_swap_inner a b (-a) 0) ?_
  refine Q'.eqv_trans _ ((0 : Q') + b) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_neg_self_eqv a)
      (YMGap.Constructive.QPoly.q_add_zero_eqv b)
  exact Q'.eqv_of_eq (Q'.zero_add' b)

private theorem endpoint_center_expansion_algebra
    (A B C D E : Q') :
    (((A + B) + C) + D) + -(A + E) ≈
      (B + C) + (D + -E) := by
  have hneg : -(A + E) ≈ -A + -E := Q'.neg_add_eqv A E
  refine Q'.eqv_trans _
    (((A + B) + C) + D + (-A + -E)) _
    (Q'.add_eqv_congr_left (((A + B) + C) + D) _ _ hneg) ?_
  refine Q'.eqv_trans _
    (((A + B) + (C + D)) + (-A + -E)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_assoc_eqv (A + B) C D)
  refine Q'.eqv_trans _
    (((A + B) + -A) + ((C + D) + -E)) _
    (Q'.add_swap_inner (A + B) (C + D) (-A) (-E)) ?_
  refine Q'.eqv_trans _
    (B + ((C + D) + -E)) _
    (Q'.add_eqv_congr_right _ _ _
      (endpoint_add_right_neg_left_cancel A B)) ?_
  refine Q'.eqv_trans _
    (B + (C + (D + -E))) _
    (Q'.add_eqv_congr_left B _ _ (Q'.add_assoc_eqv C D (-E))) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv B C (D + -E))

private theorem endpoint_advance_payment_algebra (A B C : Q') :
    A + -C ≈ (A + -B) + -(C + -B) := by
  have hneg : -(C + -B) ≈ B + -C := by
    refine Q'.eqv_trans _ (-C + -(-B)) _ (Q'.neg_add_eqv C (-B)) ?_
    refine Q'.eqv_trans _ (-C + B) _
      (Q'.add_eqv_congr_left (-C) _ _ (Q'.neg_neg_eqv B)) ?_
    exact Q'.add_comm_eqv (-C) B
  have hrhs : (A + -B) + -(C + -B) ≈ A + -C := by
    refine Q'.eqv_trans _ ((A + -B) + (B + -C)) _
      (Q'.add_eqv_congr_left (A + -B) _ _ hneg) ?_
    exact endpoint_reassoc_cancel A B (-C)
  exact Q'.eqv_symm hrhs

/-- Sum of all one-scale raw drops taken before a center change. -/
def lowerSixFixedCenterDropSum (k c d : Nat) : Q' :=
  finSum (fun r => lowerSixFixedCenterDrop (k + r) c) d

/-- Increasing the center by one adds exactly two sparse modes and moves the
terminal mode by two. -/
def lowerSixCenterExpansionDebt (k c : Nat) : Q' :=
  lowerSixFixedCenterSparseSlack k (c + 1) +
    -lowerSixFixedCenterSparseSlack k c

/-- Raw scale advance followed by one center enlargement. -/
def lowerSixCenterAdvanceDrop (k c d : Nat) : Q' :=
  lowerSixFixedCenterSparseSlack k c +
    -lowerSixFixedCenterSparseSlack (k + d) (c + 1)

/-- The one-scale drops telescope exactly over an arbitrary natural advance. -/
theorem lowerSixFixedCenterDropSum_eqv (k c : Nat) : ∀ d,
    lowerSixFixedCenterDropSum k c d ≈
      lowerSixFixedCenterSparseSlack k c +
        -lowerSixFixedCenterSparseSlack (k + d) c
  | 0 => by
      unfold lowerSixFixedCenterDropSum finSum
      simp only [Nat.add_zero]
      exact Q'.eqv_symm
        (Q'.add_neg_self_eqv (lowerSixFixedCenterSparseSlack k c))
  | d + 1 => by
      have ih := lowerSixFixedCenterDropSum_eqv k c d
      unfold lowerSixFixedCenterDropSum at ih ⊢
      simp only [finSum_succ]
      rw [show k + (d + 1) = (k + d) + 1 by omega]
      refine Q'.eqv_trans _
        ((lowerSixFixedCenterSparseSlack k c +
            -lowerSixFixedCenterSparseSlack (k + d) c) +
          lowerSixFixedCenterDrop (k + d) c) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ ih
      · unfold lowerSixFixedCenterDrop
        exact endpoint_reassoc_cancel _ _ _

/-- Exact two-new-mode formula for the center-expansion debt. -/
theorem lowerSixCenterExpansionDebt_eqv_modes (k c : Nat) :
    lowerSixCenterExpansionDebt k c ≈
      (lowerSixRecoverySparseMode k (2 * c + 1) +
        lowerSixRecoverySparseMode k (2 * c + 2)) +
      (Q'.ofNat 4 * integerThetaTerm (harmW k) (2 * c + 3) +
        -(Q'.ofNat 4 * integerThetaTerm (harmW k) (2 * c + 1))) := by
  have hold := lowerSixFixedCenterSparseSlack_eqv_modeSum k c
  have hnew := lowerSixFixedCenterSparseSlack_eqv_modeSum k (c + 1)
  rw [show 2 * (c + 1) = (2 * c + 1) + 1 by omega,
    finSum_succ, show 2 * c + 1 = 2 * c + 1 by rfl,
    finSum_succ] at hnew
  unfold lowerSixCenterExpansionDebt
  refine Q'.eqv_trans _
    (((finSum (fun j => lowerSixRecoverySparseMode k (j + 1)) (2 * c) +
          lowerSixRecoverySparseMode k (2 * c + 1)) +
        lowerSixRecoverySparseMode k (2 * c + 2) +
        Q'.ofNat 4 * integerThetaTerm (harmW k) (2 * c + 3)) +
      -(finSum (fun j => lowerSixRecoverySparseMode k (j + 1)) (2 * c) +
        Q'.ofNat 4 * integerThetaTerm (harmW k) (2 * c + 1))) _ ?_ ?_
  · exact Q'.add_eqv_congr' hnew (Q'.neg_eqv_congr _ _ hold)
  · exact endpoint_center_expansion_algebra _ _ _ _ _

/-- The two new endpoint modes inherit the same positive-weight,
one-crossing slope coordinate as the within-cell analysis. -/
theorem lowerSixCenterExpansionDebt_eqv_weightSlopes (k c : Nat) :
    lowerSixCenterExpansionDebt k c ≈
      (lowerSixRecoveryDropWeight k (2 * c + 1) *
          lowerSixRecoveryModeSlope k (2 * c + 1) +
        lowerSixRecoveryDropWeight k (2 * c + 2) *
          lowerSixRecoveryModeSlope k (2 * c + 2)) +
      (Q'.ofNat 4 * integerThetaTerm (harmW k) (2 * c + 3) +
        -(Q'.ofNat 4 * integerThetaTerm (harmW k) (2 * c + 1))) := by
  have hfirst := lowerSixRecoverySparseMode_eqv_weightSlope
    k (2 * c + 1) (by omega)
  have hsecond := lowerSixRecoverySparseMode_eqv_weightSlope
    k (2 * c + 2) (by omega)
  exact Q'.eqv_trans _ _ _
    (lowerSixCenterExpansionDebt_eqv_modes k c)
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr' hfirst hsecond))

/-- An endpoint advance is exactly the accumulated within-center reserve
minus the two-mode expansion debt at the new scale. -/
theorem lowerSixCenterAdvanceDrop_eqv_payment (k c d : Nat) :
    lowerSixCenterAdvanceDrop k c d ≈
      lowerSixFixedCenterDropSum k c d +
        -lowerSixCenterExpansionDebt (k + d) c := by
  have hsum := lowerSixFixedCenterDropSum_eqv k c d
  unfold lowerSixCenterAdvanceDrop lowerSixCenterExpansionDebt
  refine Q'.eqv_trans _
    ((lowerSixFixedCenterSparseSlack k c +
        -lowerSixFixedCenterSparseSlack (k + d) c) +
      -(lowerSixFixedCenterSparseSlack (k + d) (c + 1) +
        -lowerSixFixedCenterSparseSlack (k + d) c)) _ ?_ ?_
  · exact endpoint_advance_payment_algebra _ _ _
  · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsum)

/-- A cumulative within-center payment for the expansion debt proves the
corresponding endpoint drop sign. -/
theorem lowerSixCenterAdvanceDrop_nonnegative_of_payment
    {k c d : Nat}
    (hpay : lowerSixCenterExpansionDebt (k + d) c ≤
      lowerSixFixedCenterDropSum k c d) :
    (0 : Q') ≤ lowerSixCenterAdvanceDrop k c d := by
  have hnonnegative := Q'.sub_nonneg_of_le hpay
  exact Q'.le_trans' _ _ _ hnonnegative
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixCenterAdvanceDrop_eqv_payment k c d)))

/-- Even-to-odd endpoint: `2m+2` within-center steps pay one two-mode
expansion. -/
theorem lowerSixEvenOddEndpointDrop_eqv_payment (m : Nat) (hm : 1 ≤ m) :
    lowerSixEvenOddEndpointDrop m ≈
      lowerSixFixedCenterDropSum
          (lowerSixEvenCenterRightScale m) (2 * m) (2 * m + 2) +
        -lowerSixCenterExpansionDebt
          (lowerSixOddCenterRightScale m) (2 * m) := by
  have hscale : lowerSixEvenCenterRightScale m + (2 * m + 2) =
      lowerSixOddCenterRightScale m := by
    have hright : 2 * m * (m + 1) + 2 * m =
        2 * m * m + 4 * m := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    have hmm : 1 ≤ m * m := Nat.mul_le_mul hm hm
    have htwosq : 2 ≤ 2 * m * m := by
      simpa only [Nat.mul_one, Nat.mul_assoc] using
        Nat.mul_le_mul_left 2 hmm
    have hleftPos : 3 ≤ 2 * m * m + 2 * m := by omega
    have hrightPos : 1 ≤ 2 * m * m + 4 * m := by omega
    have hleftCancel :
        2 * m * m + 2 * m - 3 + 3 = 2 * m * m + 2 * m :=
      Nat.sub_add_cancel hleftPos
    have hrightCancel :
        2 * m * m + 4 * m - 1 + 1 = 2 * m * m + 4 * m :=
      Nat.sub_add_cancel hrightPos
    unfold lowerSixEvenCenterRightScale lowerSixOddCenterRightScale
    rw [hright]
    omega
  have h := lowerSixCenterAdvanceDrop_eqv_payment
    (lowerSixEvenCenterRightScale m) (2 * m) (2 * m + 2)
  unfold lowerSixCenterAdvanceDrop at h
  rw [hscale, show 2 * m + 1 = 2 * m + 1 by rfl] at h
  exact h

/-- Odd-to-next-even endpoint has the same `2m+2` payment length. -/
theorem lowerSixOddEvenEndpointDrop_eqv_payment (m : Nat) (hm : 1 ≤ m) :
    lowerSixOddEvenEndpointDrop m ≈
      lowerSixFixedCenterDropSum
          (lowerSixOddCenterRightScale m) (2 * m + 1) (2 * m + 2) +
        -lowerSixCenterExpansionDebt
          (lowerSixEvenCenterRightScale (m + 1)) (2 * m + 1) := by
  have hscale : lowerSixOddCenterRightScale m + (2 * m + 2) =
      lowerSixEvenCenterRightScale (m + 1) := by
    have hleft : 2 * m * (m + 1) + 2 * m =
        2 * m * m + 4 * m := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    have hright : 2 * (m + 1) * (m + 1) + 2 * (m + 1) =
        2 * m * m + 6 * m + 4 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
      omega
    unfold lowerSixEvenCenterRightScale lowerSixOddCenterRightScale
    rw [hleft, hright]
    omega
  have h := lowerSixCenterAdvanceDrop_eqv_payment
    (lowerSixOddCenterRightScale m) (2 * m + 1) (2 * m + 2)
  unfold lowerSixCenterAdvanceDrop at h
  rw [hscale, show 2 * m + 1 + 1 = 2 * (m + 1) by omega] at h
  exact h

theorem lowerSixEvenOddEndpointDrop_nonnegative_of_payment
    (m : Nat) (hm : 1 ≤ m)
    (hpay : lowerSixCenterExpansionDebt
        (lowerSixOddCenterRightScale m) (2 * m) ≤
      lowerSixFixedCenterDropSum
        (lowerSixEvenCenterRightScale m) (2 * m) (2 * m + 2)) :
    (0 : Q') ≤ lowerSixEvenOddEndpointDrop m := by
  have hnonnegative := Q'.sub_nonneg_of_le hpay
  exact Q'.le_trans' _ _ _ hnonnegative
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixEvenOddEndpointDrop_eqv_payment m hm)))

theorem lowerSixOddEvenEndpointDrop_nonnegative_of_payment
    (m : Nat) (hm : 1 ≤ m)
    (hpay : lowerSixCenterExpansionDebt
        (lowerSixEvenCenterRightScale (m + 1)) (2 * m + 1) ≤
      lowerSixFixedCenterDropSum
        (lowerSixOddCenterRightScale m) (2 * m + 1) (2 * m + 2)) :
    (0 : Q') ≤ lowerSixOddEvenEndpointDrop m := by
  have hnonnegative := Q'.sub_nonneg_of_le hpay
  exact Q'.le_trans' _ _ _ hnonnegative
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixOddEvenEndpointDrop_eqv_payment m hm)))

#print axioms lowerSixFixedCenterDropSum_eqv
#print axioms lowerSixCenterExpansionDebt_eqv_modes
#print axioms lowerSixCenterExpansionDebt_eqv_weightSlopes
#print axioms lowerSixCenterAdvanceDrop_eqv_payment
#print axioms lowerSixCenterAdvanceDrop_nonnegative_of_payment
#print axioms lowerSixEvenOddEndpointDrop_eqv_payment
#print axioms lowerSixOddEvenEndpointDrop_eqv_payment
#print axioms lowerSixEvenOddEndpointDrop_nonnegative_of_payment
#print axioms lowerSixOddEvenEndpointDrop_nonnegative_of_payment

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryEndpointCarrier
