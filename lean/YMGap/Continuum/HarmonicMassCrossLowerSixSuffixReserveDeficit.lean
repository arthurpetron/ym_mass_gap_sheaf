/-
Exact reserve-versus-deficit coordinates for the lower-six suffix.

The adverse prefix is identified with its exact weighted-carrier sum.  The
right reserve is then split at mode twice the integer square-root center.  The
near recovery block is the minimal reserve that must pay the prefix; the far
tail is kept as a separate nonnegative remainder.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixSuffixFirstCell

namespace YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.HarmonicThetaRepresentation

local infix:50 " ≈ " => Q'.eqv

private theorem reserve_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "reserve_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               reserve_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Number of suffix cells from the right window edge through mode `2c`. -/
def lowerSixRecoveryCount (k : Nat) : Nat :=
  2 * thetaWindowCenter k - thetaWindowRight k

/-- The near suffix block responsible for paying the adverse prefix. -/
def lowerSixRecoveryReserve (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixDirichletIncrement k (thetaWindowRight k + 1 + j))
    (lowerSixRecoveryCount k)

/-- Remaining suffix strictly beyond mode `2c`. -/
def lowerSixFarReserve (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixDirichletIncrement k
      (2 * thetaWindowCenter k + 1 + j))
    (growingAnchor k - 2 * thetaWindowCenter k)

private theorem thetaWindowRight_le_twice_center (k : Nat) :
    thetaWindowRight k ≤ 2 * thetaWindowCenter k := by
  unfold thetaWindowRight
  have h := Nat.div_le_self (thetaWindowCenter k) 4
  omega

private theorem twice_center_le_anchor {k : Nat} (hk : 48 ≤ k) :
    2 * thetaWindowCenter k ≤ growingAnchor k := by
  have hc := thetaWindowCenter_le_harmonicDen (show 38 ≤ k by omega)
  unfold growingAnchor
  omega

private theorem lowerSixAugmented_finSum_exact (k : Nat) : ∀ N,
    finSum (lowerSixAugmentedIncrement k) (N + 1) ≈
      finSum (fun j => lowerSixDirichletIncrement k (j + 1)) (N + 1) +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1
  | 0 => by
      simp only [finSum_succ, finSum_zero, lowerSixAugmentedIncrement,
        Q'.zero_add']
      exact Q'.eqv_refl _
  | N + 1 => by
      change
        (finSum (lowerSixAugmentedIncrement k) (N + 1) +
            lowerSixDirichletIncrement k (N + 2)) ≈
          ((finSum (fun j => lowerSixDirichletIncrement k (j + 1))
              (N + 1) + lowerSixDirichletIncrement k (N + 2)) +
            Q'.ofNat 4 * integerThetaTerm (harmW k) 1)
      refine Q'.eqv_trans _
        ((finSum (fun j => lowerSixDirichletIncrement k (j + 1))
              (N + 1) +
            Q'.ofNat 4 * integerThetaTerm (harmW k) 1) +
          lowerSixDirichletIncrement k (N + 2)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (lowerSixAugmented_finSum_exact k N)
      · reserve_ring

/-- Exact expression for the entire adverse prefix as a weighted carrier
sum.  No absolute-value or pointwise relaxation is introduced. -/
theorem lowerSixWindowPrefix_eqv_weightedCarrier {k : Nat} (hk : 48 ≤ k) :
    lowerSixWindowPrefix k ≈
      finSum
        (fun j => lowerSixAbelCarrier k j * lowerSixAbelWeight k j)
        (thetaWindowRight k) := by
  have hRpos : 0 < thetaWindowRight k := by
    have hc := thetaWindowCenter_ge_nine (show 38 ≤ k by omega)
    unfold thetaWindowRight
    omega
  have hterm := finSum_eqv_congr
    (fun j => lowerSixAbelCarrier k j * lowerSixAbelWeight k j)
    (lowerSixAugmentedIncrement k)
    (lowerSixAbel_term_eqv k) (thetaWindowRight k)
  have hR : thetaWindowRight k = thetaWindowRight k - 1 + 1 := by omega
  have haug := lowerSixAugmented_finSum_exact k (thetaWindowRight k - 1)
  rw [← hR] at haug
  unfold lowerSixWindowPrefix
  exact Q'.eqv_trans _
    (finSum (fun j => lowerSixDirichletIncrement k (j + 1))
        (thetaWindowRight k) +
      Q'.ofNat 4 * integerThetaTerm (harmW k) 1) _
    (Q'.add_comm_eqv _ _)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm haug) (Q'.eqv_symm hterm))

/-- Exact split of the full right reserve into the recovery block through
`2c` and the far nonnegative tail. -/
theorem lowerSixWindowRightReserve_eqv_recovery_add_far
    {k : Nat} (hk : 48 ≤ k) :
    lowerSixWindowRightReserve k ≈
      lowerSixRecoveryReserve k + lowerSixFarReserve k := by
  let R := thetaWindowRight k
  let C := 2 * thetaWindowCenter k
  let f := fun j => lowerSixDirichletIncrement k (R + 1 + j)
  have hRC : R ≤ C := thetaWindowRight_le_twice_center k
  have hCA : C ≤ growingAnchor k := twice_center_le_anchor hk
  have hcount : growingAnchor k - R =
      (C - R) + (growingAnchor k - C) := by omega
  have hsplit := finSum_split f (C - R) (growingAnchor k - C)
  rw [← hcount] at hsplit
  unfold lowerSixWindowRightReserve lowerSixRecoveryReserve
    lowerSixRecoveryCount lowerSixFarReserve
  dsimp only [R, C, f] at hsplit ⊢
  refine Q'.eqv_trans _
    (finSum (fun j => lowerSixDirichletIncrement k
        (thetaWindowRight k + 1 + j))
      (2 * thetaWindowCenter k - thetaWindowRight k) +
      finSum (fun j => lowerSixDirichletIncrement k
        (thetaWindowRight k + 1 +
          (2 * thetaWindowCenter k - thetaWindowRight k + j)))
        (growingAnchor k - 2 * thetaWindowCenter k)) _ hsplit ?_
  exact Q'.add_eqv_congr_left _ _ _
    (finSum_eqv_congr _ _ (fun j => by
      have hidx : thetaWindowRight k + 1 +
          (2 * thetaWindowCenter k - thetaWindowRight k + j) =
        2 * thetaWindowCenter k + 1 + j := by omega
      rw [hidx]
      exact Q'.eqv_refl _) _)

private theorem finSum_nonnegative_of_terms (f : Nat → Q') : ∀ N,
    (∀ j, j < N → (0 : Q') ≤ f j) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (finSum_nonnegative_of_terms f N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

/-- The recovery block is a lower bound for the full reserve once the far
tail signs are supplied.  This is deliberately separate from deficit payment. -/
theorem lowerSixRecoveryReserve_le_rightReserve_of_far_nonnegative
    {k : Nat} (hk : 48 ≤ k)
    (hfar : ∀ j, j < growingAnchor k - 2 * thetaWindowCenter k →
      (0 : Q') ≤ lowerSixDirichletIncrement k
        (2 * thetaWindowCenter k + 1 + j)) :
    lowerSixRecoveryReserve k ≤ lowerSixWindowRightReserve k := by
  have hfarSum : (0 : Q') ≤ lowerSixFarReserve k := by
    unfold lowerSixFarReserve
    exact finSum_nonnegative_of_terms _ _ hfar
  have hadd := Q'.add_le_self_of_nonneg
    (lowerSixRecoveryReserve k) (lowerSixFarReserve k) hfarSum
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (lowerSixWindowRightReserve_eqv_recovery_add_far hk)))

/-- Recovery payment plus far-tail positivity is exactly sufficient for the
full two-sided payment. -/
theorem lowerSixInterior_nonnegative_of_recovery_payment
    {k : Nat} (hk : 48 ≤ k)
    (hpay : -lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k)
    (hfar : ∀ j, j < growingAnchor k - 2 * thetaWindowCenter k →
      (0 : Q') ≤ lowerSixDirichletIncrement k
        (2 * thetaWindowCenter k + 1 + j)) :
    (0 : Q') ≤ lowerSixInteriorSum k +
      Q'.ofNat 4 * integerThetaTerm (harmW k) 1 := by
  exact lowerSixInterior_nonnegative_of_window_payment hk
    (Q'.le_trans' _ _ _ hpay
      (lowerSixRecoveryReserve_le_rightReserve_of_far_nonnegative hk hfar))

#print axioms lowerSixWindowPrefix_eqv_weightedCarrier
#print axioms lowerSixWindowRightReserve_eqv_recovery_add_far
#print axioms lowerSixRecoveryReserve_le_rightReserve_of_far_nonnegative
#print axioms lowerSixInterior_nonnegative_of_recovery_payment

end YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
