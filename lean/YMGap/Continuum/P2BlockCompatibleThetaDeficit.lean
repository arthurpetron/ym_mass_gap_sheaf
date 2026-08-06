/-
Track 11.7-fusion / R3h -- additive theta-deficit recursion.

# Result

Let `T_k = I_k - w_k H_k` be the positive finite-theta deficit.  Reflective
commutative-ring normalization proves that the physical square comparison is
implied by the additive balance

    2 I_k I_(k+1) T_(k+1)
      <= T_k I_(k+1)^2 + I_k T_(k+1)^2.

Equivalently, after division by positive theta norms, this is
`2 delta_(k+1) <= delta_k + delta_(k+1)^2`.  The present statement remains
division-free.  It is the physical-margin recursion interface needed by the
next analytic step.

# Constructivity

Finite theta sums, their proved AM--GM positivity, and a constant-size
reflected polynomial identity.  No `Classical`, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaCross

namespace YMGap.Continuum.P2BlockCompatibleThetaDeficit

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleModeOneCross
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaCross
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- Positive numerator of the missing mode-one mass at scale `k`. -/
def blockThetaDeficit (k : Nat) : Q' :=
  blockIntegerTheta k +
    -(blockWeight k * blockHalfTheta k)

theorem blockThetaDeficit_nonneg (k : Nat) :
    (0 : Q') <= blockThetaDeficit k := by
  unfold blockThetaDeficit
  exact Q'.sub_nonneg_of_le
    (halfTheta_le_integerTheta (blockWeight_nonneg k) (blockNcut k))

theorem blockIntegerTheta_nonneg (k : Nat) :
    (0 : Q') <= blockIntegerTheta k := by
  have hleft : (0 : Q') <=
      (blockWeight k * blockWeight k) * blockModeOneDen k :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (blockWeight_nonneg k) (blockWeight_nonneg k))
      (Q'.le_of_lt (blockModeOneDen_pos k))
  exact Q'.le_trans' _ _ _ hleft
    (Q'.le_of_eqv (blockModeOneDen_theta_eqv k))

/-- Recover the physical theta signal from its norm and deficit. -/
theorem blockThetaSignal_eqv (k : Nat) :
    blockWeight k * blockHalfTheta k ≈
      blockIntegerTheta k + -blockThetaDeficit k := by
  unfold blockThetaDeficit
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (blockIntegerTheta k) _ _
      (Q'.neg_add_eqv (blockIntegerTheta k)
        (-(blockWeight k * blockHalfTheta k)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv (blockIntegerTheta k)
        (-(blockIntegerTheta k))
        (-(-(blockWeight k * blockHalfTheta k))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_neg_self_eqv (blockIntegerTheta k))
      (Q'.neg_neg_eqv (blockWeight k * blockHalfTheta k))) ?_
  exact QPoly.q_zero_add_eqv _

private def deficitGapL : PolyExpr :=
  .add
    (.mul
      (.mul (.add (.var 1) (.neg (.var 3)))
        (.add (.var 1) (.neg (.var 3))))
      (.var 0))
    (.neg
      (.mul (.add (.var 0) (.neg (.var 2)))
        (.mul (.var 1) (.var 1))))

private def deficitGapR : PolyExpr :=
  .add
    (.add
      (.mul (.var 2) (.mul (.var 1) (.var 1)))
      (.mul (.var 0) (.mul (.var 3) (.var 3))))
    (.neg
      (.mul (.const 2) (.mul (.var 0) (.mul (.var 1) (.var 3)))))

private theorem deficitGap_normal :
    normalize deficitGapL = normalize deficitGapR := by decide

private theorem deficit_gap_eqv (I0 I1 T0 T1 : Q') :
    ((I1 + -T1) * (I1 + -T1)) * I0 +
        -((I0 + -T0) * (I1 * I1)) ≈
      (T0 * (I1 * I1) + I0 * (T1 * T1)) +
        -(Q'.ofNat 2 * (I0 * (I1 * T1))) := by
  simpa [deficitGapL, deficitGapR, RingNormaliser.eval] using
    (poly_identity_of_normal_eq deficitGapL deficitGapR deficitGap_normal
      (fun | 0 => I0 | 1 => I1 | 2 => T0 | _ => T1))

/-- Division-free additive deficit recurrence from the first scale not
covered by exact cells. -/
structure BlockCompatibleP2ThetaDeficitTail : Type where
  balance : forall k, 4 <= k ->
    Q'.ofNat 2 *
        (blockIntegerTheta k *
          (blockIntegerTheta (k + 1) * blockThetaDeficit (k + 1))) <=
      blockThetaDeficit k *
          (blockIntegerTheta (k + 1) * blockIntegerTheta (k + 1)) +
        blockIntegerTheta k *
          (blockThetaDeficit (k + 1) * blockThetaDeficit (k + 1))

/-- Preferred linear residual: the normalized theta deficit contracts by a
factor two.  It is stronger than the quadratic balance by exactly the
nonnegative correction `I_k*T_(k+1)^2`. -/
structure BlockCompatibleP2ThetaDeficitHalfContraction : Type where
  contraction : forall k, 4 <= k ->
    Q'.ofNat 2 *
        (blockIntegerTheta k * blockThetaDeficit (k + 1)) <=
      blockThetaDeficit k * blockIntegerTheta (k + 1)

/-- The linear half-contraction automatically pays the full quadratic
deficit balance. -/
def BlockCompatibleP2ThetaDeficitHalfContraction.toThetaDeficitTail
    (C : BlockCompatibleP2ThetaDeficitHalfContraction) :
    BlockCompatibleP2ThetaDeficitTail where
  balance := fun k hk => by
    let I0 := blockIntegerTheta k
    let I1 := blockIntegerTheta (k + 1)
    let T0 := blockThetaDeficit k
    let T1 := blockThetaDeficit (k + 1)
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ I1
      (C.contraction k hk) (blockIntegerTheta_nonneg (k + 1))
    have hfirst : Q'.ofNat 2 * (I0 * (I1 * T1)) <=
        T0 * (I1 * I1) := by
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv :
          Q'.ofNat 2 * (I0 * (I1 * T1)) ≈
            (Q'.ofNat 2 * (I0 * T1)) * I1))
        (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (by ring_qeqv :
          (T0 * I1) * I1 ≈ T0 * (I1 * I1))))
    have hcorrection : (0 : Q') <= I0 * (T1 * T1) :=
      Q'.mul_nonneg _ _ (blockIntegerTheta_nonneg k)
        (Q'.mul_nonneg _ _
          (blockThetaDeficit_nonneg (k + 1))
          (blockThetaDeficit_nonneg (k + 1)))
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.add_le_self_of_nonneg _ _ hcorrection)

/-- The additive deficit recurrence compiles to the normalized theta cross. -/
def BlockCompatibleP2ThetaDeficitTail.toThetaCrossTail
    (R : BlockCompatibleP2ThetaDeficitTail) :
    BlockCompatibleP2ThetaCrossTail where
  cross := fun k hk => by
    let I0 := blockIntegerTheta k
    let I1 := blockIntegerTheta (k + 1)
    let T0 := blockThetaDeficit k
    let T1 := blockThetaDeficit (k + 1)
    let S0 := blockWeight k * blockHalfTheta k
    let S1 := blockWeight (k + 1) * blockHalfTheta (k + 1)
    let payment := Q'.ofNat 2 * (I0 * (I1 * T1))
    let reserve := T0 * (I1 * I1) + I0 * (T1 * T1)
    have hbalance : payment <= reserve := by
      simpa only [payment, reserve, I0, I1, T0, T1] using R.balance k hk
    have hreserve : (0 : Q') <= reserve + -payment :=
      Q'.sub_nonneg_of_le hbalance
    have hgap :
        ((I1 + -T1) * (I1 + -T1)) * I0 +
            -((I0 + -T0) * (I1 * I1)) ≈
          reserve + -payment := by
      simpa only [reserve, payment] using deficit_gap_eqv I0 I1 T0 T1
    have hgapNonneg :
        (0 : Q') <=
          ((I1 + -T1) * (I1 + -T1)) * I0 +
            -((I0 + -T0) * (I1 * I1)) :=
      Q'.le_trans' _ _ _ hreserve (Q'.ge_of_eqv hgap)
    have hcore :
        (I0 + -T0) * (I1 * I1) <=
          ((I1 + -T1) * (I1 + -T1)) * I0 :=
      Q'.le_of_sub_nonneg hgapNonneg
    have hS0 : S0 ≈ I0 + -T0 := blockThetaSignal_eqv k
    have hS1 : S1 ≈ I1 + -T1 := blockThetaSignal_eqv (k + 1)
    have hleft :
        S0 * (I1 * I1) ≈ (I0 + -T0) * (I1 * I1) :=
      Q'.mul_eqv_congr_right _ _ _ hS0
    have hrightSignal :
        (S1 * S1) * I0 ≈
          ((I1 + -T1) * (I1 + -T1)) * I0 :=
      Q'.mul_eqv_congr_right _ _ I0 (mul_eqv_both hS1 hS1)
    have hrightRearrange :
        (blockWeight (k + 1) * blockWeight (k + 1)) *
            (I0 *
              (blockHalfTheta (k + 1) * blockHalfTheta (k + 1))) ≈
          (S1 * S1) * I0 := by
      dsimp only [S1]
      ring_qeqv
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hcore
        (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm hrightSignal)
            (Q'.eqv_symm hrightRearrange))))

#print axioms blockThetaDeficit_nonneg
#print axioms blockIntegerTheta_nonneg
#print axioms blockThetaSignal_eqv
#print axioms BlockCompatibleP2ThetaDeficitHalfContraction.toThetaDeficitTail
#print axioms BlockCompatibleP2ThetaDeficitTail.toThetaCrossTail

end YMGap.Continuum.P2BlockCompatibleThetaDeficit
