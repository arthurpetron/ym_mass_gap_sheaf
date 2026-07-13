/-
An upper, reciprocal form of Bernoulli's inequality over the constructive
rational substrate.

For `0 <= u <= 1`, put `w = 1-u`.  The usual lower Bernoulli estimate controls
`w^n` from below.  Gaussian cutoff localization instead needs the complementary
upper estimate

    w^n * (1 + n*u) <= 1,

equivalently `w^n <= 1/(1+n*u)`.  The proof is a direct induction and uses the
exact one-step slack `(n+1)u^2`; no logarithm, exponential, or measured
constant enters.
-/

import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ReciprocalBernoulliUpper

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-- The linear denominator occurring in reciprocal Bernoulli. -/
def bernDen (u : Q') (n : Nat) : Q' :=
  (1 : Q') + Q'.ofNat n * u

/-- Subtraction-free representative of `1-u`. -/
def oneSub (u : Q') : Q' := (1 : Q') + (-u)

private theorem ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

private def bernStepLHS : RingNormaliser.PolyExpr :=
  .add
    (.mul (.add (.const 1) (.neg (.var 0)))
      (.add (.const 1)
        (.mul (.add (.var 1) (.const 1)) (.var 0))))
    (.mul (.add (.var 1) (.const 1))
      (.mul (.var 0) (.var 0)))

private def bernStepRHS : RingNormaliser.PolyExpr :=
  .add (.const 1) (.mul (.var 1) (.var 0))

private theorem bernStep_normal :
    RingNormaliser.normalize bernStepLHS =
      RingNormaliser.normalize bernStepRHS := by decide

private theorem bernStep_identity (u x : Q') :
    ((1 + (-u)) * (1 + (x + 1) * u) + (x + 1) * (u * u)) ≈
      1 + x * u := by
  have h := RingNormaliser.poly_identity_of_normal_eq bernStepLHS bernStepRHS
    bernStep_normal (fun i => if i = 0 then u else x)
  simpa [RingNormaliser.eval, bernStepLHS, bernStepRHS] using h

/-- The exact one-step algebra: multiplying the next linear denominator by
`1-u` loses the nonnegative slack `(n+1)u^2`. -/
theorem oneSub_mul_bernDen_succ_eqv (u : Q') (n : Nat) :
    oneSub u * bernDen u (n + 1) +
        Q'.ofNat (n + 1) * (u * u) ≈ bernDen u n := by
  unfold bernDen
  have hn : Q'.ofNat (n + 1) ≈ Q'.ofNat n + 1 := by
    exact Q'.ofNat_add_eqv n 1
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left ((1 : Q') - u) _ _
        (Q'.add_eqv_congr_left 1 _ _
          (Q'.mul_eqv_congr_right _ _ u hn)))
      (Q'.mul_eqv_congr_right _ _ (u * u) hn)) ?_
  exact bernStep_identity u (Q'.ofNat n)

/-- One reciprocal-Bernoulli step, using only `u^2 >= 0`. -/
theorem oneSub_mul_bernDen_succ_le {u : Q'} (hu0 : (0 : Q') ≤ u)
    (n : Nat) :
    oneSub u * bernDen u (n + 1) ≤ bernDen u n := by
  have hsq : (0 : Q') ≤ Q'.ofNat (n + 1) * (u * u) :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _)
      (Q'.mul_nonneg _ _ hu0 hu0)
  have hadd : oneSub u * bernDen u (n + 1) ≤
      oneSub u * bernDen u (n + 1) +
        Q'.ofNat (n + 1) * (u * u) :=
    Q'.add_le_self_of_nonneg _ _ hsq
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (oneSub_mul_bernDen_succ_eqv u n))

/-- **Reciprocal Bernoulli, cleared form.**  For `0 <= u <= 1`,
`(1-u)^n * (1+n*u) <= 1`. -/
theorem oneSub_pow_mul_bernDen_le {u : Q'} (hu0 : (0 : Q') ≤ u)
    (hu1 : u ≤ (1 : Q')) : ∀ n : Nat,
    qpow (oneSub u) n * bernDen u n ≤ (1 : Q')
  | 0 => by
      change ((1 : Q') * ((1 : Q') + Q'.ofNat 0 * u)) ≤ (1 : Q')
      have hz : Q'.ofNat 0 * u ≈ (0 : Q') :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ u Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv u)
      have ha : (1 : Q') + Q'.ofNat 0 * u ≈ (1 : Q') :=
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ _ hz)
          (Q'.eqv_of_eq (Q'.add_zero' 1))
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 1 _ _ ha)
          (Q'.one_mul_eqv 1))
  | n + 1 => by
      have hw0 : (0 : Q') ≤ oneSub u := by
        unfold oneSub
        exact Q'.sub_nonneg_of_le hu1
      have hstep := oneSub_mul_bernDen_succ_le hu0 n
      have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ hstep
        (qpow_nonneg (oneSub u) hw0 n)
      have hL :
          qpow (oneSub u) (n + 1) * bernDen u (n + 1) ≈
            qpow (oneSub u) n *
              (oneSub u * bernDen u (n + 1)) := by
        change (qpow (oneSub u) n * oneSub u) * bernDen u (n + 1) ≈ _
        refine Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv (qpow (oneSub u) n) (oneSub u) (bernDen u (n + 1))) ?_
        exact Q'.eqv_refl _
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
        (Q'.le_trans' _ _ _ hmul (oneSub_pow_mul_bernDen_le hu0 hu1 n))

/-- The denominator is strictly positive (indeed at least one). -/
theorem bernDen_pos {u : Q'} (hu0 : (0 : Q') ≤ u) (n : Nat) :
    (0 : Q') < bernDen u n := by
  have hnonneg : (0 : Q') ≤ Q'.ofNat n * u :=
    Q'.mul_nonneg _ _ (ofNat_nonneg n) hu0
  exact Q'.pos_add_nonneg (by decide : (0 : Q') < (1 : Q')) hnonneg

/-- Quotient form: `(1-u)^n <= 1/(1+n*u)`. -/
theorem oneSub_pow_le_recip_bernDen {u : Q'} (hu0 : (0 : Q') ≤ u)
    (hu1 : u ≤ (1 : Q')) (n : Nat) :
    qpow (oneSub u) n ≤
      Q'.divPos (1 : Q') (bernDen u n) (bernDen_pos hu0 n) := by
  apply Q'.le_divPos_of_mul_le
  exact oneSub_pow_mul_bernDen_le hu0 hu1 n

end YMGap.Continuum.ReciprocalBernoulliUpper

#print axioms YMGap.Continuum.ReciprocalBernoulliUpper.oneSub_mul_bernDen_succ_eqv
#print axioms YMGap.Continuum.ReciprocalBernoulliUpper.oneSub_mul_bernDen_succ_le
#print axioms YMGap.Continuum.ReciprocalBernoulliUpper.oneSub_pow_mul_bernDen_le
#print axioms YMGap.Continuum.ReciprocalBernoulliUpper.bernDen_pos
#print axioms YMGap.Continuum.ReciprocalBernoulliUpper.oneSub_pow_le_recip_bernDen
