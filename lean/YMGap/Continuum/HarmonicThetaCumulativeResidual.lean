/-
# Finite cumulative scaled theta residual

The cutoff-one and cutoff-two Bernstein certificates have the common exact
form

  8 * (w * half head) + residual
    = (1+w)^3 * integer head.

This module packages that identity at an arbitrary finite cutoff.  It also
records the terminal-node adjustment required by the mismatched growing
anchor: the growing head retains one more half-integer edge but not the next
integer node.
-/

import YMGap.Continuum.HarmonicThetaTermwiseFence
import YMGap.Continuum.HarmonicVariableAnchorThetaBridge

namespace YMGap.Continuum.HarmonicThetaCumulativeResidual

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicThetaTermwiseFence
open YMGap.Continuum.HarmonicVariableAnchorThetaBridge
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem add_add_neg_cancel (a b : Q') :
    a + (b + -a) ≈ b := by
  have haa : a + -a ≈ 0 := Q'.add_neg_self_eqv a
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv a b (-a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (a + b) (b + a) (-a)
      (Q'.add_comm_eqv a b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b a (-a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left b (a + -a) 0 haa) ?_
  exact QPoly.q_add_zero_eqv b

private theorem neg_add_add_cancel (a b : Q') :
    -a + (a + b) ≈ b := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-a) a b)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (-a + a) 0 b
      (Q'.neg_add_self_eqv a)) ?_
  exact QPoly.q_zero_add_eqv b

private theorem add_left_cancel_eqv (a b c : Q')
    (h : a + b ≈ a + c) : b ≈ c := by
  have hneg : -a + (a + b) ≈ -a + (a + c) :=
    Q'.add_eqv_congr_left (-a) _ _ h
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (neg_add_add_cancel a b))
    (Q'.eqv_trans _ _ _ hneg (neg_add_add_cancel a c))

private def terminalPaymentL : RingNormaliser.PolyExpr :=
  .add (.mul (.var 0) (.var 1)) (.neg (.var 3))

private def terminalPaymentR : RingNormaliser.PolyExpr :=
  .add
    (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
      (.neg (.var 3)))
    (.neg (.mul (.var 0) (.var 2)))

private theorem terminalPayment_normal :
    RingNormaliser.normalize terminalPaymentL =
      RingNormaliser.normalize terminalPaymentR := by
  decide

private theorem terminal_payment_rearrange (F I T A : Q') :
    F * I + -A ≈ (F * (I + T) + -A) + -(F * T) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    terminalPaymentL terminalPaymentR terminalPayment_normal
    (fun
      | 0 => F
      | 1 => I
      | 2 => T
      | _ => A)
  simpa [terminalPaymentL, terminalPaymentR, RingNormaliser.eval] using h

/-- The cleared residual at a common finite cutoff.  The integer sector has
`N+1` nodes and the half-integer sector has `N` edges, exactly as in
`integerThetaSum w N` and `halfThetaSum w N`. -/
def cumulativeScaledThetaResidual (w : Q') (N : Nat) : Q' :=
  qpow ((1 : Q') + w) 3 * integerThetaSum w N +
    -(Q'.ofNat 8 * (w * halfThetaSum w N))

/-- Exact arbitrary-cutoff identity underlying the cutoff-one and cutoff-two
Bernstein certificates. -/
theorem cumulative_scaled_theta_identity (w : Q') (N : Nat) :
    Q'.ofNat 8 * (w * halfThetaSum w N) +
        cumulativeScaledThetaResidual w N ≈
      qpow ((1 : Q') + w) 3 * integerThetaSum w N := by
  unfold cumulativeScaledThetaResidual
  exact add_add_neg_cancel _ _

/-- At cutoff one the generic carrier is exactly the already-certified
Bernstein pilot residual. -/
theorem cumulative_scaled_residual_one_eqv (w : Q') :
    cumulativeScaledThetaResidual w 1 ≈
      qpow w 2 * QPoly.eval
        ThetaResidualBernsteinPilot.thetaResidualOneP w := by
  apply add_left_cancel_eqv
    (Q'.ofNat 8 * (w * halfThetaTerm w 1))
  have hgeneral := cumulative_scaled_theta_identity w 1
  have hgeneral' :
      Q'.ofNat 8 * (w * halfThetaTerm w 1) +
          cumulativeScaledThetaResidual w 1 ≈
        qpow ((1 : Q') + w) 3 *
          (integerThetaTerm w 1 + integerThetaTerm w 2) := by
    simpa [halfThetaSum, integerThetaSum, finSum, Q'.zero_add'] using hgeneral
  exact Q'.eqv_trans _ _ _ hgeneral'
    (Q'.eqv_symm (first_transport_scaled_identity w))

/-- At cutoff two the generic carrier is exactly the second positive
Bernstein pilot residual. -/
theorem cumulative_scaled_residual_two_eqv (w : Q') :
    cumulativeScaledThetaResidual w 2 ≈
      qpow w 2 * QPoly.eval
        ThetaResidualBernsteinPilot.thetaResidualTwoP w := by
  apply add_left_cancel_eqv
    (Q'.ofNat 8 *
      (w * (halfThetaTerm w 1 + halfThetaTerm w 2)))
  have hgeneral := cumulative_scaled_theta_identity w 2
  have hgeneral' :
      Q'.ofNat 8 *
            (w * (halfThetaTerm w 1 + halfThetaTerm w 2)) +
          cumulativeScaledThetaResidual w 2 ≈
        qpow ((1 : Q') + w) 3 *
          ((integerThetaTerm w 1 + integerThetaTerm w 2) +
            integerThetaTerm w 3) := by
    simpa [halfThetaSum, integerThetaSum, finSum, Q'.zero_add'] using hgeneral
  exact Q'.eqv_trans _ _ _ hgeneral'
    (Q'.eqv_symm (second_transport_scaled_identity w))

/-- Nonnegativity of the finite cumulative residual is precisely sufficient
for the retuned theta comparison at that cutoff. -/
theorem theta_comparison_of_cumulative_residual_nonnegative
    {w : Q'} (N : Nat)
    (hres : (0 : Q') ≤ cumulativeScaledThetaResidual w N) :
    w * halfThetaSum w N ≤
      retuneCube w * integerThetaSum w N := by
  exact scaled_theta_remainder_pays hres
    (cumulative_scaled_theta_identity w N)

/-- The growing head keeps `b+1` half-integer edges but only the first `b+1`
integer nodes.  This is the corresponding cleared residual. -/
def growingHeadScaledThetaResidual (w : Q') (b : Nat) : Q' :=
  qpow ((1 : Q') + w) 3 * integerThetaSum w b +
    -(Q'.ofNat 8 * (w * halfThetaSum w (b + 1)))

/-- Exact scaled identity at the mismatched growing head. -/
theorem growing_head_scaled_theta_identity (w : Q') (b : Nat) :
    Q'.ofNat 8 * (w * halfThetaSum w (b + 1)) +
        growingHeadScaledThetaResidual w b ≈
      qpow ((1 : Q') + w) 3 * integerThetaSum w b := by
  unfold growingHeadScaledThetaResidual
  exact add_add_neg_cancel _ _

/-- The growing-head residual is the common-cutoff residual after removing
the budget of the terminal integer node.  This identifies the exact extra
payment that a Pascal/Bernstein proof must make. -/
theorem growing_head_residual_eq_cumulative_minus_terminal
    (w : Q') (b : Nat) :
    growingHeadScaledThetaResidual w b ≈
      cumulativeScaledThetaResidual w (b + 1) +
        -(qpow ((1 : Q') + w) 3 * integerThetaTerm w (b + 2)) := by
  unfold growingHeadScaledThetaResidual cumulativeScaledThetaResidual
  have hsum : integerThetaSum w (b + 1) =
      integerThetaSum w b + integerThetaTerm w (b + 2) := by
    rfl
  rw [hsum]
  exact terminal_payment_rearrange _ _ _ _

/-- **First uniform residual inequality.**  To pass from the common finite
cutoff to the actual growing head, it suffices to show that its cumulative
reserve pays the one terminal integer node that is absent from the retained
head.  The statement is uniform in both `w` and the cutoff `b`. -/
theorem growing_head_residual_nonnegative_of_terminal_payment
    {w : Q'} (b : Nat)
    (hpay :
      qpow ((1 : Q') + w) 3 * integerThetaTerm w (b + 2) ≤
        cumulativeScaledThetaResidual w (b + 1)) :
    (0 : Q') ≤ growingHeadScaledThetaResidual w b := by
  have hdiff : (0 : Q') ≤
      cumulativeScaledThetaResidual w (b + 1) +
        -(qpow ((1 : Q') + w) 3 * integerThetaTerm w (b + 2)) :=
    Q'.sub_nonneg_of_le hpay
  exact Q'.le_trans' _ _ _ hdiff
    (Q'.ge_of_eqv
      (growing_head_residual_eq_cumulative_minus_terminal w b))

/-- A nonnegative growing-head residual discharges the exact theta premise
used by the variable-anchor propagation theorem. -/
theorem growing_head_theta_premise_of_residual_nonnegative
    {w : Q'} (b : Nat)
    (hres : (0 : Q') ≤ growingHeadScaledThetaResidual w b) :
    w * halfThetaSum w (b + 1) ≤
      retuneCube w * integerThetaSum w b := by
  exact scaled_theta_remainder_pays hres
    (growing_head_scaled_theta_identity w b)

/-- The concrete terminal-payment inequality therefore implies the exact
growing-head theta comparison. -/
theorem growing_head_theta_premise_of_terminal_payment
    {w : Q'} (b : Nat)
    (hpay :
      qpow ((1 : Q') + w) 3 * integerThetaTerm w (b + 2) ≤
        cumulativeScaledThetaResidual w (b + 1)) :
    w * halfThetaSum w (b + 1) ≤
      retuneCube w * integerThetaSum w b := by
  exact growing_head_theta_premise_of_residual_nonnegative b
    (growing_head_residual_nonnegative_of_terminal_payment b hpay)

/-- Harmonic specialization: residual nonnegativity at the explicit growing
anchor is exactly the outstanding theta-head premise. -/
theorem harmonic_growing_anchor_theta_premise_of_residual_nonnegative
    (k : Nat)
    (hres : (0 : Q') ≤
      growingHeadScaledThetaResidual (harmW k) (growingAnchor k)) :
    harmW k * halfThetaSum (harmW k) (growingAnchor k + 1) ≤
      retuneCube (harmW k) *
        integerThetaSum (harmW k) (growingAnchor k) :=
  growing_head_theta_premise_of_residual_nonnegative
    (growingAnchor k) hres

/-- Harmonic growing-anchor form of the terminal-payment target. -/
theorem harmonic_growing_anchor_theta_premise_of_terminal_payment
    (k : Nat)
    (hpay :
      qpow ((1 : Q') + harmW k) 3 *
          integerThetaTerm (harmW k) (growingAnchor k + 2) ≤
        cumulativeScaledThetaResidual (harmW k) (growingAnchor k + 1)) :
    harmW k * halfThetaSum (harmW k) (growingAnchor k + 1) ≤
      retuneCube (harmW k) *
        integerThetaSum (harmW k) (growingAnchor k) :=
  growing_head_theta_premise_of_terminal_payment
    (growingAnchor k) hpay

/-- Consequently the same residual certificate closes every later retained
cutoff through the public growing-anchor bridge. -/
theorem growing_anchor_retune_of_residual_nonnegative
    (k M : Nat)
    (hres : (0 : Q') ≤
      growingHeadScaledThetaResidual (harmW k) (growingAnchor k)) :
    adjCorr (harmW k) (growingAnchor k + 1 + M) ≤
      retuneCube (harmW k) *
        coordNormSq (harmW k) (growingAnchor k + 1 + M) := by
  exact growing_anchor_retune_of_theta_head k M
    (harmonic_growing_anchor_theta_premise_of_residual_nonnegative k hres)

#print axioms cumulative_scaled_theta_identity
#print axioms cumulative_scaled_residual_one_eqv
#print axioms cumulative_scaled_residual_two_eqv
#print axioms theta_comparison_of_cumulative_residual_nonnegative
#print axioms growing_head_scaled_theta_identity
#print axioms growing_head_residual_eq_cumulative_minus_terminal
#print axioms growing_head_residual_nonnegative_of_terminal_payment
#print axioms growing_head_theta_premise_of_residual_nonnegative
#print axioms growing_head_theta_premise_of_terminal_payment
#print axioms harmonic_growing_anchor_theta_premise_of_residual_nonnegative
#print axioms harmonic_growing_anchor_theta_premise_of_terminal_payment
#print axioms growing_anchor_retune_of_residual_nonnegative

end YMGap.Continuum.HarmonicThetaCumulativeResidual
