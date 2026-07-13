/-
# Linearized harmonic theta carrier

The exact retune cube lies above its tangent carrier

  1 - 3 u_k / 2.

This module packages the corresponding growing-head residual, including an
integer-cleared form.  It is a stronger target than the exact cubic residual,
but it has a lower-degree coefficient profile and therefore supplies an
independent Pascal/Bernstein route.
-/

import YMGap.Continuum.HarmonicRetuneFloor

namespace YMGap.Continuum.HarmonicThetaLinearCarrier

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicRetuneFloor
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicVariableAnchorThetaBridge
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private def halfQ : Q' := Q'.mkPos 1 2 (by decide)

/-- Exact denominator clearing for the harmonic unit. -/
theorem harmonicUnit_mul_den (k : Nat) :
    harmU k * Q'.ofNat (k + 2) ≈ (1 : Q') := by
  unfold harmU unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

/-- Exact projective coordinate of the harmonic ray:
`w_k (k+2) = k+1`. -/
theorem harmonicWeight_mul_den (k : Nat) :
    harmW k * Q'.ofNat (k + 2) ≈ Q'.ofNat (k + 1) := by
  have hM : Q'.ofNat (k + 2) ≈ Q'.ofNat (k + 1) + (1 : Q') := by
    simpa [Nat.add_assoc] using Q'.ofNat_add_eqv (k + 1) 1
  unfold harmW oneSub
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv 1 (-(harmU k)) (Q'.ofNat (k + 2))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.one_mul_eqv (Q'.ofNat (k + 2)))
      (Q'.neg_mul_eqv (harmU k) (Q'.ofNat (k + 2)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hM
      (Q'.neg_eqv_congr _ _ (harmonicUnit_mul_den k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (Q'.ofNat (k + 1)) 1 (-1)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.ofNat (k + 1)) _ _
      (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact QPoly.q_add_zero_eqv _

/-- Tangent lower carrier for the harmonic retune cube. -/
def harmonicLinearRetune (k : Nat) : Q' :=
  (1 : Q') + -(Q'.ofNat 3 * (halfQ * harmU k))

/-- Unscaled residual for the growing-head comparison with the tangent
retune carrier. -/
def harmonicLinearHeadResidual (k : Nat) : Q' :=
  harmonicLinearRetune k *
      integerThetaSum (harmW k) (growingAnchor k) +
    -(harmW k *
      halfThetaSum (harmW k) (growingAnchor k + 1))

/-- Integer-cleared form of the same residual.  Writing `b=u_k/2`, it is
`(2-6b) I - 2 L`. -/
def harmonicLinearHeadResidualCleared (k : Nat) : Q' :=
  (Q'.ofNat 2 +
      -(Q'.ofNat 6 * (halfQ * harmU k))) *
        integerThetaSum (harmW k) (growingAnchor k) +
    -(Q'.ofNat 2 *
      (harmW k *
        halfThetaSum (harmW k) (growingAnchor k + 1)))

/-- The tangent carrier is uniformly positive (in fact at least one
quarter) on the entire harmonic schedule. -/
theorem quarter_le_harmonicLinearRetune (k : Nat) :
    Q'.mkPos 1 4 (by decide) ≤ harmonicLinearRetune k := by
  let b : Q' := halfQ * harmU k
  have hb : b ≤ halfQ * halfQ := by
    unfold b
    exact Q'.mul_le_mul_of_nonneg_left _ _ halfQ
      (harmU_le_half k) (by decide)
  have hthree : Q'.ofNat 3 * b ≤
      Q'.ofNat 3 * (halfQ * halfQ) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3) hb (by decide)
  have hneg := Q'.neg_le_neg hthree
  have hadd := Q'.add_le_add_left (1 : Q') _ _ hneg
  exact Q'.le_trans' _ _ _
    (by decide : Q'.mkPos 1 4 (by decide) ≤
      (1 : Q') + -(Q'.ofNat 3 * (halfQ * halfQ)))
    (by simpa [harmonicLinearRetune, b] using hadd)

/-- Public comparison between the tangent carrier and the exact retune
cube. -/
theorem harmonicLinearRetune_le_retuneCube (k : Nat) :
    harmonicLinearRetune k ≤ retuneCube (harmW k) := by
  simpa [harmonicLinearRetune, halfQ] using harmonic_retune_linear_lower k

private def clearLinearL : RingNormaliser.PolyExpr :=
  let b := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let L := RingNormaliser.PolyExpr.var 2
  .add
    (.mul (.add (.const 2) (.neg (.mul (.const 6) b))) I)
    (.neg (.mul (.const 2) L))

private def clearLinearR : RingNormaliser.PolyExpr :=
  let b := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let L := RingNormaliser.PolyExpr.var 2
  .mul (.const 2)
    (.add
      (.mul (.add (.const 1) (.neg (.mul (.const 3) b))) I)
      (.neg L))

private theorem clearLinear_normal :
    RingNormaliser.normalize clearLinearL =
      RingNormaliser.normalize clearLinearR := by
  decide

private theorem clear_linear_identity (b I L : Q') :
    (Q'.ofNat 2 + -(Q'.ofNat 6 * b)) * I +
        -(Q'.ofNat 2 * L) ≈
      Q'.ofNat 2 *
        (((1 : Q') + -(Q'.ofNat 3 * b)) * I + -L) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    clearLinearL clearLinearR clearLinear_normal
    (fun
      | 0 => b
      | 1 => I
      | _ => L)
  simpa [clearLinearL, clearLinearR, RingNormaliser.eval] using h

private theorem finSum_nonnegative (f : Nat → Q')
    (hf : ∀ j, (0 : Q') ≤ f j) : ∀ N, (0 : Q') ≤ finSum f N
  | 0 => Q'.le_refl' 0
  | N + 1 => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ (finSum_nonnegative f hf N) (hf N)

/-- Every finite harmonic integer-theta head is nonnegative. -/
theorem harmonic_integerThetaSum_nonnegative (k N : Nat) :
    (0 : Q') ≤ integerThetaSum (harmW k) N := by
  unfold integerThetaSum
  apply finSum_nonnegative
  intro j
  unfold integerThetaTerm
  exact Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _)
    (qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _)

/-- The cleared tangent residual is exactly twice the unscaled one. -/
theorem harmonic_linear_head_residual_cleared_eqv (k : Nat) :
    harmonicLinearHeadResidualCleared k ≈
      Q'.ofNat 2 * harmonicLinearHeadResidual k := by
  unfold harmonicLinearHeadResidualCleared harmonicLinearHeadResidual
    harmonicLinearRetune halfQ
  exact clear_linear_identity _ _ _

private theorem residual_nonnegative_of_cleared {R C : Q'}
    (hC : (0 : Q') ≤ C) (hCR : C ≈ Q'.ofNat 2 * R) :
    (0 : Q') ≤ R := by
  have htwoR : (0 : Q') ≤ Q'.ofNat 2 * R :=
    Q'.le_trans' _ _ _ hC (Q'.le_of_eqv hCR)
  have hscaled : Q'.ofNat 2 * (0 : Q') ≤ Q'.ofNat 2 * R :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv _)) htwoR
  exact Q'.le_of_mul_le_mul_left hscaled (by decide)

private theorem add_neg_cancel (a b : Q') :
    a + (b + -a) ≈ b := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv a b (-a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-a) (Q'.add_comm_eqv a b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b a (-a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left b _ _ (Q'.add_neg_self_eqv a)) ?_
  exact QPoly.q_add_zero_eqv b

/-- Nonnegativity of the unscaled tangent residual gives the stronger linear
theta-head comparison. -/
theorem harmonic_linear_theta_head_of_residual_nonnegative
    (k : Nat)
    (hres : (0 : Q') ≤ harmonicLinearHeadResidual k) :
    harmW k * halfThetaSum (harmW k) (growingAnchor k + 1) ≤
      harmonicLinearRetune k *
        integerThetaSum (harmW k) (growingAnchor k) := by
  let L := harmW k *
    halfThetaSum (harmW k) (growingAnchor k + 1)
  let T := harmonicLinearRetune k *
    integerThetaSum (harmW k) (growingAnchor k)
  have hadd : L ≤ L + harmonicLinearHeadResidual k :=
    Q'.add_le_self_of_nonneg L _ hres
  have hid : L + harmonicLinearHeadResidual k ≈ T := by
    unfold harmonicLinearHeadResidual
    dsimp [L, T]
    exact add_neg_cancel _ _
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hid)

/-- The stronger linear comparison implies the exact cubic-retune theta
premise because the integer theta head is nonnegative. -/
theorem harmonic_theta_head_of_linear_residual_nonnegative
    (k : Nat)
    (hres : (0 : Q') ≤ harmonicLinearHeadResidual k) :
    harmW k * halfThetaSum (harmW k) (growingAnchor k + 1) ≤
      retuneCube (harmW k) *
        integerThetaSum (harmW k) (growingAnchor k) := by
  have hlinear := harmonic_linear_theta_head_of_residual_nonnegative k hres
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _
    (integerThetaSum (harmW k) (growingAnchor k))
    (harmonicLinearRetune_le_retuneCube k)
    (harmonic_integerThetaSum_nonnegative k (growingAnchor k))
  exact Q'.le_trans' _ _ _ hlinear hmul

/-- Integer-cleared residual nonnegativity is a sufficient all-later retune
certificate on the harmonic schedule. -/
theorem growing_anchor_retune_of_linear_cleared_nonnegative
    (k M : Nat)
    (hres : (0 : Q') ≤ harmonicLinearHeadResidualCleared k) :
    adjCorr (harmW k) (growingAnchor k + 1 + M) ≤
      retuneCube (harmW k) *
        coordNormSq (harmW k) (growingAnchor k + 1 + M) := by
  have hraw : (0 : Q') ≤ harmonicLinearHeadResidual k :=
    residual_nonnegative_of_cleared hres
      (harmonic_linear_head_residual_cleared_eqv k)
  exact growing_anchor_retune_of_theta_head k M
    (harmonic_theta_head_of_linear_residual_nonnegative k hraw)

#print axioms harmonic_integerThetaSum_nonnegative
#print axioms harmonicUnit_mul_den
#print axioms harmonicWeight_mul_den
#print axioms quarter_le_harmonicLinearRetune
#print axioms harmonicLinearRetune_le_retuneCube
#print axioms harmonic_linear_head_residual_cleared_eqv
#print axioms harmonic_linear_theta_head_of_residual_nonnegative
#print axioms harmonic_theta_head_of_linear_residual_nonnegative
#print axioms growing_anchor_retune_of_linear_cleared_nonnegative

end YMGap.Continuum.HarmonicThetaLinearCarrier
