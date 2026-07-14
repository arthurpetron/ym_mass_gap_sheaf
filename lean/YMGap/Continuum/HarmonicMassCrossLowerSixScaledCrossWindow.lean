/-
Two-sided window coordinates for the shared lower-six cross-scale sum.

The denominator-scaled step is not pointwise monotone and its ordinary
cumulative prefixes are not all nonnegative.  The exact shared sum is
therefore split at the same square-root right edge used by the one-scale
suffix proof.  This retains the complete positive-side reserve instead of
discarding the cancellation needed by the scaled induction.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowDifference

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossWindow

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-- One common-mode contribution to the denominator-scaled step. -/
def lowerSixScaledCrossTerm (k j : Nat) : Q' :=
  Q'.ofNat (k + 3) * lowerSixWeightedAbelTerm (k + 1) j +
    -(Q'.ofNat (k + 2) * lowerSixWeightedAbelTerm k j)

/-- Cumulative cross-scale prefix of arbitrary length. -/
def lowerSixScaledCrossPrefix (k N : Nat) : Q' :=
  finSum (lowerSixScaledCrossTerm k) N

/-- Prefix through the established square-root right edge. -/
def lowerSixScaledCrossWindowPrefix (k : Nat) : Q' :=
  lowerSixScaledCrossPrefix k (thetaWindowRight k)

/-- Complete remaining common-mode suffix. -/
def lowerSixScaledCrossWindowSuffix (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixScaledCrossTerm k (thetaWindowRight k + j))
    (growingAnchor k - thetaWindowRight k)

private theorem thetaWindowRight_le_anchor_same
    {k : Nat} (hk : 48 ≤ k) :
    thetaWindowRight k ≤ growingAnchor k := by
  let c := thetaWindowCenter k
  have hc : 9 ≤ c := by
    dsimp only [c]
    exact thetaWindowCenter_ge_nine (show 38 ≤ k by omega)
  have hsq : c * c ≤ thetaWindowLength k := by
    dsimp only [c, thetaWindowCenter]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hright : thetaWindowRight k + 1 ≤ 2 * c + 1 := by
    unfold thetaWindowRight
    dsimp only [c]
    have hdiv := Nat.div_le_self (thetaWindowCenter k) 4
    omega
  have hroom : 2 * c + 1 ≤ c * c := by
    have hmul := Nat.mul_le_mul_right c (show 3 ≤ c by omega)
    have hlinear : 2 * c + 1 ≤ 3 * c := by omega
    exact Nat.le_trans hlinear (by simpa [Nat.mul_comm] using hmul)
  rw [thetaWindowLength_eq_anchor] at hsq
  omega

/-- Exact prefix/suffix decomposition of the sole shared-mode residual. -/
theorem lowerSixScaledCrossShared_eqv_window {k : Nat} (hk : 48 ≤ k) :
    lowerSixScaledCrossShared k ≈
      lowerSixScaledCrossWindowPrefix k +
        lowerSixScaledCrossWindowSuffix k := by
  let R := thetaWindowRight k
  let A := growingAnchor k
  let f := lowerSixScaledCrossTerm k
  have hRA : R ≤ A := by
    dsimp only [R, A]
    exact thetaWindowRight_le_anchor_same hk
  have hcount : A = R + (A - R) := by omega
  have hsplit := finSum_split f R (A - R)
  rw [← hcount] at hsplit
  unfold lowerSixScaledCrossShared lowerSixScaledCrossWindowPrefix
    lowerSixScaledCrossPrefix lowerSixScaledCrossWindowSuffix
    lowerSixScaledCrossTerm
  dsimp only [R, A, f] at hsplit ⊢
  exact hsplit

/-- The corrected two-sided payment is sufficient for the uniform scaled
step. -/
theorem lowerSixScaledWindowStep_of_crossWindowPayment
    {k : Nat} (hk : 48 ≤ k)
    (hpay : -lowerSixScaledCrossWindowPrefix k ≤
      lowerSixScaledCrossWindowSuffix k) :
    LowerSixScaledWindowStep k := by
  have hsum : (0 : Q') ≤
      lowerSixScaledCrossWindowPrefix k +
        lowerSixScaledCrossWindowSuffix k := by
    have h := Q'.add_le_add_left
      (lowerSixScaledCrossWindowPrefix k) _ _ hpay
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.add_neg_self_eqv (lowerSixScaledCrossWindowPrefix k)))) h
  have hshared : (0 : Q') ≤ lowerSixScaledCrossShared k :=
    Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv
        (Q'.eqv_symm (lowerSixScaledCrossShared_eqv_window hk)))
  exact lowerSixScaledWindowStep_of_shared_nonnegative hk hshared

/-- The ordinary cumulative-prefix criterion fails inside the current
all-scale regime: through mode 22 at scale 247 the scaled cross prefix is
strictly negative. -/
theorem lowerSixScaledCross_plainPrefix_fails_k247 :
    ¬ ((0 : Q') ≤ lowerSixScaledCrossPrefix 247 22) := by
  unfold lowerSixScaledCrossPrefix lowerSixScaledCrossTerm
    lowerSixWeightedAbelTerm lowerSixAbelCarrier lowerSixAbelWeight
    lowerSixModeCarrier lowerSixModeWeight lowerSixDirichletProfile
    thetaRootSlope harmW harmU oneSub unit finSum qpow
  decide

#print axioms lowerSixScaledCrossShared_eqv_window
#print axioms lowerSixScaledWindowStep_of_crossWindowPayment
#print axioms lowerSixScaledCross_plainPrefix_fails_k247

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossWindow
