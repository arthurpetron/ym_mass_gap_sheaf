/-
# Exact arithmetic corridor for the unresolved lower-six tail

The local second-flux consumer ranges from the first mode after the moving
square-root window through `growingAnchor`.  This file records the two exact
integer inequalities defining that corridor and packages the lower boundary
as a nonnegative rational coordinate

`X = 2 n^2 - (k + 2)`.

These are consequences of the existing window definitions, not additional
analytic hypotheses.
-/

import YMGap.Continuum.HarmonicLowerSixTailLocalWeightReduction
import YMGap.Continuum.ChebOrthoBracketDecay

namespace YMGap.Continuum.HarmonicLowerSixTailCorridor

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- The first mode beyond the moving left window lies on the
`k+2 <= 2 n^2` side of the square-root boundary. -/
theorem lowerSixTail_den_le_two_sq_of_left_succ_le
    {k n : Nat} (hn : thetaWindowLeft k + 1 ≤ n) :
    k + 2 ≤ 2 * (n * n) := by
  let c := thetaWindowCenter k
  have hcn : c + 1 ≤ 2 * n := by
    dsimp only [c]
    unfold thetaWindowLeft at hn
    omega
  have hroot :
      thetaWindowLength k < (c + 1) * (c + 1) := by
    dsimp only [c]
    unfold thetaWindowCenter
    exact ChebOrthoBracketDecay.isqrt_ub _
  have hsquare : (c + 1) * (c + 1) ≤ (2 * n) * (2 * n) :=
    Nat.mul_le_mul hcn hcn
  have hfour : (c + 1) * (c + 1) ≤ 4 * (n * n) := by
    calc
      (c + 1) * (c + 1) ≤ (2 * n) * (2 * n) := hsquare
      _ = 4 * (n * n) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  unfold thetaWindowLength at hroot
  omega

/-- The production tail cutoff is exactly the complementary linear wall
`n <= 2(k+2)`. -/
theorem lowerSixTail_mode_le_two_den_of_le_growingAnchor
    {k n : Nat} (hn : n ≤ growingAnchor k) :
    n ≤ 2 * (k + 2) := by
  unfold growingAnchor at hn
  exact hn

/-- Nonnegative integer distance from the lower square-root boundary. -/
def lowerSixTailBoundaryNat (k n : Nat) : Nat :=
  2 * (n * n) - (k + 2)

/-- Exact rational incarnation of the lower square-root-boundary distance. -/
def lowerSixTailBoundaryX (k n : Nat) : Q' :=
  Q'.ofNat (lowerSixTailBoundaryNat k n)

theorem lowerSixTailBoundaryNat_add_den
    {k n : Nat} (hn : thetaWindowLeft k + 1 ≤ n) :
    k + 2 + lowerSixTailBoundaryNat k n = 2 * (n * n) := by
  have hden := lowerSixTail_den_le_two_sq_of_left_succ_le hn
  unfold lowerSixTailBoundaryNat
  omega

theorem lowerSixTailBoundaryX_nonnegative (k n : Nat) :
    (0 : Q') ≤ lowerSixTailBoundaryX k n := by
  unfold lowerSixTailBoundaryX
  exact HeatKernelRGStep.zero_le_ofNat _

/-- Adding the denominator back to `X` recovers the exact doubled square. -/
theorem lowerSixTail_den_add_boundaryX_eqv_two_sq
    {k n : Nat} (hn : thetaWindowLeft k + 1 ≤ n) :
    Q'.ofNat (k + 2) + lowerSixTailBoundaryX k n ≈
      Q'.ofNat (2 * (n * n)) := by
  have hadd := Q'.ofNat_add_eqv (k + 2) (lowerSixTailBoundaryNat k n)
  have hnat := lowerSixTailBoundaryNat_add_den hn
  rw [hnat] at hadd
  unfold lowerSixTailBoundaryX
  exact Q'.eqv_symm hadd

private theorem ofNat_two_sq_eqv (n : Nat) :
    Q'.ofNat (2 * (n * n)) ≈
      Q'.ofNat 2 * RingNormaliser.qpow (Q'.ofNat n) 2 := by
  have houter := HeatKernelRGStep.ofNat_mul_eqv 2 (n * n)
  have hinner := HeatKernelRGStep.ofNat_mul_eqv n n
  have hpow' :
      RingNormaliser.qpow (Q'.ofNat n) 2 ≈
        Q'.ofNat n * Q'.ofNat n := by
    unfold RingNormaliser.qpow
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.one_mul_eqv (Q'.ofNat n))
  have hpow :
      Q'.ofNat n * Q'.ofNat n ≈
        RingNormaliser.qpow (Q'.ofNat n) 2 :=
    Q'.eqv_symm hpow'
  exact Q'.eqv_trans _ _ _ houter
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ hinner hpow))

private abbrev PE := RingNormaliser.PolyExpr

private def pBoundaryMoveL : PE := .var 1

private def pBoundaryMoveR : PE :=
  .add (.add (.var 0) (.var 1)) (.neg (.var 0))

private theorem pBoundaryMove_normal :
    RingNormaliser.normalize pBoundaryMoveL =
      RingNormaliser.normalize pBoundaryMoveR := by
  decide

private theorem boundary_move_algebra (D X : Q') :
    X ≈ (D + X) + -D := by
  simpa [pBoundaryMoveL, pBoundaryMoveR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pBoundaryMoveL pBoundaryMoveR pBoundaryMove_normal
      (fun | 0 => D | _ => X))

/-- Exact subtraction normal form for the nonnegative boundary coordinate. -/
theorem lowerSixTailBoundaryX_eqv_two_sq_sub_den
    {k n : Nat} (hn : thetaWindowLeft k + 1 ≤ n) :
    lowerSixTailBoundaryX k n ≈
      Q'.ofNat 2 * RingNormaliser.qpow (Q'.ofNat n) 2 +
        -Q'.ofNat (k + 2) := by
  let D := Q'.ofNat (k + 2)
  let X := lowerSixTailBoundaryX k n
  let T := Q'.ofNat 2 * RingNormaliser.qpow (Q'.ofNat n) 2
  have hsum : D + X ≈ T :=
    Q'.eqv_trans _ (Q'.ofNat (2 * (n * n))) _
      (lowerSixTail_den_add_boundaryX_eqv_two_sq hn)
      (ofNat_two_sq_eqv n)
  have hmove : X ≈ (D + X) + -D := by
    exact boundary_move_algebra D X
  have hreplace : (D + X) + -D ≈ T + -D :=
    Q'.add_eqv_congr' hsum (Q'.eqv_refl (-D))
  dsimp only [D, X, T] at hmove hreplace ⊢
  exact Q'.eqv_trans _ _ _ hmove hreplace

#print axioms lowerSixTail_den_le_two_sq_of_left_succ_le
#print axioms lowerSixTail_mode_le_two_den_of_le_growingAnchor
#print axioms lowerSixTailBoundaryNat_add_den
#print axioms lowerSixTailBoundaryX_nonnegative
#print axioms lowerSixTail_den_add_boundaryX_eqv_two_sq
#print axioms lowerSixTailBoundaryX_eqv_two_sq_sub_den

end YMGap.Continuum.HarmonicLowerSixTailCorridor
