/-
# Cap-aware depth schedule for the ORIGINAL remainder diagonals

The preceding fixed-width schedule makes the endpoint-mixing error small
before it is multiplied by the global scalar-square remainder cap `B`.
This module pays that outer factor as well.  It feeds

  epsilon / (1 + B)

to the existing lag schedule and returns an explicit depth at which the
complete cap-amplified lag contribution is at most `epsilon`.  Both literal
remainder diagonals are then bounded by

  B * (OWN + OWN) + epsilon.

The actual OWN deficit mean remains unestimated.  The schedule depends on
the spatial width through the existing mixing rate and proves no
width-uniform contraction, ORIGINAL-to-FREE comparison, cutoff removal,
continuum Hamiltonian, or Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitLagSchedule

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitDiagonalLagSchedule

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitLagControl
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitLagSchedule
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonal
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- One positive slack above the cap that multiplies the lag error. -/
def originalBulkDeficitDiagonalLagScale (s : Nat) (hs : 0 < s) : Q' :=
  1 + originalBulkScalarSquareRemainderCap s hs

theorem originalBulkDeficitDiagonalLagScale_positive
    (s : Nat) (hs : 0 < s) :
    (0 : Q') < originalBulkDeficitDiagonalLagScale s hs := by
  unfold originalBulkDeficitDiagonalLagScale
  exact Q'.pos_add_nonneg (by decide)
    (originalBulkScalarSquareRemainderCap_nonnegative s hs)

/-- Inner lag tolerance that also pays the outer diagonal cap. -/
def originalBulkDeficitDiagonalLagTolerance
    (s : Nat) (hs : 0 < s) (epsilon : Q') : Q' :=
  Q'.divPos epsilon (originalBulkDeficitDiagonalLagScale s hs)
    (originalBulkDeficitDiagonalLagScale_positive s hs)

theorem originalBulkDeficitDiagonalLagTolerance_positive
    (s : Nat) (hs : 0 < s) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < originalBulkDeficitDiagonalLagTolerance s hs epsilon := by
  unfold originalBulkDeficitDiagonalLagTolerance
  exact Q'.divPos_pos _ _
    (originalBulkDeficitDiagonalLagScale_positive s hs) hepsilon

/-- Executable fixed-width depth paying both copies of the deficit cap inside
the lag error and the further cap multiplying the diagonal budget. -/
def originalBulkDeficitDiagonalLagDepth {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (epsilon : Q') : Nat :=
  originalBulkDeficitLagDepth hw0 hw1 s hs
    (originalBulkDeficitDiagonalLagTolerance s hs epsilon)

/-- At the returned depth, the complete cap-amplified lag payment is at most
the requested tolerance. -/
theorem originalBulkDeficitDiagonalLagError_at_depth_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    originalBulkScalarSquareRemainderCap s hs *
        originalBulkDeficitLagError hw0 hw1 s hs
          (originalBulkDeficitDiagonalLagDepth hw0 hw1 s hs epsilon) ≤
      epsilon := by
  let bound := originalBulkScalarSquareRemainderCap s hs
  let scale := originalBulkDeficitDiagonalLagScale s hs
  let tolerance := originalBulkDeficitDiagonalLagTolerance s hs epsilon
  let depth := originalBulkDeficitDiagonalLagDepth hw0 hw1 s hs epsilon
  have herror : originalBulkDeficitLagError hw0 hw1 s hs depth ≤ tolerance := by
    exact originalBulkDeficitLagError_at_depth_le hw0 hw1 s hs
      (originalBulkDeficitDiagonalLagTolerance_positive s hs hepsilon)
  have hbound0 : (0 : Q') ≤ bound :=
    originalBulkScalarSquareRemainderCap_nonnegative s hs
  have hscaled :
      bound * originalBulkDeficitLagError hw0 hw1 s hs depth ≤
        bound * tolerance :=
    Q'.mul_le_mul_of_nonneg_left _ _ bound herror hbound0
  have hboundScale : bound ≤ scale := by
    have h := Q'.add_le_add_right (0 : Q') 1 bound (by decide)
    rw [Q'.zero_add'] at h
    exact h
  have htolerance0 : (0 : Q') ≤ tolerance :=
    Q'.le_of_lt (originalBulkDeficitDiagonalLagTolerance_positive s hs hepsilon)
  have hscale : bound * tolerance ≤ scale * tolerance :=
    Q'.mul_le_mul_of_nonneg_right _ _ tolerance hboundScale htolerance0
  have hcollapse : scale * tolerance ≈ epsilon := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv scale tolerance)
      (Q'.divPos_mul_eqv epsilon scale
        (originalBulkDeficitDiagonalLagScale_positive s hs))
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hcollapse))

/-- The whole milestone-372 scalar diagonal budget separates into twice the
actual OWN contribution plus the requested cap-aware lag tolerance. -/
theorem originalBulkDeficitDiagonalLagBudget_at_depth_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    let depth := originalBulkDeficitDiagonalLagDepth hw0 hw1 s hs epsilon
    let bound := originalBulkScalarSquareRemainderCap s hs
    let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage depth
    let lagError := originalBulkDeficitLagError hw0 hw1 s hs depth
    bound * ((own + lagError) + own) ≤
      bound * (own + own) + epsilon := by
  dsimp only
  let depth := originalBulkDeficitDiagonalLagDepth hw0 hw1 s hs epsilon
  let bound := originalBulkScalarSquareRemainderCap s hs
  let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage depth
  let lagError := originalBulkDeficitLagError hw0 hw1 s hs depth
  have hlag : bound * lagError ≤ epsilon :=
    originalBulkDeficitDiagonalLagError_at_depth_le
      hw0 hw1 s hs hepsilon
  have hrearrange :
      bound * ((own + lagError) + own) ≈
        bound * (own + own) + bound * lagError := by
    exact poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.add (.var 1) (.var 2)) (.var 1)))
      (.add
        (.mul (.var 0) (.add (.var 1) (.var 1)))
        (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => bound | 1 => own | _ => lagError)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrearrange)
    (Q'.add_le_add_left (bound * (own + own)) _ _ hlag)

/-- The lower shifted-remainder diagonal now exposes the actual OWN term and
pays the complete lag contribution by the requested tolerance. -/
theorem originalBulkScalarSquareRemainder_leftDiagonal_le_capAwareScheduled
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage L : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    let depth := originalBulkDeficitDiagonalLagDepth hw0 hw1 s hs epsilon
    let remainder := originalBulkScalarSquareRemainder s hs
    let center := originalBulkScalarSquareRemainderOwnMean
      hw0 hw1 s hs stage depth
    let bound := originalBulkScalarSquareRemainderCap s hs
    let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage depth
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) depth L depth
        (polyMul (shifted remainder center) (shifted remainder center)) ≤
      bound * (own + own) + epsilon := by
  dsimp only
  let depth := originalBulkDeficitDiagonalLagDepth hw0 hw1 s hs epsilon
  have hbase := originalBulkScalarSquareRemainder_leftDiagonal_le_ownMeanLag
    hw0 hw1 s hs stage depth L
  have hbudget := originalBulkDeficitDiagonalLagBudget_at_depth_le
    hw0 hw1 s hs stage hepsilon
  exact Q'.le_trans' _ _ _ hbase hbudget

/-- The chronologically lifted diagonal obeys the same cap-aware scheduled
budget at the identical returned depth. -/
theorem originalBulkScalarSquareRemainder_rightDiagonal_le_capAwareScheduled
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage L : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    let depth := originalBulkDeficitDiagonalLagDepth hw0 hw1 s hs epsilon
    let remainder := originalBulkScalarSquareRemainder s hs
    let center := originalBulkScalarSquareRemainderOwnMean
      hw0 hw1 s hs stage depth
    let bound := originalBulkScalarSquareRemainderCap s hs
    let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage depth
    let lifted := liftBoundary (L * N (s * s)) (shifted remainder center)
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) depth L depth (polyMul lifted lifted) ≤
      bound * (own + own) + epsilon := by
  dsimp only
  let depth := originalBulkDeficitDiagonalLagDepth hw0 hw1 s hs epsilon
  have hbase := originalBulkScalarSquareRemainder_rightDiagonal_le_ownMeanLag
    hw0 hw1 s hs stage depth L
  have hbudget := originalBulkDeficitDiagonalLagBudget_at_depth_le
    hw0 hw1 s hs stage hepsilon
  exact Q'.le_trans' _ _ _ hbase hbudget

#print axioms originalBulkDeficitDiagonalLagScale_positive
#print axioms originalBulkDeficitDiagonalLagTolerance_positive
#print axioms originalBulkDeficitDiagonalLagDepth
#print axioms originalBulkDeficitDiagonalLagError_at_depth_le
#print axioms originalBulkDeficitDiagonalLagBudget_at_depth_le
#print axioms originalBulkScalarSquareRemainder_leftDiagonal_le_capAwareScheduled
#print axioms originalBulkScalarSquareRemainder_rightDiagonal_le_capAwareScheduled

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitDiagonalLagSchedule
