/-
# Constructive depth schedule for the finite ORIGINAL deficit lag error

The existing endpoint-mixing rate may equal zero and is not uniform in the
spatial width.  The positive dominating rate

  1 - (1/2) * mixFraction

is nevertheless strictly between zero and one at every fixed nome and width.
Applying the constructive `powBaseCutoff` to this rate at tolerance
`epsilon / (1 + 2*B)` returns an explicit depth at which the actual lag error
`mixRate^n * (2*B)` is at most `epsilon`.

The resulting theorems substitute that tolerance into both literal diagonal
remainder bounds used by the finite Cauchy estimates.  The schedule depends on
width and on the cap `B`; it does not prove that the actual OWN deficit mean is
small, compare the ORIGINAL vector jet with the FREE Gaussian law, remove a
cutoff, or establish a continuum Hamiltonian or Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitLagControl
import YMGap.Continuum.BakryEmery
import YMGap.Constructive.CRealLog

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitLagSchedule

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixFraction mixFraction_positive mixFraction_le_one mixRate mixRate_nonnegative
    mixRate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitLagControl
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonal
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem sub_le_sub_local {a a' b b' : Q'}
    (ha : a ≤ a') (hb : b' ≤ b) : a + -b ≤ a' + -b' := by
  have hleft : a + -b ≤ a' + -b := Q'.add_le_add_right a a' (-b) ha
  have hright : a' + -b ≤ a' + -b' :=
    Q'.add_le_add_left a' (-b) (-b') (Q'.neg_le_neg hb)
  exact Q'.le_trans' _ _ _ hleft hright

private theorem sub_pos_of_lt_local {a b : Q'} (h : b < a) :
    (0 : Q') < a + -b := by
  have hlt : b.num * (a.den : Int) < a.num * (b.den : Int) := h
  apply CReal.pos_of_num_pos
  show 0 < a.num * (b.den : Int) + (-b.num) * (a.den : Int)
  have hsub : (0 : Int) < a.num * (b.den : Int) - b.num * (a.den : Int) :=
    Int.sub_pos.mpr hlt
  simpa only [Int.neg_mul, Int.sub_eq_add_neg] using hsub

/-- A positive fixed-width rate dominating the existing endpoint-mixing rate. -/
def originalBulkDeficitSafeMixRate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) : Q' :=
  1 + -(half * mixFraction hw0 hw1 width)

theorem originalBulkDeficitSafeMixRate_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) :
    (0 : Q') < originalBulkDeficitSafeMixRate hw0 hw1 width := by
  let fraction := mixFraction hw0 hw1 width
  have hscaled : half * fraction ≤ half * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left fraction 1 half
      (mixFraction_le_one hw0 hw1 width) half_nonneg
  have hscaledHalf : half * fraction ≤ half :=
    Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.mul_one_eqv half))
  have hscaledOne : half * fraction < (1 : Q') :=
    Q'.lt_of_le_of_lt hscaledHalf (by decide)
  unfold originalBulkDeficitSafeMixRate
  exact sub_pos_of_lt_local hscaledOne

theorem originalBulkDeficitSafeMixRate_lt_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) :
    originalBulkDeficitSafeMixRate hw0 hw1 width < (1 : Q') := by
  unfold originalBulkDeficitSafeMixRate
  exact BakryEmery.one_sub_lt_one
    (Q'.mul_pos (by decide : (0 : Q') < half)
      (mixFraction_positive hw0 hw1 width))

theorem mixRate_le_originalBulkDeficitSafeMixRate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) :
    mixRate hw0 hw1 width ≤
      originalBulkDeficitSafeMixRate hw0 hw1 width := by
  let fraction := mixFraction hw0 hw1 width
  have hfraction0 : (0 : Q') ≤ fraction :=
    Q'.le_of_lt (mixFraction_positive hw0 hw1 width)
  have hscaled : half * fraction ≤ (1 : Q') * fraction :=
    Q'.mul_le_mul_of_nonneg_right half 1 fraction (by decide) hfraction0
  have hscaledFraction : half * fraction ≤ fraction :=
    Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.one_mul_eqv fraction))
  unfold originalBulkDeficitSafeMixRate mixRate
  exact sub_le_sub_local (Q'.le_refl' 1) hscaledFraction

/-- One positive slack above the doubled trace-deficit cap. -/
def originalBulkDeficitLagScale (s : Nat) (hs : 0 < s) : Q' :=
  1 +
    (originalBulkScalarSquareRemainderCap s hs +
      originalBulkScalarSquareRemainderCap s hs)

theorem originalBulkDeficitLagScale_positive (s : Nat) (hs : 0 < s) :
    (0 : Q') < originalBulkDeficitLagScale s hs := by
  unfold originalBulkDeficitLagScale
  exact Q'.pos_add_nonneg (by decide)
    (Q'.zero_le_add _ _
      (originalBulkScalarSquareRemainderCap_nonnegative s hs)
      (originalBulkScalarSquareRemainderCap_nonnegative s hs))

/-- The rational power tolerance that pays both copies of the global cap. -/
def originalBulkDeficitLagTolerance
    (s : Nat) (hs : 0 < s) (epsilon : Q') : Q' :=
  Q'.divPos epsilon (originalBulkDeficitLagScale s hs)
    (originalBulkDeficitLagScale_positive s hs)

theorem originalBulkDeficitLagTolerance_positive
    (s : Nat) (hs : 0 < s) {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < originalBulkDeficitLagTolerance s hs epsilon := by
  unfold originalBulkDeficitLagTolerance
  exact Q'.divPos_pos _ _ (originalBulkDeficitLagScale_positive s hs) hepsilon

/-- Executable fixed-width depth at which the actual endpoint-mixing payment
is at most the requested positive rational tolerance. -/
def originalBulkDeficitLagDepth {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (epsilon : Q') : Nat :=
  HKConvGen.powBaseCutoff
    (originalBulkDeficitSafeMixRate hw0 hw1 (s * s))
    (originalBulkDeficitLagTolerance s hs epsilon)

/-- At the returned depth, the literal error from milestone 372 is no larger
than the supplied positive rational tolerance. -/
theorem originalBulkDeficitLagError_at_depth_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    originalBulkDeficitLagError hw0 hw1 s hs
        (originalBulkDeficitLagDepth hw0 hw1 s hs epsilon) ≤ epsilon := by
  let bound := originalBulkScalarSquareRemainderCap s hs
  let coefficient := bound + bound
  let rate := mixRate hw0 hw1 (s * s)
  let safeRate := originalBulkDeficitSafeMixRate hw0 hw1 (s * s)
  let scale := originalBulkDeficitLagScale s hs
  let tolerance := originalBulkDeficitLagTolerance s hs epsilon
  let depth := originalBulkDeficitLagDepth hw0 hw1 s hs epsilon
  have hrate0 : (0 : Q') ≤ rate := mixRate_nonnegative hw0 hw1 (s * s)
  have hrateSafe : rate ≤ safeRate :=
    mixRate_le_originalBulkDeficitSafeMixRate hw0 hw1 (s * s)
  have hpowerDominated : rate ^ depth ≤ safeRate ^ depth :=
    CRealLog.pow_le_pow_base rate safeRate hrate0 hrateSafe depth
  have hsafePower : safeRate ^ depth ≤ tolerance := by
    exact HKConvGen.pow_base_le_cutoff
      (originalBulkDeficitSafeMixRate_positive hw0 hw1 (s * s))
      (originalBulkDeficitSafeMixRate_lt_one hw0 hw1 (s * s))
      (originalBulkDeficitLagTolerance_positive s hs hepsilon)
  have hpower : rate ^ depth ≤ tolerance :=
    Q'.le_trans' _ _ _ hpowerDominated hsafePower
  have hcoefficient0 : (0 : Q') ≤ coefficient :=
    Q'.zero_le_add _ _
      (originalBulkScalarSquareRemainderCap_nonnegative s hs)
      (originalBulkScalarSquareRemainderCap_nonnegative s hs)
  have herror : rate ^ depth * coefficient ≤ tolerance * coefficient :=
    Q'.mul_le_mul_of_nonneg_right _ _ coefficient hpower hcoefficient0
  have hcoefficientScale : coefficient ≤ scale := by
    have h := Q'.add_le_add_right (0 : Q') 1 coefficient (by decide)
    rw [Q'.zero_add'] at h
    exact h
  have htolerance0 : (0 : Q') ≤ tolerance :=
    Q'.le_of_lt (originalBulkDeficitLagTolerance_positive s hs hepsilon)
  have hscale : tolerance * coefficient ≤ tolerance * scale :=
    Q'.mul_le_mul_of_nonneg_left _ _ tolerance hcoefficientScale htolerance0
  have hcollapse : tolerance * scale ≈ epsilon := by
    exact Q'.divPos_mul_eqv epsilon scale
      (originalBulkDeficitLagScale_positive s hs)
  unfold originalBulkDeficitLagError
  exact Q'.le_trans' _ _ _ herror
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hcollapse))

/-- The arbitrary-lag deficit mean at the returned depth differs from the
actual OWN mean by at most the requested tolerance. -/
theorem originalBulkDeficit_windowRatio_le_ownMean_add_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage L : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    let depth := originalBulkDeficitLagDepth hw0 hw1 s hs epsilon
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) depth L depth
        (sourcePolynomial (originalBulkDeficitExpression s hs)) ≤
      originalBulkDeficitOwnMean hw0 hw1 s hs stage depth + epsilon := by
  dsimp only
  let depth := originalBulkDeficitLagDepth hw0 hw1 s hs epsilon
  have hbase := originalBulkDeficit_windowRatio_le_ownMean_add_lagError
    hw0 hw1 s hs stage depth L
  have herror := originalBulkDeficitLagError_at_depth_le
    hw0 hw1 s hs hepsilon
  exact Q'.le_trans' _ _ _ hbase
    (Q'.add_le_add_left
      (originalBulkDeficitOwnMean hw0 hw1 s hs stage depth)
      (originalBulkDeficitLagError hw0 hw1 s hs depth) epsilon herror)

/-- The lower shifted-remainder diagonal has only the actual OWN mean and the
requested tolerance left in its scalar budget. -/
theorem originalBulkScalarSquareRemainder_leftDiagonal_le_scheduled {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage L : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    let depth := originalBulkDeficitLagDepth hw0 hw1 s hs epsilon
    let remainder := originalBulkScalarSquareRemainder s hs
    let center := originalBulkScalarSquareRemainderOwnMean
      hw0 hw1 s hs stage depth
    let bound := originalBulkScalarSquareRemainderCap s hs
    let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage depth
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) depth L depth
        (polyMul (shifted remainder center) (shifted remainder center)) ≤
      bound * ((own + epsilon) + own) := by
  dsimp only
  let depth := originalBulkDeficitLagDepth hw0 hw1 s hs epsilon
  let bound := originalBulkScalarSquareRemainderCap s hs
  let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage depth
  have hbase := originalBulkScalarSquareRemainder_leftDiagonal_le_ownMeanLag
    hw0 hw1 s hs stage depth L
  have herror := originalBulkDeficitLagError_at_depth_le
    hw0 hw1 s hs hepsilon
  have hinner := Q'.add_le_add_left own _ _ herror
  have hsum := Q'.add_le_add_right _ _ own hinner
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ bound hsum
    (originalBulkScalarSquareRemainderCap_nonnegative s hs)
  exact Q'.le_trans' _ _ _ hbase hscaled

/-- The chronologically lifted diagonal obeys the identical scheduled scalar
budget, so both Cauchy factors use the same returned depth. -/
theorem originalBulkScalarSquareRemainder_rightDiagonal_le_scheduled {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage L : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    let depth := originalBulkDeficitLagDepth hw0 hw1 s hs epsilon
    let remainder := originalBulkScalarSquareRemainder s hs
    let center := originalBulkScalarSquareRemainderOwnMean
      hw0 hw1 s hs stage depth
    let bound := originalBulkScalarSquareRemainderCap s hs
    let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage depth
    let lifted := liftBoundary (L * N (s * s)) (shifted remainder center)
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) depth L depth (polyMul lifted lifted) ≤
      bound * ((own + epsilon) + own) := by
  dsimp only
  let depth := originalBulkDeficitLagDepth hw0 hw1 s hs epsilon
  let bound := originalBulkScalarSquareRemainderCap s hs
  let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage depth
  have hbase := originalBulkScalarSquareRemainder_rightDiagonal_le_ownMeanLag
    hw0 hw1 s hs stage depth L
  have herror := originalBulkDeficitLagError_at_depth_le
    hw0 hw1 s hs hepsilon
  have hinner := Q'.add_le_add_left own _ _ herror
  have hsum := Q'.add_le_add_right _ _ own hinner
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ bound hsum
    (originalBulkScalarSquareRemainderCap_nonnegative s hs)
  exact Q'.le_trans' _ _ _ hbase hscaled

#print axioms originalBulkDeficitSafeMixRate_positive
#print axioms originalBulkDeficitSafeMixRate_lt_one
#print axioms mixRate_le_originalBulkDeficitSafeMixRate
#print axioms originalBulkDeficitLagScale_positive
#print axioms originalBulkDeficitLagTolerance_positive
#print axioms originalBulkDeficitLagDepth
#print axioms originalBulkDeficitLagError_at_depth_le
#print axioms originalBulkDeficit_windowRatio_le_ownMean_add_tolerance
#print axioms originalBulkScalarSquareRemainder_leftDiagonal_le_scheduled
#print axioms originalBulkScalarSquareRemainder_rightDiagonal_le_scheduled

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitLagSchedule
