/-
# Endpoint means of the original one-step window

Removing the unobserved step on either side identifies each endpoint
insertion with the existing two-message middle ratio.  Swapping those two
messages then proves that the endpoint means agree.  Every identity retains
the original finite action and positive partition; no cutoff or time limit is
taken here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEndpointMean

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (middleRatio_swap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- The lower endpoint insertion is the middle ratio with the unused step
absorbed into the right terminal message. -/
theorem lower_endpoint_mean {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    windowRatio hw0 hw1 K width hK n 1 n f ≈
      middleRatio hw0 hw1 K width hK n (n+1) f := by
  have hp : SupportedQuaternionBlocks ((0+1)*(N width)) f := by
    simpa only [Nat.zero_add, Nat.one_mul] using hf
  exact Q'.eqv_trans _ _ _
    (by simpa only [Nat.zero_add] using
      (windowRatio_pad_right hw0 hw1 K width hK n 0 n hp))
    (windowRatio_zero hw0 hw1 K width hK n (n+1) hf)

/-- The lifted upper endpoint insertion is the middle ratio with the unused
step absorbed into the left terminal message. -/
theorem upper_endpoint_mean {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    windowRatio hw0 hw1 K width hK n 1 n (liftBoundary (N width) f) ≈
      middleRatio hw0 hw1 K width hK (n+1) n f := by
  have hp : SupportedQuaternionBlocks ((0+1)*(N width)) f := by
    simpa only [Nat.zero_add, Nat.one_mul] using hf
  exact Q'.eqv_trans _ _ _
    (by simpa only [Nat.zero_add] using
      (windowRatio_pad_left hw0 hw1 K width hK n 0 n hp))
    (windowRatio_zero hw0 hw1 K width hK (n+1) n hf)

/-- Both endpoint insertions have the same normalized mean in the same
one-step window. -/
theorem endpoint_means_eqv {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    windowRatio hw0 hw1 K width hK n 1 n f ≈
      windowRatio hw0 hw1 K width hK n 1 n (liftBoundary (N width) f) := by
  exact Q'.eqv_trans _ _ _ (lower_endpoint_mean hw0 hw1 K width hK n hf)
    (Q'.eqv_trans _ _ _ (middleRatio_swap hw0 hw1 K width hK n (n+1) f)
      (Q'.eqv_symm (upper_endpoint_mean hw0 hw1 K width hK n hf)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEndpointMean

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEndpointMean.lower_endpoint_mean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEndpointMean.upper_endpoint_mean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEndpointMean.endpoint_means_eqv
