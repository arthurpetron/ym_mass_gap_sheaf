/-
# Original endpoint means and finite lag comparison

Equal terminal boundaries give the same mean at both endpoints of an
arbitrary chronological window. Exact padding identifies that mean with
the original middle ratio at terminal depths n and n+L. Comparing different
lags therefore uses right-boundary forgetting at a zero-transition window;
it does not assume finite stationarity or identify distinct partitions.

The consumer is the expansion of original centered endpoint products at
consecutive lags. All action factors, the supplied finite mean, and the
existing head cutoff guard remain unchanged. No response or scaling bound
is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (middleRatio_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion (liftBoundary_add)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] baseLinks windowRatio middleRatio mixRate

private theorem lower_pad {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n L : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    windowRatio hw0 hw1 K width hK m L n f ≈
      windowRatio hw0 hw1 K width hK m 0 (n+L) f := by
  induction L generalizing n with
  | zero =>
    simpa only [Nat.add_zero] using
      (Q'.eqv_refl (windowRatio hw0 hw1 K width hK m 0 n f))
  | succ L ih =>
    have hsize : N width ≤ (L+1)*(N width) := by
      rw [Nat.succ_mul]
      omega
    have hsp : SupportedQuaternionBlocks ((L+1)*(N width)) f := by
      intro term ht
      exact Nat.le_trans (hf term ht) (Nat.mul_le_mul_left 4 hsize)
    have hpad := windowRatio_pad_right hw0 hw1 K width hK m L n hsp
    have hnext := ih (n+1)
    have htime : (n+1)+L = n+(L+1) := by omega
    rw [htime] at hnext
    exact Q'.eqv_trans _ _ _ hpad hnext

private theorem upper_pad {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n L : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    windowRatio hw0 hw1 K width hK m L n (liftBoundary (L*(N width)) f) ≈
      windowRatio hw0 hw1 K width hK (m+L) 0 n f := by
  induction L generalizing m with
  | zero =>
    simpa only [Nat.zero_mul, Nat.add_zero, liftBoundary] using
      (Q'.eqv_refl (windowRatio hw0 hw1 K width hK m 0 n f))
  | succ L ih =>
    have hsp : SupportedQuaternionBlocks ((L+1)*(N width))
        (liftBoundary (L*(N width)) f) := by
      simpa only [Nat.succ_mul, Nat.add_comm] using lift_supported hf (L*(N width))
    have hplace : liftBoundary ((L+1)*(N width)) f =
        liftBoundary (N width) (liftBoundary (L*(N width)) f) := by
      rw [Nat.succ_mul, Nat.add_comm (L*(N width)) (N width), liftBoundary_add]
    have hpad := windowRatio_pad_left hw0 hw1 K width hK m L n hsp
    rw [← hplace] at hpad
    have hnext := ih (m+1)
    have htime : (m+1)+L = m+(L+1) := by omega
    rw [htime] at hnext
    exact Q'.eqv_trans _ _ _ hpad hnext

/-- The lower endpoint mean retains the exact original two terminal depths. -/
theorem lower_endpoint_mean {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    windowRatio hw0 hw1 K width hK n L n f ≈
      middleRatio hw0 hw1 K width hK n (n+L) f :=
  Q'.eqv_trans _ _ _ (lower_pad hw0 hw1 K width hK n n L hf)
    (windowRatio_zero hw0 hw1 K width hK n (n+L) hf)

/-- The actual shifted upper endpoint has the SAME finite mean as the lower
endpoint. This uses original transfer symmetry, not stationarity. -/
theorem upper_endpoint_mean {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    windowRatio hw0 hw1 K width hK n L n (liftBoundary (L*(N width)) f) ≈
      middleRatio hw0 hw1 K width hK n (n+L) f :=
  Q'.eqv_trans _ _ _ (upper_pad hw0 hw1 K width hK n n L hf)
    (Q'.eqv_trans _ _ _ (windowRatio_zero hw0 hw1 K width hK (n+L) n hf)
      (middleRatio_swap hw0 hw1 K width hK (n+L) n f))

theorem endpoint_means_eqv {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    windowRatio hw0 hw1 K width hK n L n f ≈
      windowRatio hw0 hw1 K width hK n L n (liftBoundary (L*(N width)) f) :=
  Q'.eqv_trans _ _ _ (lower_endpoint_mean hw0 hw1 K width hK n L hf)
    (Q'.eqv_symm (upper_endpoint_mean hw0 hw1 K width hK n L hf))

/-- Both orders of the original finite mean comparison at arbitrary lags.
The error depends on the shared boundary depth n, not on L or J. -/
theorem endpoint_mean_lags_commonTail {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n L J : Nat) {f : RatPoly} {C : Q'} (I : Interval (N width) f C) :
    windowRatio hw0 hw1 K width hK n L n f ≤
        windowRatio hw0 hw1 K width hK n J n f + mixRate hw0 hw1 width ^ n * (C+C) ∧
      windowRatio hw0 hw1 K width hK n J n f ≤
        windowRatio hw0 hw1 K width hK n L n f + mixRate hw0 hw1 width ^ n * (C+C) := by
  have I0 : Interval ((0+1)*(N width)) f C := by
    simpa only [Nat.zero_add, Nat.one_mul] using I
  have h := windowRatio_right_commonTail hw0 hw1 K width hK n 0 n (n+L) (n+J)
    I0 (by omega) (by omega)
  have hL := lower_pad hw0 hw1 K width hK n n L I.support
  have hJ := lower_pad hw0 hw1 K width hK n n J I.support
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
      (Q'.le_trans' _ _ _ h.1
        (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_symm hJ) (Q'.eqv_refl _)))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hJ)
      (Q'.le_trans' _ _ _ h.2
        (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_symm hL) (Q'.eqv_refl _))))⟩

/-- The actual original middle mean inherits both signs of the supplied
interval cap, for arbitrary finite terminal depths. -/
theorem middleRatio_interval_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat)
    {f : RatPoly} {C : Q'} (I : Interval (N width) f C) :
    -C ≤ middleRatio hw0 hw1 K width hK m n f ∧
      middleRatio hw0 hw1 K width hK m n f ≤ C := by
  have I0 : Interval ((0+1)*(N width)) f C := by
    simpa only [Nat.zero_add, Nat.one_mul] using I
  have h := windowRatio_later_bounds hw0 hw1 K width hK m 0 0 n I0 (Nat.zero_le n)
  change -C ≤ windowRatio hw0 hw1 K width hK m 0 n f ∧
    windowRatio hw0 hw1 K width hK m 0 n f ≤ C at h
  have he := windowRatio_zero hw0 hw1 K width hK m n I.support
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.le_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) h.2⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl.lower_endpoint_mean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl.upper_endpoint_mean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl.endpoint_means_eqv
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl.endpoint_mean_lags_commonTail
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl.middleRatio_interval_bounds
