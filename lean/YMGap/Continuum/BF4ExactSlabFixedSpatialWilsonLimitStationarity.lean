/-
# Discrete time stationarity of the same original Wilson limits

Unequal finite padding changes both external boundary lengths but keeps the
complete original normalized action. The existing common-tail estimate is
uniform in the retained cutoff and explicitly controls independent boundary
lengths. Thus padding identifies the two already constructed joint limits,
without identifying their different Cauchy witnesses or representative
reindexings. The established spatial convergence then gives stationarity of
the actual three-regulator limit for translations fitting the same window.

Nome and physical lattice spacing remain fixed. This scalar identity is an
input to time balance on the enlarged Wilson carrier, not a completed time
operator, a strict bound on that carrier, or a continuum construction.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowStationarity
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
import YMGap.Constructive.CRealLimitClose

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowStationarity
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (centeredExpression centered_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenter_mapOffsets)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit (windowTimeModulus)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary
  (windowTimeCap windowTimeCap_nonnegative polynomialWindow_commonTail)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

attribute [local irreducible] mixRate windowTimeCap windowRatio originalWindowScalar originalJointLimit spatialLimit

/-- At the SAME retained heat stage, four independent late boundary lengths
are controlled by the existing explicit modulus of the actual source cap. -/
theorem originalWindow_rectangle {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e)
    (epsilon : Q') (heps : (0 : Q') < epsilon) (stage m n i j : Nat)
    (hm : windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial e)) epsilon ≤ m)
    (hn : windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial e)) epsilon ≤ n)
    (hi : windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial e)) epsilon ≤ i)
    (hj : windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial e)) epsilon ≤ j) :
    originalWindowScalar hw0 hw1 L e stage m n ≤
        originalWindowScalar hw0 hw1 L e stage i j + epsilon ∧
      originalWindowScalar hw0 hw1 L e stage i j ≤
        originalWindowScalar hw0 hw1 L e stage m n + epsilon := by
  let s := geometricCutoff (mixRate hw0 hw1 width)
    (windowTimeCap hw0 hw1 width (polynomialCap (sourcePolynomial e))) epsilon
  have hm' : s+1 ≤ m := by
    change 1+s ≤ m at hm
    omega
  have hn' : s+1 ≤ n := by
    change 1+s ≤ n at hn
    omega
  have hi' : s+1 ≤ i := by
    change 1+s ≤ i at hi
    omega
  have hj' : s+1 ≤ j := by
    change 1+s ≤ j at hj
    omega
  have hb := polynomialWindow_commonTail hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) L s m n i j (sourcePolynomial e)
    (source_supported L e he) hm' hn' hi' hj'
  have herror := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width)
    (windowTimeCap_nonnegative hw0 hw1 width (polynomialCap_nonnegative (sourcePolynomial e)))
    heps s (Nat.le_refl s)
  have hfirst := Q'.le_trans' _ _ _ hb.1 (Q'.add_le_add_left _ _ _ herror)
  have hsecond := Q'.le_trans' _ _ _ hb.2 (Q'.add_le_add_left _ _ _ herror)
  have hp := originalWindowScalar_pin hw0 hw1 L e he stage m n
  have hq := originalWindowScalar_pin hw0 hw1 L e he stage i j
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
      (Q'.le_trans' _ _ _ hfirst (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hq))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hq)
      (Q'.le_trans' _ _ _ hsecond (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hp)))⟩

/-- Existing joint limits agree after arbitrary unequal padding. The
comparison threshold is the pre-existing Type-valued windowTimeModulus. -/
theorem originalJoint_padding {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L left right : Nat) (e : WindowExpression width) (he : Within L e) :
    Equiv (originalJointLimit hw0 hw1 (L+left+right) (shift left e)
      (shift_within_padding L left right e he)) (originalJointLimit hw0 hw1 L e he) := by
  apply Equiv_of_limit_of_close
    (originalJoint_diagonal_converges hw0 hw1 (L+left+right) (shift left e)
      (shift_within_padding L left right e he))
    (originalJoint_diagonal_converges hw0 hw1 L e he)
  intro epsilon heps
  refine ⟨windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial e)) epsilon,
    fun s hs => ⟨0, fun _ _ => ?_⟩⟩
  have hb := originalWindow_rectangle hw0 hw1 L e he epsilon heps s (s+left) (s+right) s s
    (Nat.le_trans hs (Nat.le_add_right s left))
    (Nat.le_trans hs (Nat.le_add_right s right)) hs hs
  have hp := originalScalar_padding hw0 hw1 L left right e he s s s
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) hb.1,
    Q'.le_trans' _ _ _ hb.2 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hp))⟩

/-- A fitting nonnegative shift preserves the existing joint limit in the
SAME displayed window; both sides compare to one shorter original window. -/
theorem originalJoint_shift_within_window {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L total d : Nat) (e : WindowExpression width)
    (he : Within L e) (hfit : L+d ≤ total) :
    Equiv (originalJointLimit hw0 hw1 total (shift d e)
      (within_mono hfit _ (shift_within L d e he)))
      (originalJointLimit hw0 hw1 total e
        (within_mono (by omega : L ≤ total) e he)) := by
  have hleft := originalJoint_padding hw0 hw1 L d (total-(L+d)) e he
  have hright := originalJoint_padding hw0 hw1 L 0 (total-L) e he
  have hlenLeft : L+d+(total-(L+d)) = total := by omega
  have hlenRight : L+0+(total-L) = total := by omega
  have hfirst : Equiv (originalJointLimit hw0 hw1 total (shift d e)
      (within_mono hfit _ (shift_within L d e he)))
      (originalJointLimit hw0 hw1 L e he) := by
    simpa only [hlenLeft] using hleft
  have hsecond : Equiv (originalJointLimit hw0 hw1 total e
      (within_mono (by omega : L ≤ total) e he))
      (originalJointLimit hw0 hw1 L e he) := by
    simpa only [hlenRight, shift_zero] using hright
  exact hfirst.trans hsecond.symm

private theorem centered_shift {base : Nat} (r d : Nat) (e : WindowExpression base) :
    centeredExpression r (shift d e) = shift d (centeredExpression r e) :=
  recenter_mapOffsets _ (fun offset => offset+d) e

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0<base)

/-- Unequal padding remains invisible after the actual spatial regulator
recedes. Both sides retain their own explicit row and diagonal moduli. -/
theorem spatialLimit_padding (H H' left right : Nat)
    (hlen : 2*H' = 2*H+left+right) (e : WindowExpression base) (he : Within (2*H) e) :
    Equiv (spatialLimit hw0 hw1 H' (shift left e)
      (within_mono (by omega : 2*H+left ≤ 2*H') _ (shift_within (2*H) left e he))
      hsmall hd hs hb)
      (spatialLimit hw0 hw1 H e he hsmall hd hs hb) := by
  apply Equiv_of_limit_of_equal
    (hA := jointLimits_spatial_converge hw0 hw1 H' (shift left e)
      (within_mono (by omega : 2*H+left ≤ 2*H') _ (shift_within (2*H) left e he))
      hsmall hd hs hb)
    (hB := jointLimits_spatial_converge hw0 hw1 H e he hsmall hd hs hb)
  intro r
  have h := originalJoint_padding hw0 hw1 (2*H) left right (centeredExpression r e)
    ((centered_within r (2*H) e).mpr he)
  simpa only [← hlen, centered_shift] using h

/-- Original discrete time stationarity, with a literal finite support
guard. The reflection/window center and the physical spatial chart stay
fixed; only the entire signed observable expression is shifted. -/
theorem spatialLimit_shift_within (H L d : Nat) (e : WindowExpression base)
    (he : Within L e) (hfit : L+d ≤ 2*H) :
    Equiv (spatialLimit hw0 hw1 H (shift d e)
      (within_mono hfit _ (shift_within L d e he)) hsmall hd hs hb)
      (spatialLimit hw0 hw1 H e (within_mono (by omega : L ≤ 2*H) e he)
        hsmall hd hs hb) := by
  apply Equiv_of_limit_of_equal
    (hA := jointLimits_spatial_converge hw0 hw1 H (shift d e)
      (within_mono hfit _ (shift_within L d e he)) hsmall hd hs hb)
    (hB := jointLimits_spatial_converge hw0 hw1 H e
      (within_mono (by omega : L ≤ 2*H) e he) hsmall hd hs hb)
  intro r
  have h := originalJoint_shift_within_window hw0 hw1 L (2*H) d (centeredExpression r e)
    ((centered_within r L e).mpr he) hfit
  simpa only [centered_shift] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity.originalWindow_rectangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity.originalJoint_padding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity.originalJoint_shift_within_window
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity.spatialLimit_padding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity.spatialLimit_shift_within
