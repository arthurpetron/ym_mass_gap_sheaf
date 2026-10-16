/-
# Bounded expectation bridge from the selected window to the full slab

The fixed-width ORIGINAL vector-jet pair is placed on the common `2^66`
one-source normalization, hence on the squared scale for a two-source pair.
Its difference from the centered full-slab identity-scaled pure response is
retained as a named law-and-centering defect.  The defect has an explicit
finite bound: the selected-window vector diagonal budget plus direct
full-slab numerator/partition bounds.

This does not identify the two action measures, prove the defect small, pay a
strict margin, remove a cutoff, construct a continuum Hamiltonian, or prove a
mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSourceBridge
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainderGeometric

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSourceBridge
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.OSReconstructionProgress (q_cancel_left)
open YMGap.Continuum.QuaternionHaarCharacterInterval
  (heatRatio heatRemainderBound)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- The actual selected-window pair of the vector jet centered at its finite
OWN mean. -/
def originalBulkVectorQuadraticJetWindowPair
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  let jet := originalBulkVectorQuadraticJetOwnShifted
    hw0 hw1 s hs stage n
  laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n L jet jet

/-- The selected-window pair on the common pair normalization
`(2^66)^2`. -/
def originalBulkVectorQuadraticJetScaledWindowPair
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  let scale := globalCayleyVectorJetNorthWeightScale
  (scale * scale) *
    originalBulkVectorQuadraticJetWindowPair hw0 hw1 s hs stage n L

/-- The SAME-ORIGINAL selected-window pair is bounded by the existing vector
diagonal geometric budget. -/
theorem originalBulkVectorQuadraticJetWindowPair_abs_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    Q'.abs
        (originalBulkVectorQuadraticJetWindowPair
          hw0 hw1 s hs stage n L) ≤
      originalBulkVectorQuadraticJetDiagonalGeometricBudget
        hw0 hw1 hd hsRate s hs n := by
  let jet := originalBulkVectorQuadraticJetOwnShifted
    hw0 hw1 s hs stage n
  let pair := laggedWindowPair hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
    n L jet jet
  let budget := originalBulkVectorQuadraticJetDiagonalGeometricBudget
    hw0 hw1 hd hsRate s hs n
  have hYoung := laggedWindowPair_two_abs_le_diagonal_sum
    hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
    n L jet jet
    (originalBulkVectorQuadraticJetOwnShifted_supported
      hw0 hw1 s hs stage n)
    (originalBulkVectorQuadraticJetOwnShifted_supported
      hw0 hw1 s hs stage n)
  change 2 * Q'.abs pair ≤
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul jet jet) +
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (liftBoundary (L * N (s * s)) jet)
          (liftBoundary (L * N (s * s)) jet)) at hYoung
  have hleft := originalBulkVectorQuadraticJet_leftDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  have hright := originalBulkVectorQuadraticJet_rightDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (polyMul jet jet) ≤ budget at hleft
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul (liftBoundary (L * N (s * s)) jet)
        (liftBoundary (L * N (s * s)) jet)) ≤ budget at hright
  have hsum : 2 * Q'.abs pair ≤ budget + budget :=
    Q'.le_trans' _ _ _ hYoung (Q'.add_le_add hleft hright)
  have hregroup : budget + budget ≈ 2 * budget :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
      (by decide) (fun _ => budget)
  have htwice : 2 * Q'.abs pair ≤ 2 * budget :=
    Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hregroup)
  change Q'.abs pair ≤ budget
  exact q_cancel_left (c := (2 : Q')) (by decide) htwice

/-- Explicit selected-window contribution to the law-bridge defect after the
common pair scaling. -/
def originalBulkVectorQuadraticJetScaledWindowPairAbsBound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) : Q' :=
  let scale := globalCayleyVectorJetNorthWeightScale
  (scale * scale) *
    originalBulkVectorQuadraticJetDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n

theorem originalBulkVectorQuadraticJetScaledWindowPair_abs_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    Q'.abs
        (originalBulkVectorQuadraticJetScaledWindowPair
          hw0 hw1 s hs stage n L) ≤
      originalBulkVectorQuadraticJetScaledWindowPairAbsBound
        hw0 hw1 hd hsRate s hs n := by
  let scaleSquare := globalCayleyVectorJetNorthWeightScale *
    globalCayleyVectorJetNorthWeightScale
  let pair := originalBulkVectorQuadraticJetWindowPair
    hw0 hw1 s hs stage n L
  let budget := originalBulkVectorQuadraticJetDiagonalGeometricBudget
    hw0 hw1 hd hsRate s hs n
  have hpair := originalBulkVectorQuadraticJetWindowPair_abs_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change Q'.abs pair ≤ budget at hpair
  have hscale : (0 : Q') ≤ scaleSquare := by
    unfold scaleSquare globalCayleyVectorJetNorthWeightScale
    decide
  change Q'.abs (scaleSquare * pair) ≤ scaleSquare * budget
  exact Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le scaleSquare pair) (by
    rw [ExpNeg.abs_of_nonneg hscale]
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hpair hscale)

/-- Direct absolute bound for one full-slab identity-scaled pure expectation. -/
def globalCayleyVectorJetBulkIdentityScaledPureOriginalAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : Q' :=
  expectationAbsBound w hw0 hw1 half
    (globalCayleyVectorJetBulkIdentityScaledPureSource
      s hs (centralExtent half) time)

/-- Direct absolute bound for the full-slab pure pair expectation. -/
def globalCayleyVectorJetBulkPairIdentityScaledPureOriginalAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : Q' :=
  expectationAbsBound w hw0 hw1 half
    (globalCayleyVectorJetBulkPairIdentityScaledPureSource
      s hs (centralExtent half) leftTime rightTime)

/-- Direct absolute bound for the centered full-slab identity-scaled pure
response. -/
def globalCayleyVectorJetBulkCenteredIdentityScaledPureOriginalAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : Q' :=
  globalCayleyVectorJetBulkPairIdentityScaledPureOriginalAbsBound
      w hw0 hw1 half s hs leftTime rightTime +
    globalCayleyVectorJetBulkIdentityScaledPureOriginalAbsBound
        w hw0 hw1 half s hs leftTime *
      globalCayleyVectorJetBulkIdentityScaledPureOriginalAbsBound
        w hw0 hw1 half s hs rightTime

theorem globalCayleyVectorJetBulkCenteredIdentityScaledPureOriginalAbsBound_nonnegative
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    (0 : Q') ≤
      globalCayleyVectorJetBulkCenteredIdentityScaledPureOriginalAbsBound
        w hw0 hw1 half s hs leftTime rightTime := by
  exact Q'.zero_le_add _ _
    (expectationAbsBound_nonnegative w hw0 hw1 half _)
    (Q'.mul_nonneg _ _
      (expectationAbsBound_nonnegative w hw0 hw1 half _)
      (expectationAbsBound_nonnegative w hw0 hw1 half _))

private theorem abs_neg_le {value bound : Q'}
    (h : Q'.abs value ≤ bound) : Q'.abs (-value) ≤ bound :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' value)) h

private theorem abs_mul_le_of_bounds
    {left right leftBound rightBound : Q'}
    (hleft : Q'.abs left ≤ leftBound)
    (hright : Q'.abs right ≤ rightBound)
    (hleftBound : (0 : Q') ≤ leftBound) :
    Q'.abs (left * right) ≤ leftBound * rightBound :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le left right)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hleft (Q'.abs_nonneg right))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftBound))

/-- Every approximant of the centered full-slab pure response obeys the
direct numerator/partition bound. -/
theorem globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse_approx_abs_le
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime index : Nat) :
    Q'.abs
        ((globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
          w hw0 hw1 half s hs leftTime rightTime).approx index) ≤
      globalCayleyVectorJetBulkCenteredIdentityScaledPureOriginalAbsBound
        w hw0 hw1 half s hs leftTime rightTime := by
  let pairSource := globalCayleyVectorJetBulkPairIdentityScaledPureSource
    s hs (centralExtent half) leftTime rightTime
  let leftSource := globalCayleyVectorJetBulkIdentityScaledPureSource
    s hs (centralExtent half) leftTime
  let rightSource := globalCayleyVectorJetBulkIdentityScaledPureSource
    s hs (centralExtent half) rightTime
  let pair := (expectation w hw0 hw1 half pairSource).approx index
  let left := (expectation w hw0 hw1 half leftSource).approx index
  let right := (expectation w hw0 hw1 half rightSource).approx index
  let pairBound := expectationAbsBound w hw0 hw1 half pairSource
  let leftBound := expectationAbsBound w hw0 hw1 half leftSource
  let rightBound := expectationAbsBound w hw0 hw1 half rightSource
  have hpair := expectation_approx_abs_le
    w hw0 hw1 half pairSource index
  have hleft := expectation_approx_abs_le
    w hw0 hw1 half leftSource index
  have hright := expectation_approx_abs_le
    w hw0 hw1 half rightSource index
  have hproduct : Q'.abs (left * right) ≤ leftBound * rightBound :=
    abs_mul_le_of_bounds hleft hright
      (expectationAbsBound_nonnegative w hw0 hw1 half leftSource)
  change Q'.abs (pair + -(left * right)) ≤
    pairBound + leftBound * rightBound
  exact Q'.le_trans' _ _ _ (Q'.abs_add_le' pair (-(left * right)))
    (Q'.add_le_add hpair (abs_neg_le hproduct))

theorem globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse_abs_le
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.leEv
      (CReal.abs
        (globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
          w hw0 hw1 half s hs leftTime rightTime))
      (CReal.ofQ'
        (globalCayleyVectorJetBulkCenteredIdentityScaledPureOriginalAbsBound
          w hw0 hw1 half s hs leftTime rightTime)) :=
  CReal.leEv_le_ofQ'_of_approx_le
    (globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse_approx_abs_le
      w hw0 hw1 half s hs leftTime rightTime)

/-- Complete discrepancy between the squared-scale selected-window pair and
the centered full-slab response of the source identified in the source bridge.
It includes both the action-law and centering changes. -/
def globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (half s : Nat) (hs : 0 < s) (stage n L leftTime rightTime : Nat) : CReal :=
  CReal.sub
    (CReal.ofQ'
      (originalBulkVectorQuadraticJetScaledWindowPair
        hw0 hw1 s hs stage n L))
    (globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
      w hw0 hw1 half s hs leftTime rightTime)

/-- Exact expectation-level bridge.  No equality of laws is assumed: their
complete discrepancy is the named defect on the right. -/
theorem originalBulkVectorQuadraticJetScaledWindowPair_fullSlab_split
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (half s : Nat) (hs : 0 < s) (stage n L leftTime rightTime : Nat) :
    CReal.Equiv
      (CReal.ofQ'
        (originalBulkVectorQuadraticJetScaledWindowPair
          hw0 hw1 s hs stage n L))
      (CReal.add
        (globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect
          hw0 hw1 half s hs stage n L leftTime rightTime)) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro index
  exact poly_identity_of_normal_eq
    (.var 0)
    (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
    (by decide)
    (fun
      | 0 => originalBulkVectorQuadraticJetScaledWindowPair
          hw0 hw1 s hs stage n L
      | _ => (globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
          w hw0 hw1 half s hs leftTime rightTime).approx index)

/-- Explicit finite bound for the complete action-law and centering defect. -/
def globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefectAbsBound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (half s : Nat) (hs : 0 < s) (n leftTime rightTime : Nat) : Q' :=
  originalBulkVectorQuadraticJetScaledWindowPairAbsBound
      hw0 hw1 hd hsRate s hs n +
    globalCayleyVectorJetBulkCenteredIdentityScaledPureOriginalAbsBound
      w hw0 hw1 half s hs leftTime rightTime

theorem globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefectAbsBound_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (half s : Nat) (hs : 0 < s) (n leftTime rightTime : Nat) :
    (0 : Q') ≤
      globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefectAbsBound
        hw0 hw1 hd hsRate half s hs n leftTime rightTime := by
  apply Q'.zero_le_add
  · unfold originalBulkVectorQuadraticJetScaledWindowPairAbsBound
    exact Q'.mul_nonneg _ _ (by decide)
      (originalBulkVectorQuadraticJetDiagonalGeometricBudget_nonnegative
        hw0 hw1 hd hsRate s hs n)
  · exact
      globalCayleyVectorJetBulkCenteredIdentityScaledPureOriginalAbsBound_nonnegative
        w hw0 hw1 half s hs leftTime rightTime

/-- Every approximant of the complete window-to-full-slab defect obeys the
sum of its selected-window and full-slab bounds. -/
theorem globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect_approx_abs_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (half s : Nat) (hs : 0 < s)
    (stage n L leftTime rightTime index : Nat) :
    Q'.abs
        ((globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect
          hw0 hw1 half s hs stage n L leftTime rightTime).approx index) ≤
      globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefectAbsBound
        hw0 hw1 hd hsRate half s hs n leftTime rightTime := by
  let selected := originalBulkVectorQuadraticJetScaledWindowPair
    hw0 hw1 s hs stage n L
  let full := globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
    w hw0 hw1 half s hs leftTime rightTime
  let selectedBound := originalBulkVectorQuadraticJetScaledWindowPairAbsBound
    hw0 hw1 hd hsRate s hs n
  let fullBound :=
    globalCayleyVectorJetBulkCenteredIdentityScaledPureOriginalAbsBound
      w hw0 hw1 half s hs leftTime rightTime
  have hselected :=
    originalBulkVectorQuadraticJetScaledWindowPair_abs_geometric_le
      hw0 hw1 hsmall hd hsRate s hs stage n L
  change Q'.abs selected ≤ selectedBound at hselected
  have hfull :=
    globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse_approx_abs_le
      w hw0 hw1 half s hs leftTime rightTime index
  change Q'.abs (full.approx index) ≤ fullBound at hfull
  change Q'.abs (selected + -(full.approx index)) ≤
    selectedBound + fullBound
  exact Q'.le_trans' _ _ _ (Q'.abs_add_le' selected (-(full.approx index)))
    (Q'.add_le_add hselected (abs_neg_le hfull))

private theorem creal_abs_le_of_approx_abs_le
    (value : CReal) (bound : Q')
    (h : ∀ index, Q'.abs (value.approx index) ≤ bound) :
    CReal.leEv (CReal.abs value) (CReal.ofQ' bound) :=
  CReal.leEv_le_ofQ'_of_approx_le h

/-- Constructive-real absolute bound for the complete selected-window to
full-slab law-and-centering defect. -/
theorem globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect_abs_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (half s : Nat) (hs : 0 < s)
    (stage n L leftTime rightTime : Nat) :
    CReal.leEv
      (CReal.abs
        (globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect
          hw0 hw1 half s hs stage n L leftTime rightTime))
      (CReal.ofQ'
        (globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefectAbsBound
          hw0 hw1 hd hsRate half s hs n leftTime rightTime)) := by
  let defect := globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect
    hw0 hw1 half s hs stage n L leftTime rightTime
  let bound :=
    globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefectAbsBound
      hw0 hw1 hd hsRate half s hs n leftTime rightTime
  change CReal.leEv (CReal.abs defect) (CReal.ofQ' bound)
  apply creal_abs_le_of_approx_abs_le defect bound
  intro index
  have h :=
    globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect_approx_abs_le
      hw0 hw1 hsmall hd hsRate half s hs stage n L leftTime rightTime index
  change Q'.abs (defect.approx index) ≤ bound at h
  exact h

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound.originalBulkVectorQuadraticJetWindowPair_abs_geometric_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound.originalBulkVectorQuadraticJetScaledWindowPair_abs_geometric_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound.globalCayleyVectorJetBulkCenteredIdentityScaledPureOriginalAbsBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound.globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse_approx_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound.globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound.originalBulkVectorQuadraticJetScaledWindowPair_fullSlab_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound.globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefectAbsBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound.globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect_approx_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound.globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect_abs_le
