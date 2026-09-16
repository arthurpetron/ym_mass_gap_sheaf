/-
# Reflected positivity of the SAME selected fixed-spatial action

The actual symmetric chain face list supplies the selected lower/upper
reflection permutation. The action-dressing theorem therefore proves the
original reflected Haar numerator nonnegative, without an assumed positive
form or a replacement of the selected action by the full ambient action.
The existing positive reciprocal normalizes that very partition. Every
representative of its existing fixed-chain cutoff limit is nonnegative.

The nome range is 0<w<1 and finite prefixes use K>=headCutoff(w). The chain
is centered by start+depth=radius+1, with 2*depth transitions. Spatial
selection remains the original physically clipped chainIds list. Arbitrary
signed supported one-sided polynomials, not merely positive insertions, are
allowed. This is a finite-chain/fixed-chain-cutoff-limit result, not yet
reflected positivity of the constructed two-boundary time limit. Its literal
reflected-observable pin, physical OS quotient/transfer/vacuum, uniform
spatial/spacing control and the continuum Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection
import YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction
import YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflectionPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

/-- Actual symmetric selected-chain numerator, including its central weight once. -/
theorem originalChain_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K radius width start depth : Nat) (hcenter : start+depth=radius+1)
    (hK : headCutoff w ≤ K) (p : RatPoly) (hp : OneSided radius p)
    (hs : SupportedQuaternionBlocks (blockCount radius) p) :
    (0 : Q') ≤ quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p)
        (originalChainAction w K (adjacentEvenExtent radius) width start (2*depth))) :=
  selectedAction_nonnegative hw0 hw1 K radius hK (selectedIds radius width start depth)
    (fun _ hi => chainIds_physical hi) (selectedLower_reflection_perm hcenter) p hp hs

/-- Normalization uses the already constructed reciprocal of exactly these faces. -/
theorem originalChain_finiteValue_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (radius width start depth : Nat) (hcenter : start+depth=radius+1)
    (p : RatPoly) (hp : OneSided radius p)
    (hs : SupportedQuaternionBlocks (blockCount radius) p) (stage : Nat) :
    (0 : Q') ≤ finiteValue w hw0 hw1 (adjacentEvenExtent radius)
      (selectedIds radius width start depth) (fun _ hi => chainIds_physical hi)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p) stage := by
  apply Q'.mul_nonneg
  · exact originalChain_nonnegative hw0 hw1 (headCutoff w+stage) radius width start depth
      hcenter (Nat.le_add_right _ _) p hp hs
  · exact Q'.le_of_lt (PositiveRationalCauchyReciprocal.term_pos _ _ _ stage)

/-- Positivity survives the EXISTING explicit-modulus cutoff limit of the same action.
The chain is fixed here; no time/width/spacing limit is interchanged. -/
theorem originalChain_expectation_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (radius width start depth : Nat) (hcenter : start+depth=radius+1)
    (p : RatPoly) (hp : OneSided radius p)
    (hs : SupportedQuaternionBlocks (blockCount radius) p) :
    leEv (ofQ' 0) (expectation w hw0 hw1 (adjacentEvenExtent radius)
      (selectedIds radius width start depth) (fun _ hi => chainIds_physical hi)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p)) := by
  apply leEv_ofQ'_of_approx_ge
  intro n
  exact originalChain_finiteValue_nonnegative hw0 hw1 radius width start depth hcenter p hp hs _

end YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflectionPositive

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflectionPositive.originalChain_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflectionPositive.originalChain_finiteValue_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflectionPositive.originalChain_expectation_nonnegative
