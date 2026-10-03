/-
# The literal dyadic square has positive finite odd OWN variance

The selected-link word floor is transported through the original zero-window
placement to the chronological depths n+1,n.  Every original action factor,
the odd partition and its OWN mean are retained, including n=0.

This is a fixed-nome certificate floor, not a useful uniform relative-energy
or changing-family survival estimate.
-/

import YMGap.Continuum.BF4ExactSlabWilsonWordVariance
import YMGap.Continuum.BF4DyadicWilsonSquarePlacedGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard

namespace YMGap.Continuum.BF4DyadicWilsonSquareOddVarianceFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)
open YMGap.Continuum.BF4ExactSlabWilsonWordVariance
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquarePlacedGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)

local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] originalWindowScalar middleRatio baseLinks

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- Arbitrary left/right depths in the exact ambient original action.  The
regulator stage is independent of both depths. -/
theorem originalWindowScalar_rectangular_variance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width stage m n : Nat) (hwidth : side scale < width) :
    let loop := paddedSquare scale width hwidth
    let mean := originalWindowScalar hw0 hw1 0 (.loop 0 loop 1) stage m n
    starRatio w ≤
      originalWindowScalar hw0 hw1 0
        (.mul (.loop 0 loop 1) (.loop 0 loop 1)) stage m n + -(mean*mean) := by
  let extent := width + (m + (0 + n))
  let ids := chainIds extent width 0 (m + (0 + n))
  have hambient : width ≤ extent := by omega
  have htime : m ≤ extent := by omega
  have hfinite := finiteValue_variance_floor hw0 hw1 extent ids
    (fun _ hi => chainIds_physical hi)
    (chainIds_nodup extent width 0 (m + (0 + n)))
    (placedSelectedLink m)
    (placedSelectedLink_physical scale width extent hwidth hambient m htime)
    (placedDyadicTail scale m)
    (placedDyadicTail_physical scale width extent hwidth hambient m htime)
    (placedSelectedLink_not_mem_placedDyadicTail scale m) stage
  simpa only [originalWindowScalar, placedPolynomial, Nat.zero_add,
    Nat.add_zero, paddedSquare_placed_edges_split, placedSelectedEdge,
    extent, ids] using hfinite

private theorem odd_stage_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width stage depth : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    starRatio w ≤ oddVariance hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) depth f := by
  let loop := paddedSquare scale width hwidth
  let f := sourceCharacter width loop.edges 1
  have hf := sourceCharacter_supported width loop.edges 1
  have hm : originalWindowScalar hw0 hw1 0 (.loop 0 loop 1) stage (depth+1) depth ≈
      middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        (depth+1) depth f := by
    have hp := originalWindowScalar_pin hw0 hw1 0 (.loop 0 loop 1)
      (Nat.le_refl 0) stage (depth+1) depth
    have hp' : originalWindowScalar hw0 hw1 0 (.loop 0 loop 1) stage (depth+1) depth ≈
        windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
          (depth+1) 0 depth f := by
      simpa only [sourcePolynomial, Nat.zero_mul, liftBoundary] using hp
    exact Q'.eqv_trans _ _ _ hp'
      (windowRatio_zero hw0 hw1 _ width (Nat.le_add_right _ _) (depth+1) depth hf)
  have hs : originalWindowScalar hw0 hw1 0
      (.mul (.loop 0 loop 1) (.loop 0 loop 1)) stage (depth+1) depth ≈
      middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        (depth+1) depth (polyMul f f) := by
    have hp := originalWindowScalar_pin hw0 hw1 0
      (.mul (.loop 0 loop 1) (.loop 0 loop 1))
      ⟨Nat.le_refl 0, Nat.le_refl 0⟩ stage (depth+1) depth
    have hp' : originalWindowScalar hw0 hw1 0
        (.mul (.loop 0 loop 1) (.loop 0 loop 1)) stage (depth+1) depth ≈
        windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
          (depth+1) 0 depth (polyMul f f) := by
      simpa only [sourcePolynomial, Nat.zero_mul, liftBoundary] using hp
    exact Q'.eqv_trans _ _ _ hp'
      (windowRatio_zero hw0 hw1 _ width (Nat.le_add_right _ _) (depth+1) depth
        (supported_polyMul hf hf))
  have hfloor := originalWindowScalar_rectangular_variance_floor
    hw0 hw1 scale width stage (depth+1) depth hwidth
  have he := Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _ (qmul hm hm))
  exact Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv he)

/-- The SAME original odd-chain OWN variance, for every late cutoff and
every depth including zero.  There is no terminal-square substitution. -/
theorem paddedSquare_oddVariance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    starRatio w ≤ oddVariance hw0 hw1 K width hK depth f := by
  have h := odd_stage_floor hw0 hw1 scale width (K-headCutoff w) depth hwidth
  simpa only [Nat.add_sub_of_le hK] using h

end YMGap.Continuum.BF4DyadicWilsonSquareOddVarianceFloor

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareOddVarianceFloor.originalWindowScalar_rectangular_variance_floor
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareOddVarianceFloor.paddedSquare_oddVariance_floor
