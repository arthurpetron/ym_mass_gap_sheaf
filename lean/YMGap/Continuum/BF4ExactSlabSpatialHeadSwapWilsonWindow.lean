/-
# Actual signed Wilson windows under the finite spatial head swap

The complete ordered source loops are transported geometrically; their edge
order, inverse flags, time offsets, spins and signed operations are retained.
The SAME chronological action and reciprocal normalize the resulting finite
window scalar. No replacement cylinder law, width map or continuum rotation
is used. This supplies the finite input to reflected-form invariance, not a
scaling-family bound or continuum QFT covariance.
-/

import YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop
import YMGap.Continuum.BF4ExactSlabSpatialHeadSwapAction
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit

namespace YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.BF4ExactSlabSpatialHeadSwapHaar
open YMGap.Continuum.BF4ExactSlabSpatialHeadSwapAction
open YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (haar_of_coeff_eqv)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation "B" extent => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

/-- Only spatial coordinates change; every signed syntactic operation remains. -/
def swapExpression {width : Nat} : WindowExpression width → WindowExpression width
  | .one => .one
  | .loop offset value spin => .loop offset (swapSourceLoop value) spin
  | .add e f => .add (swapExpression e) (swapExpression f)
  | .mul e f => .mul (swapExpression e) (swapExpression f)
  | .smul c e => .smul c (swapExpression e)

theorem within_swap {width L : Nat} : ∀ e : WindowExpression width,
    Within L (swapExpression e) ↔ Within L e
  | .one => Iff.rfl
  | .loop _ _ _ => Iff.rfl
  | .add e f => and_congr (within_swap e) (within_swap f)
  | .mul e f => and_congr (within_swap e) (within_swap f)
  | .smul _ e => within_swap e

/-- Spatial transport commutes with all time-offset recodings, including mirror. -/
theorem swap_mapOffsets {width : Nat} (f : Nat → Nat) : ∀ e : WindowExpression width,
    swapExpression (mapOffsets f e) = mapOffsets f (swapExpression e)
  | .one => rfl
  | .loop _ _ _ => rfl
  | .add e g => by
      change WindowExpression.add (swapExpression (mapOffsets f e))
        (swapExpression (mapOffsets f g)) =
        WindowExpression.add (mapOffsets f (swapExpression e)) (mapOffsets f (swapExpression g))
      rw [swap_mapOffsets f e, swap_mapOffsets f g]
  | .mul e g => by
      change WindowExpression.mul (swapExpression (mapOffsets f e))
        (swapExpression (mapOffsets f g)) =
        WindowExpression.mul (mapOffsets f (swapExpression e)) (mapOffsets f (swapExpression g))
      rw [swap_mapOffsets f e, swap_mapOffsets f g]
  | .smul c e => congrArg (WindowExpression.smul c) (swap_mapOffsets f e)

theorem swap_mirror {width : Nat} (h : Nat) (e : WindowExpression width) :
    swapExpression (mirror h e) = mirror h (swapExpression e) :=
  swap_mapOffsets _ e

private theorem swapped_placed_edges (time : Nat) (edges : List OrientedBF4Link) :
    (edges.map (shiftEntry time)).map swapEntry =
      (edges.map swapEntry).map (shiftEntry time) := by
  simp only [List.map_map, Function.comp_def, swapEntry_shift_commute]

/-- Literal original slab insertion; arbitrary ordered words, not products of traces. -/
theorem placedPolynomial_swap {width : Nat} (extent start : Nat) :
    ∀ e : WindowExpression width,
    PaddedPolynomialCoeffEqv (B extent)
      (swapPolynomial extent (placedPolynomial extent start e))
      (placedPolynomial extent start (swapExpression e))
  | .one => .of_prefix (swapPolynomial_one_prefix extent)
  | .loop offset value spin => by
      change PaddedPolynomialCoeffEqv (B extent)
        (swapPolynomial extent (BF4ExactSlabTemporalGaugeWilsonWord.character extent
          (value.edges.map (shiftEntry (start+offset))) spin))
        (BF4ExactSlabTemporalGaugeWilsonWord.character extent
          ((value.edges.map swapEntry).map (shiftEntry (start+offset))) spin)
      rw [← swapped_placed_edges]
      exact character_swap extent _ spin
  | .add e f => by
      change PaddedPolynomialCoeffEqv (B extent)
        (swapPolynomial extent (polyAdd _ _)) (polyAdd _ _)
      rw [swapPolynomial, reindexQuaternionPolynomial_add]
      exact (placedPolynomial_swap extent start e).add (placedPolynomial_swap extent start f)
  | .mul e f => by
      change PaddedPolynomialCoeffEqv (B extent)
        (swapPolynomial extent (polyMul _ _)) (polyMul _ _)
      rw [swapPolynomial, reindexQuaternionPolynomial_mul]
      exact (placedPolynomial_swap extent start e).mul (placedPolynomial_swap extent start f)
  | .smul c e => by
      change PaddedPolynomialCoeffEqv (B extent)
        (swapPolynomial extent (polySmul c _)) (polySmul c _)
      rw [swapPolynomial, reindexQuaternionPolynomial_smul]
      exact (placedPolynomial_swap extent start e).smul c

/-- Every original chronological heat factor and the terminal slice remain. -/
theorem original_window_numerator_swap {width : Nat} (w : Q')
    (K extent start steps placement : Nat)
    (hw : width ≤ extent+1) (ht : start+steps ≤ extent)
    (e : WindowExpression width) :
    numerator w (B extent) extent (chainIds extent width start steps)
        (placedPolynomial extent placement (swapExpression e)) K ≈
      numerator w (B extent) extent (chainIds extent width start steps)
        (placedPolynomial extent placement e) K := by
  let action := originalChainAction w K extent width start steps
  let p := placedPolynomial extent placement e
  let q := placedPolynomial extent placement (swapExpression e)
  have ha := originalChainAction_support w K extent width start steps
  have hpin := ((PaddedPolynomialCoeffEqv.refl (B extent) action).mul
    (placedPolynomial_swap extent placement e)).haar
    (supported_polyMul ha (swapPolynomial_supported extent p))
    (supported_polyMul ha (placed_supported extent placement (swapExpression e)))
  have hinvariant := originalChainAction_weighted_haar_swap w K extent width start steps
    hw ht p (placed_supported extent placement e)
  change quaternionHaar (B extent) (polyMul q action) ≈
    quaternionHaar (B extent) (polyMul p action)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv (B extent) (RatPolyCoeffEqv.mul_comm q action))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hpin)
      (Q'.eqv_trans _ _ _ hinvariant
        (haar_of_coeff_eqv (B extent) (RatPolyCoeffEqv.mul_comm action p))))

/-- SAME finite normalized original-window value; the reciprocal is unchanged. -/
theorem originalWindowScalar_swap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (stage m n : Nat) :
    originalWindowScalar hw0 hw1 L (swapExpression e) stage m n ≈
      originalWindowScalar hw0 hw1 L e stage m n := by
  unfold originalWindowScalar finiteValue
  exact Q'.mul_eqv_congr_right _ _ _
    (original_window_numerator_swap w _ (width+(m+(L+n))) 0 (m+(L+n)) m
      (by omega) (by omega) e)

end YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonWindow

#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonWindow.swapExpression
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonWindow.within_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonWindow.swap_mapOffsets
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonWindow.swap_mirror
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonWindow.placedPolynomial_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonWindow.original_window_numerator_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonWindow.originalWindowScalar_swap
