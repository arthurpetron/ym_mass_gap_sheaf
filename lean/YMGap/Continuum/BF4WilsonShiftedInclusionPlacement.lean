/-
# Placement and centered inclusion syntax for original Wilson windows

These are finite, literal identities: shifting every temporal offset moves
the placement start, while zero spatial inclusion followed by recentering
agrees with one direct recentering into the larger centered chart.  No action,
Haar law, limit, or analytic estimate is introduced.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison

namespace YMGap.Continuum.BF4WilsonShiftedInclusionPlacement

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (centeredExpression chartInsertion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyAdd polyMul polySmul)

theorem placed_shift {base : Nat} (extent start K : Nat)
    (e : WindowExpression base) :
    placedPolynomial extent start (shift K e) =
      placedPolynomial extent (start+K) e := by
  induction e with
  | one => rfl
  | loop offset value spin =>
      simp only [shift, mapOffsets, placedPolynomial,
        show start+(offset+K)=start+K+offset by omega]
  | add e f ihe ihf =>
      change polyAdd (placedPolynomial extent start (shift K e))
          (placedPolynomial extent start (shift K f)) =
        polyAdd (placedPolynomial extent (start+K) e)
          (placedPolynomial extent (start+K) f)
      rw [ihe, ihf]
  | mul e f ihe ihf =>
      change polyMul (placedPolynomial extent start (shift K e))
          (placedPolynomial extent start (shift K f)) =
        polyMul (placedPolynomial extent (start+K) e)
          (placedPolynomial extent (start+K) f)
      rw [ihe, ihf]
  | smul c e ihe =>
      change polySmul c (placedPolynomial extent start (shift K e)) =
        polySmul c (placedPolynomial extent (start+K) e)
      rw [ihe]

theorem centered_include {base larger : Nat} (hb : base ≤ larger) (r : Nat)
    (e : WindowExpression base) :
    centeredExpression r (includeExpression hb e) =
      recenterExpression (space := r+1)
        (by unfold paddedWidth; omega : base+(r+1) ≤ paddedWidth larger r) e := by
  unfold centeredExpression includeExpression
  have h := recenterExpression_comp
    (width := base) (middle := larger)
    (targetWidth := paddedWidth larger r)
    (first := 0) (second := r+1)
    (by simpa only [Nat.add_zero] using hb)
    (by unfold paddedWidth; omega) e
  simpa only [Nat.add_zero, Nat.zero_add] using h

theorem chartInsertion_shifted_include {base larger : Nat} (hb : base ≤ larger)
    (r R t K : Nat) (e : WindowExpression base) :
    chartInsertion r R t (shift K (includeExpression hb e)) =
      placedPolynomial (chartExtent larger r R t) (paddedWidth larger r+1+t+K)
        (recenterExpression (space := r+1)
          (by unfold paddedWidth; omega : base+(r+1) ≤ paddedWidth larger r) e) := by
  have hc : centeredExpression r (shift K (includeExpression hb e)) =
      shift K (centeredExpression r (includeExpression hb e)) :=
    recenter_mapOffsets _ (fun offset => offset+K) (includeExpression hb e)
  unfold chartInsertion
  rw [hc, placed_shift, centered_include]

#print axioms YMGap.Continuum.BF4WilsonShiftedInclusionPlacement.placed_shift
#print axioms YMGap.Continuum.BF4WilsonShiftedInclusionPlacement.centered_include
#print axioms YMGap.Continuum.BF4WilsonShiftedInclusionPlacement.chartInsertion_shifted_include

end YMGap.Continuum.BF4WilsonShiftedInclusionPlacement
