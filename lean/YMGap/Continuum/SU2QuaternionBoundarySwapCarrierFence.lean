/-
# Boundary-swap carrier fence for literal quaternion polynomials

The physical two-boundary reflection exchanges the first and second blocks of
four quaternion coordinates.  The original dense-list helper
`swapBoundaryExponents` reconstructs an eight-entry list with `getD`, so it is
extensionally correct on evaluations but is not a strict unital map on the
literal list carrier: even the empty exponent list is padded by eight zeros.

`ReferenceTranslationAction` deliberately requires a strict unital
`ObsHom`.  Therefore the current helper cannot be installed there by treating
semantic equality as literal equality.  These finite counterexamples bank that
normalization fence before the corrected fixed-eight-coordinate carrier is
introduced.
-/

import YMGap.Continuum.SU2QuaternionHaarPolynomialPositivity
import YMGap.Continuum.ReferenceWeightTimeGeometry

namespace YMGap.Continuum.SU2QuaternionBoundarySwapCarrierFence

open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

/-- The dense-list boundary swap does not preserve the literal polynomial
unit required by `ObsHom.map_one`. -/
theorem theta_polyOne_ne_polyOne : theta polyOne ≠ polyOne := by
  decide

/-- Consequently the current dense-list swap is not even a literal
involution on the polynomial unit. -/
theorem theta_square_polyOne_ne_polyOne :
    theta (theta polyOne) ≠ polyOne := by
  decide

/-- No strict observable endomorphism can have the current `theta` as its map,
because the unitality field would contradict the explicit unit fence. -/
theorem no_strict_theta_obsHom :
    ¬ Nonempty { T : ObservableMeasure.ObsHom quaternionPairAlg quaternionPairAlg //
      T.map = theta } := by
  rintro ⟨T, hT⟩
  have hunit : theta polyOne = polyOne := by
    rw [← hT]
    exact T.map_one
  exact theta_polyOne_ne_polyOne hunit

end YMGap.Continuum.SU2QuaternionBoundarySwapCarrierFence

#print axioms YMGap.Continuum.SU2QuaternionBoundarySwapCarrierFence.theta_polyOne_ne_polyOne
#print axioms YMGap.Continuum.SU2QuaternionBoundarySwapCarrierFence.theta_square_polyOne_ne_polyOne
#print axioms YMGap.Continuum.SU2QuaternionBoundarySwapCarrierFence.no_strict_theta_obsHom
