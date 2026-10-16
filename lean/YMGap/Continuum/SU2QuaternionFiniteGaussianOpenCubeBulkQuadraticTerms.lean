/-
# Explicit weighted row terms of the finite open-cube bulk source

The two quadratic observables in the normalized-quartic response are the
literal `bulkSourceHeronRadialSquare` polynomials at their own history times.
This leaf exposes each one as the finite weighted list of squared color-curl
rows already present in its definition.  The rational face coefficient stays
outside the row square, matching the square-root-free source encoding.

This is an exact source-term pin only.  It does not expand the plaquette
quartic, form the connected cumulant, estimate it, compare the ORIGINAL law,
or establish a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
import YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource

/-- Number of independent three-color noise coordinates used by the actual
bulk source at the given finite history length. -/
def bulkSourceNoiseCount (timeBonds s : Nat) : Nat :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount (bulkSourceWidth s))
  coordinateCount + (coordinateCount + coordinateCount)

/-- Exact finite weighted quadratic row terms of one bulk-source observable. -/
def bulkSourceHeronQuadraticTerms
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) :
    List (Q' × RatPoly) :=
  (List.range (3 * (bulkSourceFaces s).length)).map fun rowIndex =>
    (bulkSourceIndexWeight s hs (rowIndex / 3),
      finiteGaussianRowSquare (bulkSourceNoiseCount timeBonds s)
        (bulkSourceHeronColorCurlRow
          timeBonds s stage time rowIndex))

/-- The term list reconstructs the literal weighted radial source polynomial
definitionally; no covariance or moment identity is used. -/
theorem bulkSourceHeronRadialSquare_eq_quadraticTerms
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) :
    bulkSourceHeronRadialSquare timeBonds s hs stage time =
      polySum ((bulkSourceHeronQuadraticTerms
        timeBonds s hs stage time).map fun term =>
          polySmul term.1 term.2) := by
  unfold bulkSourceHeronRadialSquare bulkSourceHeronQuadraticTerms
    bulkSourceNoiseCount
    combGaugeFreeHistoryHeronWeightedCurlRadialSquare
    finiteGaussianWeightedRadialSquare
  simp only [List.map_map]
  rfl

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms.bulkSourceHeronRadialSquare_eq_quadraticTerms
