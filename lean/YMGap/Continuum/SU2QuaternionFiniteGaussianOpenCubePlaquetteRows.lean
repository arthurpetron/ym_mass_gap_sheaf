/-
# Actual finite open-cube plaquette rows for the normalized Cayley quartic

This leaf selects the four literal links of one internal open-cube plaquette
in the existing rooted comb gauge.  A physical history row extracts that link
coordinate at one time (and is zero on a comb-tree link), the certified Heron
factor pulls it back to independent rational Gaussian noise, and
`threeColorRows` supplies the three SU(2) color components.  The inverse-word
slots C and D are negated, giving the exact directed order `a,b,-c,-d` used by
the original Cayley source theorem.

The final theorem specializes the checked denominator-normalized quartic
expectation to these SAME four rows.  It does not prove a sign, sum over bulk
faces, control the higher remainder, identify the original interacting law or
establish a physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquettePathGram
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
import YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation

local infix:50 " ≈ " => Q'.eqv

/-- Physical-history coefficient row extracting one rooted-comb-gauge link at
one time.  Links on the comb tree have no gauge coordinate and therefore give
the zero row. -/
def combGaugeFreeHistoryLinkRow
    (width time : Nat) (link : Z4Link) (coordinate : Nat) : Q' :=
  if link ∈ combGaugeLinks width then
    if coordinate = historyIndex (combGaugeEdgeCount width) time
        ((combGaugeLinks width).idxOf link) then 1 else 0
  else 0

/-- Three-color Heron-pulled row of one directed gauge-fixed link. -/
def combGaugeFreeHistoryHeronDirectedLinkRows
    (timeBonds width stage time : Nat) (sign : Q') (link : Z4Link)
    (component coordinate : Nat) : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  sign *
    threeColorRows coordinateCount
      (pulledRow coordinateCount
        (combGaugeFreeHistoryHeronTransform timeBonds width stage)
        (combGaugeFreeHistoryLinkRow width time link))
      component coordinate

/-- The four actual directed plaquette row triples in original word order.
Slots C and D carry the inverse-link sign. -/
def combGaugeFreeHistoryHeronDirectedPlaquetteRows
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    Nat → Nat → Nat → Q'
  | 0 => combGaugeFreeHistoryHeronDirectedLinkRows
      timeBonds width stage time 1 (faceLinkA face)
  | 1 => combGaugeFreeHistoryHeronDirectedLinkRows
      timeBonds width stage time 1 (faceLinkB face)
  | 2 => combGaugeFreeHistoryHeronDirectedLinkRows
      timeBonds width stage time (-1) (faceLinkC face)
  | _ => combGaugeFreeHistoryHeronDirectedLinkRows
      timeBonds width stage time (-1) (faceLinkD face)

def combGaugePlaquetteNoiseCount (timeBonds width : Nat) : Nat :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  coordinateCount + (coordinateCount + coordinateCount)

/-- Literal normalized Cayley quartic polynomial for one actual finite
open-cube plaquette under the staged Heron reference. -/
def combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
    (timeBonds width stage time : Nat) (face : Z4Plaq) : RatPoly :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianNormalizedCayleyH4Polynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Exact Gram expression for the same actual plaquette-row expectation. -/
def combGaugeFreeHistoryPlaquetteNormalizedH4GramExpectation
    (timeBonds width stage time : Nat) (face : Z4Plaq) : Q' :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianNormalizedCayleyH4GramExpectation
    (combGaugePlaquetteNoiseCount timeBonds width)
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- The normalized quartic expectation specialized to the four literal links
of an actual internal open-cube plaquette at an in-range history time. -/
theorem finiteProductGaussian_openCubePlaquette_normalized_cayleyH4
    (timeBonds width stage time : Nat) (face : Z4Plaq)
    (_hface : face ∈ internalOpenCubeFaces width)
    (_htime : time ≤ timeBonds) :
    finiteProductGaussian (combGaugePlaquetteNoiseCount timeBonds width)
        (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
          timeBonds width stage time face) ≈
      combGaugeFreeHistoryPlaquetteNormalizedH4GramExpectation
        timeBonds width stage time face := by
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  exact finiteProductGaussian_normalized_cayleyH4
    (combGaugePlaquetteNoiseCount timeBonds width)
    (rows 0) (rows 1) (rows 2) (rows 3)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows.finiteProductGaussian_openCubePlaquette_normalized_cayleyH4
