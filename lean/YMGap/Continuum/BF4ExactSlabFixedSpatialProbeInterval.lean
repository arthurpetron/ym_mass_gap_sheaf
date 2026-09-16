/-
# Explicit intervals for the actual signed spatial probes

Each signed character term has a computed square cap, hence a two-sided
polynomial certificate. Finite sums within a face and products across faces
then bound the SAME sourceProbe, preserving repeated faces, signed rational
coefficients and shared link variables.

The deliberately coarse cap depends only on the supplied spins, coefficients
and factor lists, not on width, nome or heat cutoff. The source construction's
identity fallback makes this algebraic statement valid for every face list;
the existing sourceProbe_pin still needs its physical face-membership and
placement guards. This supplies an initial cone bracket against polyOne,
not a stationary law, operator estimate or OS claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported plaquette_unit)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)

/-- A rational signed coefficient enters through its square, not its sign.
The extra one is the existing square-root-free linear-bound budget. -/
def termCap (term : Nat × Q') : Q' :=
  (term.2 * term.2) * characterBound term.1 + 1

/-- Sum of the explicit term caps in one signed face factor. -/
def factorCap : List (Nat × Q') → Q'
  | [] => 0
  | term::terms => termCap term + factorCap terms

/-- Product of the face-factor caps in the original probe list order.
An empty probe is one; an empty signed face factor has cap zero. -/
def probeCap : List FaceFactor → Q'
  | [] => 1
  | f::fs => factorCap f.2 * probeCap fs

private def termInterval (width : Nat) (face : Z4Plaq) (term : Nat × Q') :
    Interval (N width)
      (polySmul term.2 (characterPolynomial (plaquette width face).scalar term.1))
      (termCap term) :=
  Interval.ofSquare
    ((character_squareBound
      (SquareBound.scalar
        (plaquette_supported width (N width) (Nat.le_refl _) face)
        (plaquette_unit width (N width) (Nat.le_refl _) face)) term.1).smul term.2)

private def factorInterval (width : Nat) (face : Z4Plaq) :
    (terms : List (Nat × Q')) → Interval (N width)
      (finitePolySum (fun term =>
        polySmul term.2 (characterPolynomial (plaquette width face).scalar term.1)) terms)
      (factorCap terms)
  | [] => Interval.zero (N width)
  | term::terms => (termInterval width face term).add (factorInterval width face terms)

/-- Inhabited two-sided certificate for the actual signed source probe.
No positivity of the probe, disjointness of faces, or analytic bound is assumed. -/
def sourceProbe_interval (width : Nat) :
    (fs : List FaceFactor) → Interval (N width) (sourceProbe width fs) (probeCap fs)
  | [] => Interval.one (N width)
  | f::fs => (factorInterval width f.1 f.2).mul (sourceProbe_interval width fs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval.termCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval.factorCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval.probeCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval.sourceProbe_interval
