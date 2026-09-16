/-
# A positive retained original tube head still carries correlation

At the explicit cutoff max 1 (headCutoff w), every heat factor of the
original twelve-face tube has a square certificate. Their product retains
all shared links, all cutoff spins, and the original ordered tubeIds.
For the unchanged lower/reflected-upper response probes its connected
numerator is exactly w^36, hence strictly positive for 0<w<1.

Thus this retained interacting head cannot be assigned a zero connected
baseline merely because no additional tail factor is present. No tail
expansion is defined here. This evaluates only the named tube sub-action,
not the full slab, and proves neither decay nor a spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue
import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison

namespace YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- One computable cutoff meets both the heat-head and spin-one requirements. -/
def cutoff (w : Q') : Nat := max 1 (headCutoff w)

theorem cutoff_ge_one (w : Q') : 1 ≤ cutoff w := Nat.le_max_left _ _

theorem headCutoff_le_cutoff (w : Q') : headCutoff w ≤ cutoff w := Nat.le_max_right _ _

/-- The original ordered tube product; no tube factor is removed or replaced. -/
def headPolynomial (w : Q') (margin : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w (cutoff w) (responseExtent margin)) (tubeIds margin)

/-- A constructed positive certificate on the original full link carrier. -/
def headCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (margin : Nat) :
    Certificate (List.length (boundaryCompleteSlabLinks (responseExtent margin))) (headPolynomial w margin) :=
  headProduct_certificate hw0 hw1 (cutoff w) (responseExtent margin) (headCutoff_le_cutoff w)
    (tubeIds margin) (fun id hi => ((tubeIds_mem_iff margin id).mp hi).1)

/-- The same original action and probes, including both replica means. -/
def connectedHead (w : Q') (margin : Nat) : Q' :=
  BF4ExactSlabDisconnectedHaarCancellation.connectedNumerator
    w (cutoff w) (responseExtent margin) (tubeIds margin)
    (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe))

theorem connectedHead_eq (w : Q') (margin : Nat) :
    connectedHead w margin ≈ RingNormaliser.qpow w 36 :=
  original_tube_numerator w (cutoff w) margin (cutoff_ge_one w)

private theorem power_pos {w : Q'} (hw : (0 : Q') < w) :
    ∀ n, (0 : Q') < RingNormaliser.qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (power_pos hw n) hw

theorem connectedHead_pos {w : Q'} (hw0 : (0 : Q') < w) (margin : Nat) :
    (0 : Q') < connectedHead w margin :=
  Q'.pos_of_lt_of_le (power_pos hw0 36) (Q'.ge_of_eqv (connectedHead_eq w margin))

/-- In particular, the retained-head connected baseline cannot be set to zero. -/
theorem connectedHead_ne_zero {w : Q'} (hw0 : (0 : Q') < w) (margin : Nat) :
    ¬ connectedHead w margin ≈ 0 := by
  intro hz
  have hfalse : (0 : Q') < 0 :=
    Q'.pos_of_lt_of_le (connectedHead_pos hw0 margin) (Q'.le_of_eqv hz)
  exact (by decide : ¬ ((0 : Q') < 0)) hfalse

/-- These are the original response endpoints, separated by three time steps. -/
theorem original_endpoint_separation (margin : Nat) :
    (sliceFace margin 3).1.2.2.2 = (sliceFace margin 0).1.2.2.2 + 3 :=
  BF4ExactSlabShiftedProbeTubeGeometry.endpoint_separation margin

end YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation

#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation.cutoff
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation.cutoff_ge_one
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation.headCutoff_le_cutoff
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation.headPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation.headCertificate
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation.connectedHead
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation.connectedHead_eq
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation.connectedHead_pos
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation.connectedHead_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeadCorrelation.original_endpoint_separation
