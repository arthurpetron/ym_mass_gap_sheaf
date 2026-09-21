/-
# The intrinsic plaquette span is the literal Wilson lag source

For one physical spatial plaquette, chart the intrinsic face presentation at
its physical time radius.  The mixed reflected polynomial is exactly the
two-time fundamental Wilson source used by the all-nome moment argument.
This is only a finite coefficient identity: it changes neither the action nor
the partition, and asserts no positive-time lower bound or limiting survival.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
import YMGap.Continuum.BF4WilsonAllNomeMomentConvexity

namespace YMGap.Continuum.BF4WilsonPlaquetteSourcePin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (sourceProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe (windowProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection (mirrorSchedule)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (mixedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe
  (mirrorSpan_encodeChart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (encodeChart encodeSchedule radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit
  (unitSpan encodeChart_unit sourceSpan_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
  (advanceSchedule advanceSpan advanceSpan_zero radius_advance_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (facePresentation faceSpan faceSpan_radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
  (plaquetteLoop sourceCharacter_plaquette)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity (lagExpression)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem singleton_sum (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul 1 p) polyZero) p :=
  ((RatPolyCoeffEqv.one_smul p).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero p)

private theorem singleton_product (C : Z4Plaq → Nat → RatPoly) (p : Z4Plaq) :
    RatPolyCoeffEqv
      (BF4ExactSlabTemporalSweep.product C [(p, [(1, 1)])]) (C p 1) :=
  ((((RatPolyCoeffEqv.one_smul (C p 1)).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero (C p 1))).mul (RatPolyCoeffEqv.refl polyOne)).trans
      (RatPolyCoeffEqv.mul_one _)

private theorem singleton_window (width offset : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (windowProbe width [(offset, [(face, [(1, 1)])])])
      (liftBoundary (offset*(N width))
        (characterPolynomial (plaquette width face).scalar 1)) :=
  ((lift_coeff (offset*(N width))
    (singleton_product
      (fun p spin => characterPolynomial (plaquette width p).scalar spin) face)).mul
      (RatPolyCoeffEqv.refl polyOne)).trans (RatPolyCoeffEqv.mul_one _)

private theorem singleton_span (width offset : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (sourceSpan width [(1, [(offset, [(face, [(1, 1)])])])])
      (liftBoundary (offset*(N width))
        (characterPolynomial (plaquette width face).scalar 1)) :=
  (singleton_sum _).trans (singleton_window width offset face)

/-- Advancing the radius-zero face presentation by `n` stays within radius
`n`.  This is an upper bound; no assertion is made for arbitrary spans. -/
theorem face_time_radius (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (n : Nat) :
    radius (physicalTime n (faceSpan width face hf)).val ≤ n := by
  change radius (advanceSpan n (faceSpan width face hf).val) ≤ n
  have h := radius_advance_le n (faceSpan width face hf).val
  rw [faceSpan_radius, Nat.zero_add] at h
  exact h

/-- The mixed radius-zero chart polynomial for a plaquette against the unit
is the fixed Wilson singleton source.  This is the finite coefficient pin
used to identify the completed mean; it changes neither action nor partition. -/
theorem mixedProduct_mean (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    RatPolyCoeffEqv
      (mixedProduct width 0
        (encodeChart 0 (faceSpan width face hf).val)
        (encodeChart 0 unitSpan))
      (sourcePolynomial (.loop 0 (plaquetteLoop face hf) 1)) := by
  have hx : radius (faceSpan width face hf).val ≤ 0 := by
    rw [faceSpan_radius]
    exact Nat.le_refl 0
  rw [mixedProduct, mirrorSpan_encodeChart 0 (faceSpan width face hf).val hx,
    advanceSpan_zero, encodeChart_unit, sourceSpan_unit]
  change RatPolyCoeffEqv
    (polyMul (sourceSpan width (faceSpan width face hf).val) polyOne)
    (liftBoundary (0*(N width))
      (sourceCharacter width (plaquetteLoop face hf).edges 1))
  have hs := singleton_span width 0 face
  have hw := lift_coeff (0*(N width))
    (sourceCharacter_plaquette width face 1).symm
  exact ((hs.mul (RatPolyCoeffEqv.refl polyOne)).trans
    (RatPolyCoeffEqv.mul_one _)).trans hw

/-- The mixed intrinsic polynomial for a plaquette and its `n`-step physical
advance is the SAME finite two-time Wilson source used by `lagExpression`.
The statement is coefficient-sensitive and has no nome or positivity guard. -/
theorem mixedProduct_lag (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (n : Nat) :
    RatPolyCoeffEqv
      (mixedProduct width n
        (encodeChart n (faceSpan width face hf).val)
        (encodeChart n (physicalTime n (faceSpan width face hf)).val))
      (sourcePolynomial (lagExpression (plaquetteLoop face hf) n)) := by
  have hu : mirrorSpan n (encodeChart n (faceSpan width face hf).val) =
      [(1, [(n, [(face, [(1, 1)])])])] := by
    simp only [faceSpan, facePresentation, encodeChart, encodeSchedule, mirrorSpan,
      mirrorSchedule, List.map_cons, List.map_nil, Nat.sub_zero]
    rw [show 2*n-n=n by omega]
  have hl : encodeChart n (physicalTime n (faceSpan width face hf)).val =
      [(1, [(0, [(face, [(1, 1)])])])] := by
    simp only [physicalTime, faceSpan, facePresentation, advanceSpan, advanceSchedule,
      encodeChart, encodeSchedule, List.map_cons, List.map_nil, Nat.zero_add, Nat.sub_self]
  unfold mixedProduct
  rw [hu, hl]
  change RatPolyCoeffEqv
    (polyMul
      (sourceSpan width [(1, [(n, [(face, [(1, 1)])])])])
      (sourceSpan width [(1, [(0, [(face, [(1, 1)])])])]))
    (polyMul
      (liftBoundary (n*(N width))
        (sourceCharacter width (plaquetteLoop face hf).edges 1))
      (liftBoundary (0*(N width))
        (sourceCharacter width (plaquetteLoop face hf).edges 1)))
  have hsource := sourceCharacter_plaquette width face 1
  have hwilson (offset : Nat) : RatPolyCoeffEqv
      (liftBoundary (offset*(N width))
        (characterPolynomial (plaquette width face).scalar 1))
      (liftBoundary (offset*(N width))
        (sourceCharacter width (plaquetteLoop face hf).edges 1)) := by
    exact lift_coeff _ hsource.symm
  exact ((singleton_span width n face).mul (singleton_span width 0 face)).trans
    ((hwilson n).mul (hwilson 0))

#print axioms face_time_radius
#print axioms mixedProduct_mean
#print axioms mixedProduct_lag

end YMGap.Continuum.BF4WilsonPlaquetteSourcePin
