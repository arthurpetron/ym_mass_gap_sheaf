/-
# Finite-state covariance fence for strict reflected time translation

The exact affine time-shift covariance remainder applies to an ordinary
unconditional cylinder whose whole root list is translated by one common
time shift.  A radius-indexed strict reflection quadratic has a different
finite presentation.  Its local joint-kernel entries are corrected-slab
conditional cylinder probabilities, and increasing the reflection radius
together with positive-time translation moves the reflected lower query by a
pure spatial shift.

This file records both facts at the precise finite types.  It expands the
translated radius-indexed quadratic into its local joint law, identifies each
entry with its literal corrected-slab cylinder, and machine-fences the naive
identification of the spatial lower-query transport with affine time
translation.  Hence the unconditional boundary-remainder theorem cannot be
silently substituted for the missing half-space compression comparison.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslationAction
import YMGap.Continuum.Z4TimeShiftedFiniteNormalizedCovarianceRemainder

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointFiniteCovarianceFence

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteJointKernelPushforward
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslationAction
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The translated finite quadratic is a corrected-slab joint law -/

/-- Exact expansion of the radius-indexed translated reflection quadratic
through the finite local support-pair law. -/
theorem strictJointCylinderRadiusTimeTranslatedReflectionQuadratic_eqv_localLaw
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (vector : StrictJointCylinderVector base) :
    strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
        coupling hcoupling cutoff radius shift vector ≈
      finiteJointQuadratic
        (centralLocalSupportFingerprintSpace (radius + shift)
          (centralStrictLocalQueryCode (radius + shift) (base + shift)
            (timeTranslateStrictJointCylinderVector shift vector).roots))
        (timeTranslateStrictJointCylinderVector shift vector).coefficient
        (centralNormalizedLocalSupportPairLaw
          coupling hcoupling cutoff (radius + shift)
          (centralStrictLocalQueryCode (radius + shift) (base + shift)
            (timeTranslateStrictJointCylinderVector shift vector).roots)) := by
  unfold strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
    strictJointCylinderRadiusReflectionQuadratic
    strictJointCylinderRadiusCoefficient
  exact centralNormalizedSupportReflectionQuadratic_eq_localJointLaw
    coupling hcoupling cutoff (radius + shift)
    (centralStrictLocalQueryCode (radius + shift) (base + shift)
      (timeTranslateStrictJointCylinderVector shift vector).roots)
    (timeTranslateStrictJointCylinderVector shift vector).coefficient

/-- Every matrix entry of the translated local joint law is literally a
corrected-slab conditional marked-cylinder probability. -/
theorem timeTranslatedStrictJointLocalGramEntry_eqv_correctedSlabCylinder
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) :
    centralNormalizedLocalSupportPairLaw
        coupling hcoupling cutoff (radius + shift)
        (centralStrictLocalQueryCode (radius + shift) (base + shift)
          (timeTranslateStrictJointCylinderVector shift vector).roots)
        left right ≈
      couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling cutoff (centralExtent (radius + shift))
        (slabMarkedCylinderEvent
          (centralStrictJointCanonicalAtoms
            (radius + shift) (base + shift)
            (timeTranslateStrictJointCylinderVector shift vector).roots
            (strictQueryBase_le_after_timeTranslate hbase shift)
            (timeTranslateStrictJointCylinderVector shift vector).rootsCanonical)
          (centralStrictJointPairPredicate
            (timeTranslateStrictJointCylinderVector shift vector).roots.length
            left right)) := by
  exact centralNormalizedLocalSupportPairLaw_eq_strictMarkedCylinder
    coupling hcoupling cutoff
    (strictQueryBase_le_after_timeTranslate hbase shift)
    (timeTranslateStrictJointCylinderVector shift vector).rootsCanonical
    left right

/-! ## 2. The geometric map is not affine time translation -/

/-- A nonzero pure spatial shift and the affine Euclidean-time shift disagree
on every plaquette, already at the first spatial coordinate. -/
theorem spatialShiftPlaquette_ne_timeShiftPlaquette
    {shift : Nat} (hshift : 0 < shift) (plaquette : Z4Plaq) :
    spatialShiftPlaquette shift plaquette ≠
      timeShiftPlaquette shift plaquette := by
  intro hequal
  have hfirst := congrArg (fun target : Z4Plaq => target.1.1) hequal
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp only [spatialShiftPlaquette, spatialShiftVertex,
    timeShiftPlaquette, timeShiftVertex] at hfirst
  omega

/-- The actual radius-shifted lower strict query is transported by the pure
spatial map that is distinct from affine time translation for nonzero shift. -/
theorem timeTranslatedStrictLowerRoot_has_spatial_transport
    {radius base shift : Nat} (hbase : strictQueryBase base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient (radius + shift))
        (centralStrictLowerCanonicalRoot (radius + shift) (base + shift)
          (timeShiftCanonicalRoot shift base root)))
      ((geometricPolymer (centralAmbient radius)
          (centralStrictLowerCanonicalRoot radius base root)).map
        (spatialShiftPlaquette shift)) :=
  centralStrictLowerCanonicalRoot_timeShift_sameSupport hbase hroot

#print axioms strictJointCylinderRadiusTimeTranslatedReflectionQuadratic_eqv_localLaw
#print axioms timeTranslatedStrictJointLocalGramEntry_eqv_correctedSlabCylinder
#print axioms spatialShiftPlaquette_ne_timeShiftPlaquette
#print axioms timeTranslatedStrictLowerRoot_has_spatial_transport

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointFiniteCovarianceFence
