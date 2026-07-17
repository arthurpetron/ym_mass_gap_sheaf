/-
# Exact corrected-slab covariance remainder for strict time translation

The translated strict local Gram entry and the source entry are conditional
probabilities in two different corrected slabs.  Their exact finite
comparison therefore has two normalizations.  This file records the honest
target-minus-source cross determinant, first for arbitrary corrected-slab
events and then for the strict joint cylinder.

Only the reflected lower query is transported by a pure three-coordinate
spatial shift.  The unreflected upper query also moves forward in Euclidean
time, so the whole translated joint event is retained literally below.  No
whole-event spatial covariance, vanishing remainder, contraction, or
infinite-volume state invariance is asserted.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointFiniteCovarianceFence

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCorrectedSlabCovarianceRemainder

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointFiniteCovarianceFence
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslationAction
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4TimeShiftedFiniteNormalizedCovarianceRemainder

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic exact conditional normalization algebra -/

def couplingParametricKPhysicalSlabSupportDenominator
    (coupling : Q') (cutoff extent : Nat) : Q' :=
  parametricKEventNumerator coupling cutoff (extent + 1)
    (ambientSlabSupportedB extent)

def couplingParametricKPhysicalSlabRestrictedNumerator
    (coupling : Q') (cutoff extent : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  parametricKEventNumerator coupling cutoff (extent + 1)
    (fun physical => ambientSlabSupportedB extent physical &&
      cutoffOneLiftedFamilyEvent (extent + 1) event physical)

/-- Correct orientation for target minus source with two conditional
normalizations: `N_target * D_source - N_source * D_target`. -/
def couplingParametricKPhysicalGivenSlabCrossRemainder
    (coupling : Q') (cutoff targetExtent sourceExtent : Nat)
    (targetEvent sourceEvent : List (List Nat) → Bool) : Q' :=
  couplingParametricKPhysicalSlabRestrictedNumerator
        coupling cutoff targetExtent targetEvent *
      couplingParametricKPhysicalSlabSupportDenominator
        coupling cutoff sourceExtent -
    couplingParametricKPhysicalSlabRestrictedNumerator
        coupling cutoff sourceExtent sourceEvent *
      couplingParametricKPhysicalSlabSupportDenominator
        coupling cutoff targetExtent

theorem couplingParametricKPhysicalGivenSlabProbability_sub_eqv_crossRemainder
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff targetExtent sourceExtent : Nat)
    (targetEvent sourceEvent : List (List Nat) → Bool) :
    couplingParametricKPhysicalGivenSlabProbability
          coupling hcoupling cutoff targetExtent targetEvent -
        couplingParametricKPhysicalGivenSlabProbability
          coupling hcoupling cutoff sourceExtent sourceEvent ≈
      Q'.divPos
        (couplingParametricKPhysicalGivenSlabCrossRemainder
          coupling cutoff targetExtent sourceExtent
          targetEvent sourceEvent)
        (couplingParametricKPhysicalSlabSupportDenominator
            coupling cutoff targetExtent *
          couplingParametricKPhysicalSlabSupportDenominator
            coupling cutoff sourceExtent)
        (Q'.mul_pos
          (couplingParametricKPhysicalSlabSupportNumerator_pos
            hcoupling cutoff targetExtent)
          (couplingParametricKPhysicalSlabSupportNumerator_pos
            hcoupling cutoff sourceExtent)) := by
  unfold couplingParametricKPhysicalGivenSlabProbability
    couplingParametricKPhysicalGivenSlabCrossRemainder
    couplingParametricKPhysicalSlabRestrictedNumerator
    couplingParametricKPhysicalSlabSupportDenominator
  exact divPos_sub_eqv_crossDifference _ _ _ _
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hcoupling cutoff targetExtent)
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hcoupling cutoff sourceExtent)

/-! ## 2. Literal source and translated strict joint events -/

def strictJointCorrectedSlabCylinderEvent
    {base : Nat} (radius : Nat)
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) : List (List Nat) → Bool :=
  slabMarkedCylinderEvent
    (centralStrictJointCanonicalAtoms radius base vector.roots
      hbase vector.rootsCanonical)
    (centralStrictJointPairPredicate vector.roots.length left right)

def timeTranslatedStrictJointCorrectedSlabCylinderEvent
    {base radius : Nat} (hbase : strictQueryBase base ≤ radius)
    (shift : Nat) (vector : StrictJointCylinderVector base)
    (left right : List Bool) : List (List Nat) → Bool :=
  strictJointCorrectedSlabCylinderEvent (radius + shift)
    (strictQueryBase_le_after_timeTranslate hbase shift)
    (timeTranslateStrictJointCylinderVector shift vector) left right

def timeTranslatedStrictJointCorrectedSlabCrossRemainder
    (coupling : Q') (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) : Q' :=
  couplingParametricKPhysicalGivenSlabCrossRemainder
    coupling cutoff
    (centralExtent (radius + shift)) (centralExtent radius)
    (timeTranslatedStrictJointCorrectedSlabCylinderEvent
      hbase shift vector left right)
    (strictJointCorrectedSlabCylinderEvent
      radius hbase vector left right)

/-- Exact target-minus-source conditional law for the translated strict
joint cylinder.  This theorem deliberately leaves the boundary determinant
visible. -/
theorem timeTranslatedStrictJointCorrectedSlabProbability_sub_source_eqv_remainder
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) :
    couplingParametricKPhysicalGivenSlabProbability
          coupling hcoupling cutoff (centralExtent (radius + shift))
          (timeTranslatedStrictJointCorrectedSlabCylinderEvent
            hbase shift vector left right) -
        couplingParametricKPhysicalGivenSlabProbability
          coupling hcoupling cutoff (centralExtent radius)
          (strictJointCorrectedSlabCylinderEvent
            radius hbase vector left right) ≈
      Q'.divPos
        (timeTranslatedStrictJointCorrectedSlabCrossRemainder
          coupling cutoff radius shift hbase vector left right)
        (couplingParametricKPhysicalSlabSupportDenominator
            coupling cutoff (centralExtent (radius + shift)) *
          couplingParametricKPhysicalSlabSupportDenominator
            coupling cutoff (centralExtent radius))
        (Q'.mul_pos
          (couplingParametricKPhysicalSlabSupportNumerator_pos
            hcoupling cutoff (centralExtent (radius + shift)))
          (couplingParametricKPhysicalSlabSupportNumerator_pos
            hcoupling cutoff (centralExtent radius))) := by
  simpa only [timeTranslatedStrictJointCorrectedSlabCrossRemainder] using
    (couplingParametricKPhysicalGivenSlabProbability_sub_eqv_crossRemainder
      hcoupling cutoff
      (centralExtent (radius + shift)) (centralExtent radius)
      (timeTranslatedStrictJointCorrectedSlabCylinderEvent
        hbase shift vector left right)
      (strictJointCorrectedSlabCylinderEvent
        radius hbase vector left right))

/-! ## 3. Entrywise strict local-Gram specialization -/

theorem timeTranslatedStrictJointLocalGramEntry_sub_source_eqv_remainder
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) :
    centralNormalizedLocalSupportPairLaw
          coupling hcoupling cutoff (radius + shift)
          (centralStrictLocalQueryCode (radius + shift) (base + shift)
            (timeTranslateStrictJointCylinderVector shift vector).roots)
          left right -
        centralNormalizedLocalSupportPairLaw
          coupling hcoupling cutoff radius
          (centralStrictLocalQueryCode radius base vector.roots)
          left right ≈
      Q'.divPos
        (timeTranslatedStrictJointCorrectedSlabCrossRemainder
          coupling cutoff radius shift hbase vector left right)
        (couplingParametricKPhysicalSlabSupportDenominator
            coupling cutoff (centralExtent (radius + shift)) *
          couplingParametricKPhysicalSlabSupportDenominator
            coupling cutoff (centralExtent radius))
        (Q'.mul_pos
          (couplingParametricKPhysicalSlabSupportNumerator_pos
            hcoupling cutoff (centralExtent (radius + shift)))
          (couplingParametricKPhysicalSlabSupportNumerator_pos
            hcoupling cutoff (centralExtent radius))) := by
  have htarget :=
    centralNormalizedLocalSupportPairLaw_eq_strictMarkedCylinder
      coupling hcoupling cutoff
      (strictQueryBase_le_after_timeTranslate hbase shift)
      (timeTranslateStrictJointCylinderVector shift vector).rootsCanonical
      left right
  have hsource :=
    centralNormalizedLocalSupportPairLaw_eq_strictMarkedCylinder
      coupling hcoupling cutoff hbase vector.rootsCanonical left right
  have hreplace :
      centralNormalizedLocalSupportPairLaw
            coupling hcoupling cutoff (radius + shift)
            (centralStrictLocalQueryCode (radius + shift) (base + shift)
              (timeTranslateStrictJointCylinderVector shift vector).roots)
            left right -
          centralNormalizedLocalSupportPairLaw
            coupling hcoupling cutoff radius
            (centralStrictLocalQueryCode radius base vector.roots)
            left right ≈
        couplingParametricKPhysicalGivenSlabProbability
              coupling hcoupling cutoff (centralExtent (radius + shift))
              (timeTranslatedStrictJointCorrectedSlabCylinderEvent
                hbase shift vector left right) -
          couplingParametricKPhysicalGivenSlabProbability
              coupling hcoupling cutoff (centralExtent radius)
              (strictJointCorrectedSlabCylinderEvent
                radius hbase vector left right) := by
    simpa only [timeTranslatedStrictJointCorrectedSlabCylinderEvent,
      strictJointCorrectedSlabCylinderEvent] using
      (Q'.add_eqv_congr' htarget
        (Q'.neg_eqv_congr _ _ hsource))
  exact Q'.eqv_trans _ _ _ hreplace
    (timeTranslatedStrictJointCorrectedSlabProbability_sub_source_eqv_remainder
      hcoupling cutoff radius shift hbase vector left right)

/-- The geometric input behind the target event is pure spatial transport
for each reflected lower root.  No corresponding claim is made for the
whole lower-plus-upper event. -/
theorem timeTranslatedStrictJointLowerRoot_has_spatial_transport
    {radius base shift : Nat} (hbase : strictQueryBase base ≤ radius)
    (vector : StrictJointCylinderVector base) {root : List Nat}
    (hroot : root ∈ vector.roots) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient (radius + shift))
        (centralStrictLowerCanonicalRoot (radius + shift) (base + shift)
          (timeShiftCanonicalRoot shift base root)))
      ((geometricPolymer (centralAmbient radius)
          (centralStrictLowerCanonicalRoot radius base root)).map
        (spatialShiftPlaquette shift)) :=
  timeTranslatedStrictLowerRoot_has_spatial_transport
    hbase (vector.rootsCanonical root hroot)

#print axioms couplingParametricKPhysicalGivenSlabProbability_sub_eqv_crossRemainder
#print axioms timeTranslatedStrictJointCorrectedSlabProbability_sub_source_eqv_remainder
#print axioms timeTranslatedStrictJointLocalGramEntry_sub_source_eqv_remainder
#print axioms timeTranslatedStrictJointLowerRoot_has_spatial_transport

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCorrectedSlabCovarianceRemainder
