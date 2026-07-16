/-
# Literal mixed-cylinder event carried by each direct OS entry

The two-code conditional event is specialized to strict source and target
query codes.  Its family event is exactly one cylinder on the concatenation
of the source lower roots and target upper roots.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipairConditional

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSEntryEvent

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipairConditional
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery

local infix:50 " ≈ " => Q'.eqv

/-- The oriented common-box root list: transported source roots on the lower
side and doubled-time target roots on the upper side. -/
def strictJointDoubledTimeCommonCylinderRoots
    {base : Nat} (radius shift : Nat)
    (vector : StrictJointCylinderVector base) : List (List Nat) :=
  let outer := base + (shift + shift)
  centralStrictLowerCylinderRoots radius outer
      (strictJointDoubledTimeMixedSource shift vector).roots ++
    centralStrictUpperCylinderRoots radius outer
      (strictJointDoubledTimeMixedTarget shift vector).roots

theorem centralLocalSupportBipairFamilyEvent_strict_physical
    {radius leftBase rightBase : Nat}
    (hleftBase : strictQueryBase leftBase ≤ radius)
    (hrightBase : strictQueryBase rightBase ≤ radius)
    {leftRoots rightRoots : List (List Nat)}
    (hleftRoots : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers leftBase)
    (hrightRoots : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers rightBase)
    (left right : List Bool) (physical : EdgeLabelling) :
    centralLocalSupportBipairFamilyEvent radius
        (centralStrictLocalQueryCode radius leftBase leftRoots)
        (centralStrictLocalQueryCode radius rightBase rightRoots)
        left right
        (physicalCanonicalAmbientFamily (centralAmbient radius) physical) =
      sourceCylinderEvent
        (centralStrictLowerCylinderRoots radius leftBase leftRoots ++
          centralStrictUpperCylinderRoots radius rightBase rightRoots)
        (centralStrictJointPairPredicate leftRoots.length left right)
        (physicalCanonicalAmbientFamily
          (centralAmbient radius) physical) := by
  rw [centralLocalSupportBipairFamilyEvent_physical]
  unfold centralStrictLocalQueryCode
  rw [centralStrictLowerSupportQueryFingerprint_eq_familyOccurrence
      hleftBase hleftRoots physical,
    centralStrictReflectedUpperSupportQueryFingerprint_eq_familyOccurrence
      hrightBase hrightRoots physical]
  unfold sourceCylinderEvent cylinderEvent centralStrictJointPairPredicate
  rw [familyOccurrenceFingerprint_append]
  have hlength :
      (familyOccurrenceFingerprint
        (centralStrictLowerCylinderRoots radius leftBase leftRoots)
        (physicalCanonicalAmbientFamily
          (centralAmbient radius) physical)).length = leftRoots.length := by
    rw [familyOccurrenceFingerprint_length,
      centralStrictLowerCylinderRoots_length]
  rw [← hlength, List.take_append_length, List.drop_append_length]

theorem couplingPhysicalGivenSlab_strictBipair_eq_cylinder
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat)
    {radius leftBase rightBase : Nat}
    (hleftBase : strictQueryBase leftBase ≤ radius)
    (hrightBase : strictQueryBase rightBase ≤ radius)
    {leftRoots rightRoots : List (List Nat)}
    (hleftRoots : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers leftBase)
    (hrightRoots : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers rightBase)
    (left right : List Bool) :
    couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling cutoff (centralExtent radius)
        (centralLocalSupportBipairFamilyEvent radius
          (centralStrictLocalQueryCode radius leftBase leftRoots)
          (centralStrictLocalQueryCode radius rightBase rightRoots)
          left right) =
      couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling cutoff (centralExtent radius)
        (sourceCylinderEvent
          (centralStrictLowerCylinderRoots radius leftBase leftRoots ++
            centralStrictUpperCylinderRoots radius rightBase rightRoots)
          (centralStrictJointPairPredicate leftRoots.length left right)) := by
  have hevents :
      (fun physical =>
        ambientSlabSupportedB (centralExtent radius) physical &&
          cutoffOneLiftedFamilyEvent (centralExtent radius + 1)
            (centralLocalSupportBipairFamilyEvent radius
              (centralStrictLocalQueryCode radius leftBase leftRoots)
              (centralStrictLocalQueryCode radius rightBase rightRoots)
              left right) physical) =
      (fun physical =>
        ambientSlabSupportedB (centralExtent radius) physical &&
          cutoffOneLiftedFamilyEvent (centralExtent radius + 1)
            (sourceCylinderEvent
              (centralStrictLowerCylinderRoots radius leftBase leftRoots ++
                centralStrictUpperCylinderRoots radius rightBase rightRoots)
              (centralStrictJointPairPredicate
                leftRoots.length left right)) physical) := by
    funext physical
    unfold cutoffOneLiftedFamilyEvent
    have hphysical :=
      centralLocalSupportBipairFamilyEvent_strict_physical
        hleftBase hrightBase hleftRoots hrightRoots left right physical
    simpa only [centralAmbient] using congrArg
      (fun value => ambientSlabSupportedB (centralExtent radius) physical && value)
      hphysical
  unfold couplingParametricKPhysicalGivenSlabProbability
  rw [hevents]

/-- An oriented direct OS entry is exactly the corrected-slab probability of
the common-box mixed cylinder. -/
theorem strictJointDoubledTimeMixedOSOrientedEntrySequence_eqv_cylinder
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) (stage : Nat) :
    strictJointDoubledTimeMixedOSOrientedEntrySequence
        coupling hcoupling shift vector left right stage ≈
      couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling
        (centralStrictJointCenteredStageCutoff
          (base + (shift + shift)) stage)
        (centralExtent
          (strictQueryBase (base + (shift + shift)) + stage))
        (sourceCylinderEvent
          (strictJointDoubledTimeCommonCylinderRoots
            (strictQueryBase (base + (shift + shift)) + stage)
            shift vector)
          (centralStrictJointPairPredicate
            vector.roots.length left right)) := by
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  have hbase : strictQueryBase outer ≤ radius :=
    Nat.le_add_right (strictQueryBase outer) stage
  have hentry := centralNormalizedSupportBipairLaw_eq_physicalGivenSlab
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff outer stage) radius
    (centralStrictLocalQueryCode radius outer
      (strictJointDoubledTimeMixedSource shift vector).roots)
    (centralStrictLocalQueryCode radius outer
      (strictJointDoubledTimeMixedTarget shift vector).roots)
    left right
  have hevent := couplingPhysicalGivenSlab_strictBipair_eq_cylinder
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff outer stage)
    hbase hbase
    (strictJointDoubledTimeMixedSource shift vector).rootsCanonical
    (strictJointDoubledTimeMixedTarget shift vector).rootsCanonical
    left right
  rw [hevent] at hentry
  simpa only [strictJointDoubledTimeMixedOSOrientedEntrySequence,
    strictJointDoubledTimeCommonCylinderRoots, outer, radius,
    strictJointDoubledTimeMixedSource,
    strictJointDoubledTimeMixedTarget,
    boxTransportStrictJointCylinderVector_roots,
    timeTranslateStrictJointCylinderVector_roots,
    transportedCylinderRoots, List.length_map] using hentry

#print axioms centralLocalSupportBipairFamilyEvent_strict_physical
#print axioms couplingPhysicalGivenSlab_strictBipair_eq_cylinder
#print axioms strictJointDoubledTimeMixedOSOrientedEntrySequence_eqv_cylinder

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSEntryEvent
