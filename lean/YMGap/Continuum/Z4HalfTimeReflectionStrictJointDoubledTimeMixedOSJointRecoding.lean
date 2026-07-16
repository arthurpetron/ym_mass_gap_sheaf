/-
# Recoding the oriented mixed event as one ordinary strict-joint event

The direct mixed OS entry constrains the lower fingerprint of the transported
source and the upper fingerprint of the doubled-time target.  Put both root
lists into one ordinary strict-joint chart.  Its four fingerprint blocks are

  lower source, lower target, upper source, upper target.

The projection below retains exactly the first and fourth blocks.  Thus the
oriented mixed cylinder is literally an ordinary strict-joint cylinder with
one Boolean predicate; the two unused blocks carry no condition.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSEntryEvent

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointRecoding

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSEntryEvent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery

/-- The source and target roots, regarded as one root list in their common
outer presentation box. -/
def strictJointDoubledTimeMixedJointRoots
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : List (List Nat) :=
  (strictJointDoubledTimeMixedSource shift vector).roots ++
    (strictJointDoubledTimeMixedTarget shift vector).roots

@[simp] theorem strictJointDoubledTimeMixedJointRoots_length
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    (strictJointDoubledTimeMixedJointRoots shift vector).length =
      vector.roots.length + vector.roots.length := by
  unfold strictJointDoubledTimeMixedJointRoots
    strictJointDoubledTimeMixedSource
    strictJointDoubledTimeMixedTarget
    boxTransportStrictJointCylinderVector transportedCylinderRoots
  simp only [List.length_append, List.length_map,
    timeTranslateStrictJointCylinderVector_roots]

theorem strictJointDoubledTimeMixedJointRoots_canonical
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    ∀ root, root ∈ strictJointDoubledTimeMixedJointRoots shift vector →
      root ∈ canonicalSurfacePolymers (base + (shift + shift)) := by
  intro root hroot
  rcases List.mem_append.mp hroot with hsource | htarget
  · exact (strictJointDoubledTimeMixedSource shift vector).rootsCanonical
      root hsource
  · exact (strictJointDoubledTimeMixedTarget shift vector).rootsCanonical
      root htarget

/-- Retain the lower-source block and the upper-target block from a standard
four-block strict-joint fingerprint. -/
def strictJointDoubledTimeMixedJointProjection
    (rootCount : Nat) (bits : List Bool) : List Bool :=
  bits.take rootCount ++
    bits.drop (rootCount + (rootCount + rootCount))

/-- The ordinary strict-joint predicate which imposes only the oriented
source/target pair constraint. -/
def strictJointDoubledTimeMixedJointPredicate
    (rootCount : Nat) (left right : List Bool) : List Bool → Bool :=
  fun bits => centralStrictJointPairPredicate rootCount left right
    (strictJointDoubledTimeMixedJointProjection rootCount bits)

private theorem four_block_projection
    (rootCount : Nat)
    (first second third fourth : List Bool)
    (hfirst : first.length = rootCount)
    (hsecond : second.length = rootCount)
    (hthird : third.length = rootCount) :
    strictJointDoubledTimeMixedJointProjection rootCount
        ((first ++ second) ++ (third ++ fourth)) =
      first ++ fourth := by
  unfold strictJointDoubledTimeMixedJointProjection
  rw [show (first ++ second) ++ (third ++ fourth) =
      first ++ (second ++ (third ++ fourth)) by
        simp only [List.append_assoc]]
  rw [← hfirst, List.take_append_length]
  rw [List.drop_length_add_append]
  have hsum : first.length + first.length =
      second.length + third.length := by
    omega
  rw [hsum, List.drop_length_add_append, List.drop_append_length]

/-- The ordinary four-block joint cylinder with the projection predicate is
literally the oriented two-block common cylinder. -/
theorem strictJointDoubledTimeMixedJointEvent_eq_common
    {base : Nat} (shift radius : Nat)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) :
    sourceCylinderEvent
        (centralStrictJointCylinderRoots
          radius (base + (shift + shift))
          (strictJointDoubledTimeMixedJointRoots shift vector))
        (strictJointDoubledTimeMixedJointPredicate
          vector.roots.length left right) =
      sourceCylinderEvent
        (strictJointDoubledTimeCommonCylinderRoots radius shift vector)
        (centralStrictJointPairPredicate
          vector.roots.length left right) := by
  funext family
  unfold sourceCylinderEvent cylinderEvent
    strictJointDoubledTimeMixedJointRoots
    strictJointDoubledTimeCommonCylinderRoots
    centralStrictJointCylinderRoots
    strictJointDoubledTimeMixedJointPredicate
  unfold centralStrictLowerCylinderRoots centralStrictUpperCylinderRoots
  simp only [List.map_append, familyOccurrenceFingerprint_append]
  apply congrArg (centralStrictJointPairPredicate
    vector.roots.length left right)
  apply four_block_projection
  · rw [familyOccurrenceFingerprint_length, List.length_map]
    unfold strictJointDoubledTimeMixedSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
    simp only [List.length_map]
  · rw [familyOccurrenceFingerprint_length, List.length_map]
    unfold strictJointDoubledTimeMixedTarget
    simp only [timeTranslateStrictJointCylinderVector_roots, List.length_map]
  · rw [familyOccurrenceFingerprint_length, List.length_map]
    unfold strictJointDoubledTimeMixedSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
    simp only [List.length_map]

#print axioms strictJointDoubledTimeMixedJointRoots_canonical
#print axioms strictJointDoubledTimeMixedJointEvent_eq_common

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointRecoding
