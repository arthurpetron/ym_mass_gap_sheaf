/-
# Compile one face-occupancy event into a finite strict cylinder

A local occupied-face event is not the occurrence of one prescribed polymer:
the connected component containing that face may have any finite shape.  In a
fixed finite box, however, it is exactly the disjunction of the occurrence
bits of all canonical polymers pinned at the face.

This file makes that observation literal.  The already-defined pinned layer
is used as the root list of a strict-cylinder vector, and the coefficient is
the zero-one indicator that at least one root occurs.  On every corrected-
compatible family, the cylinder event and coefficient recover
`familyContainsFaceB` exactly.

The root list still grows with the box.  Thus this is the finite-volume
observable compiler, not yet the fixed-root thermodynamic bridge.  The next
analytic step is to truncate by polymer size and use the uniform pinned KP
tail to control the omitted components.
-/

import YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm

namespace YMGap.Continuum.Z4CanonicalFaceEventCylinderCompiler

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The complete pinned-layer disjunction -/

/-- A Boolean word is accepted exactly when at least one marked occurrence
bit is true. -/
def canonicalFaceCylinderPredicate (bits : List Bool) : Bool :=
  bits.any (fun bit => bit)

/-- The complete fixed-box cylinder event obtained by marking every canonical
polymer that contains `face`. -/
def canonicalFaceCylinderEvent
    (n face : Nat) : List (List Nat) → Bool :=
  sourceCylinderEvent
    (canonicalPinnedLayerPolymers n face)
    canonicalFaceCylinderPredicate

theorem canonicalPinnedLayerPolymers_canonical
    (n face : Nat) :
    ∀ polymer, polymer ∈ canonicalPinnedLayerPolymers n face →
      polymer ∈ canonicalSurfacePolymers n := by
  intro polymer hpolymer
  exact (mem_canonicalPinnedLayerPolymers_iff.mp hpolymer).1

/-- In a fixed box, face occupancy is exactly the disjunction of the
occurrence bits of the complete pinned canonical layer. -/
theorem canonicalFaceCylinderEvent_eq_familyContainsFaceB
    {n face : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    canonicalFaceCylinderEvent n face family =
      familyContainsFaceB face family := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hcylinder
    unfold canonicalFaceCylinderEvent sourceCylinderEvent cylinderEvent
      canonicalFaceCylinderPredicate familyOccurrenceFingerprint at hcylinder
    obtain ⟨bit, hbit, hbitTrue⟩ := List.any_eq_true.mp hcylinder
    obtain ⟨polymer, hpolymer, hcontains⟩ := List.mem_map.mp hbit
    have hoccurs : polymer ∈ family := by
      unfold familyContainsPolymerB at hcontains
      exact of_decide_eq_true (hcontains.trans hbitTrue)
    have hfacePolymer : face ∈ polymer :=
      (mem_canonicalPinnedLayerPolymers_iff.mp hpolymer).2
    exact (familyContainsFaceB_true_iff face family).2
      ⟨polymer, hoccurs, hfacePolymer⟩
  · intro hface
    obtain ⟨polymer, hpolymerFamily, hfacePolymer⟩ :=
      (familyContainsFaceB_true_iff face family).1 hface
    have hpolymerCanonical : polymer ∈ canonicalSurfacePolymers n :=
      compatibleAmbientFamily_member_ambient hfamily hpolymerFamily
    have hpolymerPinned : polymer ∈ canonicalPinnedLayerPolymers n face :=
      mem_canonicalPinnedLayerPolymers_iff.mpr
        ⟨hpolymerCanonical, hfacePolymer⟩
    unfold canonicalFaceCylinderEvent sourceCylinderEvent cylinderEvent
      canonicalFaceCylinderPredicate familyOccurrenceFingerprint
    apply List.any_eq_true.mpr
    refine ⟨true, ?_, rfl⟩
    apply List.mem_map.mpr
    refine ⟨polymer, hpolymerPinned, ?_⟩
    unfold familyContainsPolymerB
    exact decide_eq_true hpolymerFamily

/-! ## 2. The corresponding rational strict-cylinder vector -/

/-- Zero-one rational coefficient of the complete pinned-layer event. -/
def canonicalFaceCylinderCoefficient (bits : List Bool) : Q' :=
  if canonicalFaceCylinderPredicate bits then 1 else 0

/-- The literal strict-cylinder presentation of one fixed-box face event. -/
def canonicalFaceStrictCylinderVector
    (base face : Nat) : StrictJointCylinderVector base where
  roots := canonicalPinnedLayerPolymers base face
  rootsCanonical := canonicalPinnedLayerPolymers_canonical base face
  coefficient := canonicalFaceCylinderCoefficient

/-- Pulling the strict-cylinder coefficient back to a compatible family gives
the exact zero-one indicator of face occupancy. -/
theorem canonicalFaceStrictCylinderVector_coefficient_eq
    {n face : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    (canonicalFaceStrictCylinderVector n face).coefficient
        (familyOccurrenceFingerprint
          (canonicalFaceStrictCylinderVector n face).roots family) =
      (if familyContainsFaceB face family then (1 : Q') else 0) := by
  have hevent := canonicalFaceCylinderEvent_eq_familyContainsFaceB
    (n := n) (face := face) (family := family) hfamily
  unfold canonicalFaceCylinderEvent sourceCylinderEvent cylinderEvent at hevent
  change
    (if canonicalFaceCylinderPredicate
          (familyOccurrenceFingerprint
            (canonicalPinnedLayerPolymers n face) family)
      then (1 : Q') else 0) =
      (if familyContainsFaceB face family then (1 : Q') else 0)
  rw [hevent]

#print axioms canonicalPinnedLayerPolymers_canonical
#print axioms canonicalFaceCylinderEvent_eq_familyContainsFaceB
#print axioms canonicalFaceStrictCylinderVector_coefficient_eq

end YMGap.Continuum.Z4CanonicalFaceEventCylinderCompiler
