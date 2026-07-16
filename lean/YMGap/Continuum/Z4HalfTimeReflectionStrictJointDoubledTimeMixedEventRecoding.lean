/-
# Exact event recoding for the doubled-time mixed OS geometry

The translated strict joint chart at radius `radius + shift` is a common
three-coordinate spatial translate of an oriented mixed chart at radius
`radius`: its lower block is the original reflected block, while its upper
block is translated forward by `2 * shift` in Euclidean time.

This file upgrades the support geometry to literal equality of canonical
root lists and hence literal equality of Boolean cylinder events.  The result
is finite geometry only.  It does not identify the corresponding normalized
finite-volume probabilities, which need not be exactly translation
invariant in a corner box.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

private theorem sameSupport_map_local
    {left right : List Z4Plaq} (reindex : Z4Plaq → Z4Plaq)
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map reindex) (right.map reindex) := by
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.1 source hsource, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.2 source hsource, rfl⟩

private theorem sameSupport_right_eq_local
    {left right target : List Z4Plaq}
    (hsupport : sameSupport (L := z4Chain.toLattice) left right)
    (heq : right = target) :
    sameSupport (L := z4Chain.toLattice) left target := by
  cases heq
  exact hsupport

/-! ## 1. A fixed-radius time translate of the upper root -/

theorem strictJointRawUpperQueryPlaquette_timeShift_sameRadius
    (radius shift : Nat) (plaquette : Z4Plaq) :
    strictJointRawUpperQueryPlaquette radius
        (timeShiftPlaquette shift plaquette) =
      timeShiftPlaquette shift
        (strictJointRawUpperQueryPlaquette radius plaquette) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;>
    simp [strictJointRawUpperQueryPlaquette,
      uniformShiftPlaquette, uniformShiftVertex,
      timeShiftPlaquette, timeShiftVertex,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Moving the source root forward while keeping the reflection radius fixed
moves the unreflected upper root forward by exactly the same amount. -/
theorem centralStrictUpperCanonicalRoot_timeShift_sameRadius
    {radius base shift : Nat}
    (hshiftedBase : strictQueryBase (base + shift) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient radius)
        (centralStrictUpperCanonicalRoot radius (base + shift)
          (timeShiftCanonicalRoot shift base root)))
      ((geometricPolymer (centralAmbient radius)
          (centralStrictUpperCanonicalRoot radius base root)).map
        (timeShiftPlaquette shift)) := by
  have hbase : strictQueryBase base ≤ radius := by
    unfold strictQueryBase uniformPaddedBase at hshiftedBase ⊢
    omega
  have htranslatedCanonical := timeShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htargetRaw :=
    centralStrictUpperCanonicalRoot_raw_sameSupport_local
      hshiftedBase htranslatedCanonical
  have htime := timeShiftCanonicalRoot_sameSupport
    (shift := shift) hroot
  have htargetNested := sameSupport_trans htargetRaw
    (sameSupport_map_local
      (strictJointRawUpperQueryPlaquette radius) htime)
  have hsourceRaw :=
    centralStrictUpperCanonicalRoot_raw_sameSupport_local hbase hroot
  have hsourceMapped := sameSupport_map_local
    (timeShiftPlaquette shift) hsourceRaw
  have hmaps :
      ((geometricPolymer base root).map
          (timeShiftPlaquette shift)).map
          (strictJointRawUpperQueryPlaquette radius) =
        ((geometricPolymer base root).map
          (strictJointRawUpperQueryPlaquette radius)).map
          (timeShiftPlaquette shift) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro plaquette _
    simp only [Function.comp_apply]
    exact strictJointRawUpperQueryPlaquette_timeShift_sameRadius
      radius shift plaquette
  have htargetCommon := sameSupport_right_eq_local htargetNested hmaps
  exact sameSupport_trans htargetCommon
    (sameSupport_symm hsourceMapped)

/-! ## 2. The oriented mixed chart -/

def strictJointDoubledTimeMixedLowerRoot
    (radius base shift : Nat) (root : List Nat) : List Nat :=
  centralStrictLowerCanonicalRoot radius base root

def strictJointDoubledTimeMixedUpperRoot
    (radius base shift : Nat) (root : List Nat) : List Nat :=
  centralStrictUpperCanonicalRoot radius (base + (shift + shift))
    (timeShiftCanonicalRoot (shift + shift) base root)

def strictJointDoubledTimeMixedCylinderRoots
    (radius base shift : Nat)
    (roots : List (List Nat)) : List (List Nat) :=
  roots.map (strictJointDoubledTimeMixedLowerRoot radius base shift) ++
    roots.map (strictJointDoubledTimeMixedUpperRoot radius base shift)

@[simp] theorem strictJointDoubledTimeMixedCylinderRoots_length
    (radius base shift : Nat) (roots : List (List Nat)) :
    (strictJointDoubledTimeMixedCylinderRoots
      radius base shift roots).length = roots.length + roots.length := by
  simp [strictJointDoubledTimeMixedCylinderRoots]

theorem strictJointDoubledTimeMixedCylinderRoots_canonical
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target,
      target ∈ strictJointDoubledTimeMixedCylinderRoots
          radius base shift roots →
        target ∈ canonicalSurfacePolymers (centralAmbient radius) := by
  intro target htarget
  have hbase : strictQueryBase base ≤ radius := by
    unfold strictQueryBase uniformPaddedBase at hadmissible ⊢
    omega
  rcases List.mem_append.mp htarget with hlower | hupper
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hlower
    exact centralStrictLowerCanonicalRoot_canonical hbase
      (hroots root hroot)
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hupper
    exact centralStrictUpperCanonicalRoot_canonical hadmissible
      (timeShiftCanonicalRoot_canonical
        (shift := shift + shift) (hroots root hroot))

/-! ## 3. Both target blocks are one spatial translate -/

theorem spatialShift_timeShift_doubled_eq_upperTransport
    (shift : Nat) (plaquette : Z4Plaq) :
    spatialShiftPlaquette shift
        (timeShiftPlaquette (shift + shift) plaquette) =
      strictJointDoubledTimeUpperTransport shift plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;>
    simp [strictJointDoubledTimeUpperTransport,
      spatialShiftPlaquette, spatialShiftVertex,
      timeShiftPlaquette, timeShiftVertex]

theorem timeTranslatedStrictJointUpperRoot_has_spatialMixed_transport
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centralAmbient (radius + shift))
        (centralStrictUpperCanonicalRoot (radius + shift) (base + shift)
          (timeShiftCanonicalRoot shift base root)))
      ((geometricPolymer (centralAmbient radius)
          (strictJointDoubledTimeMixedUpperRoot
            radius base shift root)).map
        (spatialShiftPlaquette shift)) := by
  have hbase : strictQueryBase base ≤ radius := by
    unfold strictQueryBase uniformPaddedBase at hadmissible ⊢
    omega
  have htarget :=
    timeTranslatedStrictJointUpperRoot_has_doubledTime_transport
      (shift := shift) hbase hroot
  have hmixed :=
    centralStrictUpperCanonicalRoot_timeShift_sameRadius
      hadmissible hroot
  have hmixedMapped := sameSupport_map_local
    (spatialShiftPlaquette shift) hmixed
  have hmaps :
      ((geometricPolymer (centralAmbient radius)
          (centralStrictUpperCanonicalRoot radius base root)).map
          (timeShiftPlaquette (shift + shift))).map
          (spatialShiftPlaquette shift) =
        (geometricPolymer (centralAmbient radius)
          (centralStrictUpperCanonicalRoot radius base root)).map
          (strictJointDoubledTimeUpperTransport shift) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro plaquette _
    simp only [Function.comp_apply]
    exact spatialShift_timeShift_doubled_eq_upperTransport
      shift plaquette
  have hmixedCommon := sameSupport_right_eq_local hmixedMapped hmaps
  exact sameSupport_trans htarget (sameSupport_symm hmixedCommon)

/-- Literal canonical-root equality for the reflected lower member. -/
theorem timeTranslatedStrictJointLowerRoot_eq_spatialMixed
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictLowerCanonicalRoot (radius + shift) (base + shift)
        (timeShiftCanonicalRoot shift base root) =
      spatialShiftCanonicalRoot shift (centralAmbient radius)
        (strictJointDoubledTimeMixedLowerRoot
          radius base shift root) := by
  have hbase : strictQueryBase base ≤ radius := by
    unfold strictQueryBase uniformPaddedBase at hadmissible ⊢
    omega
  have htargetBase : strictQueryBase (base + shift) ≤ radius + shift := by
    unfold strictQueryBase uniformPaddedBase at hbase ⊢
    omega
  have htranslatedCanonical := timeShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htargetCanonical := centralStrictLowerCanonicalRoot_canonical
    htargetBase htranslatedCanonical
  have hsourceCanonical := centralStrictLowerCanonicalRoot_canonical
    hbase hroot
  have hshiftedCanonical := spatialShiftCanonicalRoot_canonical
    (shift := shift) hsourceCanonical
  rw [uniformPaddedBase_centralAmbient] at hshiftedCanonical
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    htargetCanonical hshiftedCanonical
  have htargetSupport :=
    centralStrictLowerCanonicalRoot_timeShift_sameSupport
      (shift := shift) hbase hroot
  have hshiftedSupport := spatialShiftCanonicalRoot_sameSupport
    (shift := shift) hsourceCanonical
  rw [uniformPaddedBase_centralAmbient] at hshiftedSupport
  exact sameSupport_trans htargetSupport
    (sameSupport_symm hshiftedSupport)

/-- Literal canonical-root equality for the unreflected upper member. -/
theorem timeTranslatedStrictJointUpperRoot_eq_spatialMixed
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictUpperCanonicalRoot (radius + shift) (base + shift)
        (timeShiftCanonicalRoot shift base root) =
      spatialShiftCanonicalRoot shift (centralAmbient radius)
        (strictJointDoubledTimeMixedUpperRoot
          radius base shift root) := by
  have hbase : strictQueryBase base ≤ radius := by
    unfold strictQueryBase uniformPaddedBase at hadmissible ⊢
    omega
  have htargetBase : strictQueryBase (base + shift) ≤ radius + shift := by
    unfold strictQueryBase uniformPaddedBase at hbase ⊢
    omega
  have htranslatedCanonical := timeShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htargetCanonical := centralStrictUpperCanonicalRoot_canonical
    htargetBase htranslatedCanonical
  have hmixedCanonical := centralStrictUpperCanonicalRoot_canonical
    hadmissible
    (timeShiftCanonicalRoot_canonical
      (shift := shift + shift) hroot)
  have hshiftedCanonical := spatialShiftCanonicalRoot_canonical
    (shift := shift) hmixedCanonical
  rw [uniformPaddedBase_centralAmbient] at hshiftedCanonical
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    htargetCanonical hshiftedCanonical
  have htargetSupport :=
    timeTranslatedStrictJointUpperRoot_has_spatialMixed_transport
      hadmissible hroot
  have hshiftedSupport := spatialShiftCanonicalRoot_sameSupport
    (shift := shift) hmixedCanonical
  rw [uniformPaddedBase_centralAmbient] at hshiftedSupport
  exact sameSupport_trans htargetSupport
    (sameSupport_symm hshiftedSupport)

/-! ## 4. Literal root-list and event equality -/

theorem timeTranslatedStrictJointCylinderRoots_eq_spatialMixed
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centralStrictJointCylinderRoots (radius + shift) (base + shift)
        (roots.map (timeShiftCanonicalRoot shift base)) =
      (strictJointDoubledTimeMixedCylinderRoots
        radius base shift roots).map
          (spatialShiftCanonicalRoot shift (centralAmbient radius)) := by
  unfold centralStrictJointCylinderRoots
    centralStrictLowerCylinderRoots centralStrictUpperCylinderRoots
    strictJointDoubledTimeMixedCylinderRoots
  rw [List.map_append, List.map_map, List.map_map,
    List.map_map, List.map_map]
  have hlower :
      roots.map
          (centralStrictLowerCanonicalRoot (radius + shift)
            (base + shift) ∘ timeShiftCanonicalRoot shift base) =
        roots.map
          (spatialShiftCanonicalRoot shift (centralAmbient radius) ∘
            strictJointDoubledTimeMixedLowerRoot radius base shift) := by
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact timeTranslatedStrictJointLowerRoot_eq_spatialMixed
      hadmissible (hroots root hroot)
  have hupper :
      roots.map
          (centralStrictUpperCanonicalRoot (radius + shift)
            (base + shift) ∘ timeShiftCanonicalRoot shift base) =
        roots.map
          (spatialShiftCanonicalRoot shift (centralAmbient radius) ∘
            strictJointDoubledTimeMixedUpperRoot radius base shift) := by
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact timeTranslatedStrictJointUpperRoot_eq_spatialMixed
      hadmissible (hroots root hroot)
  rw [hlower, hupper]

def strictJointDoubledTimeMixedCylinderEvent
    (radius base shift : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) : List (List Nat) → Bool :=
  sourceCylinderEvent
    (strictJointDoubledTimeMixedCylinderRoots
      radius base shift roots) predicate

def spatialShiftedStrictJointDoubledTimeMixedCylinderEvent
    (radius base shift : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) : List (List Nat) → Bool :=
  sourceCylinderEvent
    ((strictJointDoubledTimeMixedCylinderRoots
      radius base shift roots).map
        (spatialShiftCanonicalRoot shift (centralAmbient radius)))
    predicate

/-- The translated joint event is exactly the spatially re-encoded mixed
event.  No probability law appears in this statement. -/
theorem timeTranslatedStrictJointCylinderEvent_eq_spatialMixed
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    sourceCylinderEvent
        (centralStrictJointCylinderRoots (radius + shift) (base + shift)
          (roots.map (timeShiftCanonicalRoot shift base))) predicate =
      spatialShiftedStrictJointDoubledTimeMixedCylinderEvent
        radius base shift roots predicate := by
  unfold spatialShiftedStrictJointDoubledTimeMixedCylinderEvent
  rw [timeTranslatedStrictJointCylinderRoots_eq_spatialMixed
    hadmissible hroots]

#print axioms spatialShift_timeShift_doubled_eq_upperTransport
#print axioms centralStrictUpperCanonicalRoot_timeShift_sameRadius
#print axioms timeTranslatedStrictJointLowerRoot_eq_spatialMixed
#print axioms timeTranslatedStrictJointUpperRoot_eq_spatialMixed
#print axioms timeTranslatedStrictJointCylinderRoots_eq_spatialMixed
#print axioms timeTranslatedStrictJointCylinderEvent_eq_spatialMixed

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding
