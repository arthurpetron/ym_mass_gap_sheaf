/-
# Fixed-stage recoding of the projected joint chart

At mixed signed stage `fixedStage`, the common radius agrees with the
ordinary concatenated joint chart at outer-base stage
`fixedStage - 2 * shift`.  The lower source root is unchanged by first
transporting its source name to the outer box, while the selected upper
target root is definitionally the mixed upper root.  Consequently the
four-block projection event is literally the existing two-block mixed signed
event.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointCenteredBridge
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointFixedStageRecoding

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
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

/-- A strict lower query depends on geometric source support, not on which
finite source box supplies its canonical numerical name. -/
theorem centralStrictLowerCanonicalRoot_transportBase_eq
    {base outer radius : Nat} (hbase : base ≤ outer)
    (houter : strictQueryBase outer ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictLowerCanonicalRoot radius outer
        (transportPolymer base outer root) =
      centralStrictLowerCanonicalRoot radius base root := by
  have hbaseRadius : strictQueryBase base ≤ radius := by
    unfold strictQueryBase uniformPaddedBase at houter ⊢
    omega
  have htransported : transportPolymer base outer root ∈
      canonicalSurfacePolymers outer :=
    transportPolymer_mem_canonicalSurfacePolymers hbase hroot
  have hleft := centralStrictLowerCanonicalRoot_canonical
    houter htransported
  have hright := centralStrictLowerCanonicalRoot_canonical
    hbaseRadius hroot
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport hleft hright
  have hleftRaw := centralStrictLowerCanonicalRoot_raw_sameSupport
    houter htransported
  have hrightRaw := centralStrictLowerCanonicalRoot_raw_sameSupport
    hbaseRadius hroot
  have htransport := transportPolymer_sameSupport hbase
    (canonicalSurfacePolymer_mem_faceSupports hroot)
  have hmapped := sameSupport_map_local
    (rawStrictLowerQueryPlaquette radius) htransport
  exact sameSupport_trans hleftRaw
    (sameSupport_trans (sameSupport_symm hmapped)
      (sameSupport_symm hrightRaw))

/-- At aligned fixed stages, the lower centered source root is literally
independent of whether the original root was first transported to the common
outer source box. -/
theorem strictJointDoubledTimeMixedJointLowerCenteredRoot_eq
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictLowerCenteredStageRoot
        (base + (shift + shift))
        (fixedStage - (shift + shift))
        (transportPolymer base (base + (shift + shift)) root) =
      strictJointDoubledTimeMixedCenteredLowerRoot
        base shift fixedStage root := by
  let outer := base + (shift + shift)
  let jointStage := fixedStage - (shift + shift)
  have hbaseOuter : base ≤ outer := by
    dsimp only [outer]
    omega
  have htransported : transportPolymer base outer root ∈
      canonicalSurfacePolymers outer :=
    transportPolymer_mem_canonicalSurfacePolymers hbaseOuter hroot
  have hradius : strictQueryBase outer + jointStage =
      strictQueryBase base + fixedStage := by
    dsimp only [outer, jointStage]
    exact strictJointDoubledTime_mixedRadius_eq hstage
  have hleftCanonical := uniformShiftCanonicalRoot_canonical
    (padding := jointStage)
    (centralStrictLowerCenteredSourceRoot_canonical htransported)
  rw [strictJointCenteredStageBase_eq, hradius] at hleftCanonical
  have hrightCanonical :=
    strictJointDoubledTimeMixedCenteredLowerRoot_canonical
      (shift := shift) (stage := fixedStage) hroot
  have hle := strictJointCenteredStageBase_le_centralAmbient
    base fixedStage
  apply transportPolymer_injective_on_canonical hle
    hleftCanonical hrightCanonical
  have hleftTransport :=
    centralStrictLowerCanonicalRoot_eq_transport_centeredStage
      (base := outer) (stage := jointStage) htransported
  rw [hradius] at hleftTransport
  have hrightTransport :=
    centralStrictLowerCanonicalRoot_eq_transport_centeredStage
      (base := base) (stage := fixedStage) hroot
  have hcorner := centralStrictLowerCanonicalRoot_transportBase_eq
    hbaseOuter
    (Nat.le_add_right (strictQueryBase outer) jointStage)
    hroot
  rw [hradius] at hcorner
  exact Eq.trans hleftTransport.symm
    (Eq.trans hcorner hrightTransport)

/-- The selected lower-source/upper-target roots of the aligned ordinary
joint chart are exactly the existing mixed centered roots. -/
theorem strictJointDoubledTimeMixedJointSelectedCenteredRoots_eq
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base) :
    (strictJointDoubledTimeMixedSource shift vector).roots.map
          (centralStrictLowerCenteredStageRoot
            (base + (shift + shift))
            (fixedStage - (shift + shift))) ++
        (strictJointDoubledTimeMixedTarget shift vector).roots.map
          (centralStrictUpperCenteredStageRoot
            (base + (shift + shift))
            (fixedStage - (shift + shift))) =
      strictJointDoubledTimeMixedCenteredRoots
        base shift fixedStage vector.roots := by
  unfold strictJointDoubledTimeMixedSource
    strictJointDoubledTimeMixedTarget
    boxTransportStrictJointCylinderVector transportedCylinderRoots
    strictJointDoubledTimeMixedCenteredRoots
    strictJointDoubledTimeMixedCenteredUpperRoot
  simp only [timeTranslateStrictJointCylinderVector_roots,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  exact strictJointDoubledTimeMixedJointLowerCenteredRoot_eq
    hstage (vector.rootsCanonical root hroot)

private theorem four_block_projection_local
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

theorem projectedFourBlockCylinderEvent_eq
    (rootCount : Nat)
    (firstRoots secondRoots thirdRoots fourthRoots : List (List Nat))
    (hfirst : firstRoots.length = rootCount)
    (hsecond : secondRoots.length = rootCount)
    (hthird : thirdRoots.length = rootCount)
    (left right : List Bool) :
    sourceCylinderEvent
        ((firstRoots ++ secondRoots) ++ (thirdRoots ++ fourthRoots))
        (strictJointDoubledTimeMixedJointPredicate
          rootCount left right) =
      sourceCylinderEvent
        (firstRoots ++ fourthRoots)
        (centralStrictJointPairPredicate rootCount left right) := by
  funext family
  unfold sourceCylinderEvent cylinderEvent
    strictJointDoubledTimeMixedJointPredicate
  simp only [familyOccurrenceFingerprint_append]
  apply congrArg (centralStrictJointPairPredicate rootCount left right)
  apply four_block_projection_local
  · rw [familyOccurrenceFingerprint_length, hfirst]
  · rw [familyOccurrenceFingerprint_length, hsecond]
  · rw [familyOccurrenceFingerprint_length, hthird]

/-- Exact fixed-stage event recoding: the centered ordinary concatenated
joint event with the four-block projection predicate is the mixed signed
two-block event. -/
theorem strictJointDoubledTimeMixedJointCenteredEvent_eq_signedMixed
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) :
    sourceCylinderEvent
        (centralStrictJointCenteredStageRoots
          (base + (shift + shift))
          (fixedStage - (shift + shift))
          (strictJointDoubledTimeMixedJointRoots shift vector))
        (strictJointDoubledTimeMixedJointPredicate
          vector.roots.length left right) =
      sourceCylinderEvent
        (strictJointDoubledTimeMixedCenteredRoots
          base shift fixedStage vector.roots)
        (centralStrictJointPairPredicate
          vector.roots.length left right) := by
  rw [centralStrictJointCenteredStageRoots_split]
  unfold strictJointDoubledTimeMixedJointRoots
  simp only [List.map_append]
  rw [projectedFourBlockCylinderEvent_eq
    vector.roots.length
    ((strictJointDoubledTimeMixedSource shift vector).roots.map
      (centralStrictLowerCenteredStageRoot
        (base + (shift + shift))
        (fixedStage - (shift + shift))))
    ((strictJointDoubledTimeMixedTarget shift vector).roots.map
      (centralStrictLowerCenteredStageRoot
        (base + (shift + shift))
        (fixedStage - (shift + shift))))
    ((strictJointDoubledTimeMixedSource shift vector).roots.map
      (centralStrictUpperCenteredStageRoot
        (base + (shift + shift))
        (fixedStage - (shift + shift))))
    ((strictJointDoubledTimeMixedTarget shift vector).roots.map
      (centralStrictUpperCenteredStageRoot
        (base + (shift + shift))
        (fixedStage - (shift + shift))))]
  · rw [strictJointDoubledTimeMixedJointSelectedCenteredRoots_eq
      hstage vector]
  · unfold strictJointDoubledTimeMixedSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
    simp only [List.length_map]
  · unfold strictJointDoubledTimeMixedTarget
    simp only [timeTranslateStrictJointCylinderVector_roots,
      List.length_map]
  · unfold strictJointDoubledTimeMixedSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
    simp only [List.length_map]

#print axioms centralStrictLowerCanonicalRoot_transportBase_eq
#print axioms strictJointDoubledTimeMixedJointLowerCenteredRoot_eq
#print axioms strictJointDoubledTimeMixedJointSelectedCenteredRoots_eq
#print axioms projectedFourBlockCylinderEvent_eq
#print axioms strictJointDoubledTimeMixedJointCenteredEvent_eq_signedMixed

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointFixedStageRecoding
