/-
# Cross-volume stability of the adjacent-even one-step marked event

The exact one-step EventLaw is stated in the corrected adjacent-even ambient
box.  This leaf transports its complete marked event to a fixed centered
source chart and applies the generic constructive cross-volume estimate.

The centered source is necessarily mixed: the lower block uses source base
`base` at stage `stage + 1`, whereas the one-step upper block uses source base
`base + 1` at stage `stage` after translating each source root once in time.
Both blocks have the same radius and retain a common protected distance
`stage` from the centered boundary.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
import YMGap.Continuum.Z4CouplingParametricCrossVolumeStability

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepVolumeComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalOccurrenceCofinal
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCrossVolumeStability
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The mixed centered source chart -/

/-- The two centered schedules have literally the same ambient radius. -/
theorem adjacentEvenOneStepRadius_eq (base stage : Nat) :
    strictQueryBase base + (stage + 1) =
      strictQueryBase (base + 1) + stage := by
  unfold strictQueryBase uniformPaddedBase
  omega

/-- Source-ordered lower roots at stage `stage + 1`, followed by source-ordered
one-step upper roots at transformed base `base + 1` and stage `stage`. -/
def adjacentEvenOneStepCenteredRoots
    (base stage : Nat) (roots : List (List Nat)) : List (List Nat) :=
  roots.map (centralStrictLowerCenteredStageRoot base (stage + 1)) ++
    roots.map (fun root =>
      centralStrictUpperCenteredStageRoot (base + 1) stage
        (timeShiftCanonicalRoot 1 base root))

@[simp] theorem adjacentEvenOneStepCenteredRoots_length
    (base stage : Nat) (roots : List (List Nat)) :
    (adjacentEvenOneStepCenteredRoots base stage roots).length =
      roots.length + roots.length := by
  simp [adjacentEvenOneStepCenteredRoots]

theorem adjacentEvenOneStepCenteredLowerRoot_canonical
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictLowerCenteredStageRoot base (stage + 1) root ∈
      canonicalSurfacePolymers
        (centeredBoxBase (strictQueryBase (base + 1) + stage)) := by
  have hsource := centralStrictLowerCenteredSourceRoot_canonical hroot
  have hshifted := uniformShiftCanonicalRoot_canonical
    (padding := stage + 1) hsource
  rw [strictJointCenteredStageBase_eq,
    adjacentEvenOneStepRadius_eq base stage] at hshifted
  exact hshifted

theorem adjacentEvenOneStepCenteredUpperRoot_canonical
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictUpperCenteredStageRoot (base + 1) stage
        (timeShiftCanonicalRoot 1 base root) ∈
      canonicalSurfacePolymers
        (centeredBoxBase (strictQueryBase (base + 1) + stage)) := by
  have htranslated := timeShiftCanonicalRoot_canonical
    (shift := 1) hroot
  have hsource := centralStrictUpperCenteredSourceRoot_canonical htranslated
  have hshifted := uniformShiftCanonicalRoot_canonical
    (padding := stage) hsource
  rw [strictJointCenteredStageBase_eq] at hshifted
  exact hshifted

theorem adjacentEvenOneStepCenteredRoots_canonical
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ adjacentEvenOneStepCenteredRoots base stage roots →
      target ∈ canonicalSurfacePolymers
        (centeredBoxBase (strictQueryBase (base + 1) + stage)) := by
  intro target htarget
  rcases List.mem_append.mp htarget with hlower | hupper
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hlower
    exact adjacentEvenOneStepCenteredLowerRoot_canonical
      (hroots root hroot)
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hupper
    exact adjacentEvenOneStepCenteredUpperRoot_canonical
      (hroots root hroot)

/-! ## 2. A common protected inner box -/

theorem adjacentEvenOneStepLowerInner_le_commonInner
    (base stage : Nat) :
    strictJointCenteredInner base (stage + 1) ≤
      strictJointCenteredInner (base + 1) stage := by
  unfold strictJointCenteredInner strictJointCenteredSourceBase
    centeredBoxBase strictQueryBase uniformPaddedBase
  omega

theorem adjacentEvenOneStepCenteredLowerRoot_inside_originBox
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    PolymerInsideBox (strictJointCenteredInner (base + 1) stage)
      (centeredBoxBase (strictQueryBase (base + 1) + stage))
      (centralStrictLowerCenteredStageRoot base (stage + 1) root) := by
  have hsingleton : ∀ source, source ∈ [root] →
      source ∈ canonicalSurfacePolymers base := by
    intro source hsource
    rw [List.mem_singleton] at hsource
    subst source
    exact hroot
  have hinside :=
    centralStrictJointCenteredStageRoots_inside_originBox
      (base := base) (stage := stage + 1) (roots := [root]) hsingleton
      (centralStrictLowerCenteredStageRoot base (stage + 1) root)
      (by
        rw [centralStrictJointCenteredStageRoots_split]
        apply List.mem_append_left
        simp)
  rw [adjacentEvenOneStepRadius_eq base stage] at hinside
  intro plaquette hplaquette
  exact boxPlaquettes_mono
    (adjacentEvenOneStepLowerInner_le_commonInner base stage)
    (hinside plaquette hplaquette)

theorem adjacentEvenOneStepCenteredUpperRoot_inside_originBox
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    PolymerInsideBox (strictJointCenteredInner (base + 1) stage)
      (centeredBoxBase (strictQueryBase (base + 1) + stage))
      (centralStrictUpperCenteredStageRoot (base + 1) stage
        (timeShiftCanonicalRoot 1 base root)) := by
  have htranslated := timeShiftCanonicalRoot_canonical
    (shift := 1) hroot
  have hsingleton : ∀ source,
      source ∈ [timeShiftCanonicalRoot 1 base root] →
        source ∈ canonicalSurfacePolymers (base + 1) := by
    intro source hsource
    rw [List.mem_singleton] at hsource
    subst source
    exact htranslated
  exact centralStrictJointCenteredStageRoots_inside_originBox
    (base := base + 1) (stage := stage)
    (roots := [timeShiftCanonicalRoot 1 base root]) hsingleton
    (centralStrictUpperCenteredStageRoot (base + 1) stage
      (timeShiftCanonicalRoot 1 base root))
    (by
      rw [centralStrictJointCenteredStageRoots_split]
      apply List.mem_append_right
      simp)

theorem adjacentEvenOneStepCenteredRoots_inside_originBox
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ adjacentEvenOneStepCenteredRoots base stage roots →
      PolymerInsideBox (strictJointCenteredInner (base + 1) stage)
        (centeredBoxBase (strictQueryBase (base + 1) + stage)) target := by
  intro target htarget
  rcases List.mem_append.mp htarget with hlower | hupper
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hlower
    exact adjacentEvenOneStepCenteredLowerRoot_inside_originBox
      (hroots root hroot)
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hupper
    exact adjacentEvenOneStepCenteredUpperRoot_inside_originBox
      (hroots root hroot)

/-! ## 3. Exact transport to the adjacent-even roots -/

theorem adjacentEvenOneStepCenteredBase_le_ambient
    (base stage : Nat) :
    centeredBoxBase (strictQueryBase (base + 1) + stage) ≤
      adjacentEvenAmbient (strictQueryBase (base + 1) + stage) :=
  Nat.le_trans
    (strictJointCenteredStageBase_le_centralAmbient (base + 1) stage)
    (centralAmbient_le_adjacentEvenAmbient
      (strictQueryBase (base + 1) + stage))

theorem adjacentEvenStrictLowerCanonicalRoot_eq_transport_centeredOneStep
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    adjacentEvenStrictLowerCanonicalRoot
        (strictQueryBase (base + 1) + stage) base root =
      transportPolymer
        (centeredBoxBase (strictQueryBase (base + 1) + stage))
        (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))
        (centralStrictLowerCenteredStageRoot base (stage + 1) root) := by
  have hmiddle :=
    centralStrictLowerCanonicalRoot_eq_transport_centeredStage
      (base := base) (stage := stage + 1) hroot
  rw [adjacentEvenOneStepRadius_eq base stage] at hmiddle
  unfold adjacentEvenStrictLowerCanonicalRoot
  rw [hmiddle]
  exact transportPolymer_trans
    (strictJointCenteredStageBase_le_centralAmbient (base + 1) stage)
    (centralAmbient_le_adjacentEvenAmbient
      (strictQueryBase (base + 1) + stage))
    (adjacentEvenOneStepCenteredLowerRoot_canonical hroot)

theorem adjacentEvenStrictUpperCanonicalRoot_eq_transport_centeredOneStep
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    adjacentEvenStrictUpperCanonicalRoot
        (strictQueryBase (base + 1) + stage) base root =
      transportPolymer
        (centeredBoxBase (strictQueryBase (base + 1) + stage))
        (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))
        (centralStrictUpperCenteredStageRoot (base + 1) stage
          (timeShiftCanonicalRoot 1 base root)) := by
  have htranslated := timeShiftCanonicalRoot_canonical
    (shift := 1) hroot
  have hmiddle :=
    centralStrictUpperCanonicalRoot_eq_transport_centeredStage
      (base := base + 1) (stage := stage) htranslated
  unfold adjacentEvenStrictUpperCanonicalRoot
  rw [hmiddle]
  exact transportPolymer_trans
    (strictJointCenteredStageBase_le_centralAmbient (base + 1) stage)
    (centralAmbient_le_adjacentEvenAmbient
      (strictQueryBase (base + 1) + stage))
    (adjacentEvenOneStepCenteredUpperRoot_canonical hroot)

theorem adjacentEvenStrictJointCylinderRoots_eq_transported_centeredOneStep
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    adjacentEvenStrictJointCylinderRoots
        (strictQueryBase (base + 1) + stage) base roots =
      transportedCylinderRoots
        (centeredBoxBase (strictQueryBase (base + 1) + stage))
        (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))
        (adjacentEvenOneStepCenteredRoots base stage roots) := by
  unfold adjacentEvenStrictJointCylinderRoots
    adjacentEvenStrictLowerCylinderRoots
    adjacentEvenStrictUpperCylinderRoots
    adjacentEvenOneStepCenteredRoots transportedCylinderRoots
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact adjacentEvenStrictLowerCanonicalRoot_eq_transport_centeredOneStep
      (hroots root hroot)
  · apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact adjacentEvenStrictUpperCanonicalRoot_eq_transport_centeredOneStep
      (hroots root hroot)

/-! ## 4. Equality of the complete large and transported marked events -/

theorem adjacentEvenStrictJointSlabEvent_eq_transportedCenteredOneStep
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let hsmall := adjacentEvenOneStepCenteredBase_le_ambient base stage
    let hcentered := adjacentEvenOneStepCenteredRoots_canonical hroots
    slabMarkedCylinderEvent
        (adjacentEvenStrictJointCanonicalAtoms
          (strictQueryBase (base + 1) + stage) base roots
          (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots)
        predicate =
      markedCylinderEvent
        (transportedCanonicalCylinderAtoms hsmall
          (adjacentEvenOneStepCenteredRoots base stage roots) hcentered)
        predicate := by
  dsimp only
  unfold slabMarkedCylinderEvent markedCylinderEvent
  apply congrArg (fun rawRoots => cylinderEvent rawRoots predicate)
  calc
    (adjacentEvenStrictJointCanonicalAtoms
        (strictQueryBase (base + 1) + stage) base roots
        (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots).map
          Subtype.val =
        adjacentEvenStrictJointCylinderRoots
          (strictQueryBase (base + 1) + stage) base roots :=
      adjacentEvenStrictJointCanonicalAtoms_values
        (strictQueryBase (base + 1) + stage) base roots
        (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots
    _ = transportedCylinderRoots
          (centeredBoxBase (strictQueryBase (base + 1) + stage))
          (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))
          (adjacentEvenOneStepCenteredRoots base stage roots) :=
      adjacentEvenStrictJointCylinderRoots_eq_transported_centeredOneStep
        hroots
    _ = (transportedCanonicalCylinderAtoms
          (adjacentEvenOneStepCenteredBase_le_ambient base stage)
          (adjacentEvenOneStepCenteredRoots base stage roots)
          (adjacentEvenOneStepCenteredRoots_canonical hroots)).map
            Subtype.val :=
      (transportedCanonicalCylinderAtoms_values
        (adjacentEvenOneStepCenteredBase_le_ambient base stage)
        (adjacentEvenOneStepCenteredRoots base stage roots)
        (adjacentEvenOneStepCenteredRoots_canonical hroots)).symm

/-! ## 5. Compatible and literal physical cross-volume bounds -/

theorem couplingParametricKCompatibleAdjacentEvenStrictJoint_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))
            (slabMarkedCylinderEvent
              (adjacentEvenStrictJointCanonicalAtoms
                (strictQueryBase (base + 1) + stage) base roots
                (Nat.le_add_right (strictQueryBase (base + 1)) stage)
                hroots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase (base + 1) + stage))
            (sourceCylinderEvent
              (adjacentEvenOneStepCenteredRoots base stage roots)
              predicate)) ≤
      spinSummedCylinderBoundaryEpsilon
        (2 * roots.length) stage := by
  let hsmall := adjacentEvenOneStepCenteredBase_le_ambient base stage
  let centeredRoots := adjacentEvenOneStepCenteredRoots base stage roots
  let hcentered : ∀ root, root ∈ centeredRoots →
      root ∈ canonicalSurfacePolymers
        (centeredBoxBase (strictQueryBase (base + 1) + stage)) :=
    adjacentEvenOneStepCenteredRoots_canonical hroots
  have hbound :=
    couplingParametricKCompatibleCylinderProbability_cross_volume_abs_sub_le
      hcoupling hle cutoff hsmall centeredRoots hcentered predicate
      (adjacentEvenOneStepCenteredRoots_inside_originBox hroots)
      (strictJointCenteredInner_add_distance (base + 1) stage)
  have hevent :=
    adjacentEvenStrictJointSlabEvent_eq_transportedCenteredOneStep
      (stage := stage) hroots predicate
  have hlength : centeredRoots.length = 2 * roots.length := by
    have hraw := adjacentEvenOneStepCenteredRoots_length base stage roots
    dsimp only [centeredRoots]
    omega
  rw [← hevent] at hbound
  simpa only [centeredRoots, hlength] using hbound

theorem couplingPhysicalAdjacentEvenStrictJoint_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingKFamilyEventProbability coupling hcoupling cutoff
            (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))
            (slabMarkedCylinderEvent
              (adjacentEvenStrictJointCanonicalAtoms
                (strictQueryBase (base + 1) + stage) base roots
                (Nat.le_add_right (strictQueryBase (base + 1)) stage)
                hroots)
              predicate) -
          couplingKFamilyEventProbability coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase (base + 1) + stage))
            (sourceCylinderEvent
              (adjacentEvenOneStepCenteredRoots base stage roots)
              predicate)) ≤
      spinSummedCylinderBoundaryEpsilon
        (2 * roots.length) stage := by
  let largeEvent := slabMarkedCylinderEvent
    (adjacentEvenStrictJointCanonicalAtoms
      (strictQueryBase (base + 1) + stage) base roots
      (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots)
    predicate
  let smallEvent := sourceCylinderEvent
    (adjacentEvenOneStepCenteredRoots base stage roots) predicate
  have hbridge := couplingPhysicalAdjacentDifference_eqv_compatible
    (large := adjacentEvenAmbient (strictQueryBase (base + 1) + stage))
    (small := centeredBoxBase (strictQueryBase (base + 1) + stage))
    hcoupling cutoff largeEvent smallEvent
  have hcompatible :=
    couplingParametricKCompatibleAdjacentEvenStrictJoint_cross_centered_abs_sub_le
      (stage := stage) hcoupling hle cutoff hroots predicate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hbridge))
    (by simpa only [largeEvent, smallEvent] using hcompatible)

/-- The centered mixed event corresponding to the source-ordered pair event. -/
def adjacentEvenOneStepCenteredPairEvent
    (base stage : Nat) (roots : List (List Nat))
    (left right : List Bool) : List (List Nat) → Bool :=
  sourceCylinderEvent (adjacentEvenOneStepCenteredRoots base stage roots)
    (centralStrictJointPairPredicate roots.length left right)

theorem couplingPhysicalAdjacentEvenStrictJointPair_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    Q'.abs
        (couplingKFamilyEventProbability coupling hcoupling cutoff
            (adjacentEvenAmbient (strictQueryBase (base + 1) + stage))
            (adjacentEvenStrictJointPairFamilyEvent
              (strictQueryBase (base + 1) + stage)
              base roots left right) -
          couplingKFamilyEventProbability coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase (base + 1) + stage))
            (adjacentEvenOneStepCenteredPairEvent
              base stage roots left right)) ≤
      spinSummedCylinderBoundaryEpsilon
        (2 * roots.length) stage := by
  have hbound :=
    couplingPhysicalAdjacentEvenStrictJoint_cross_centered_abs_sub_le
      (stage := stage) hcoupling hle cutoff hroots
      (centralStrictJointPairPredicate roots.length left right)
  rw [adjacentEvenStrictJointMarkedCylinderEvent_eq
    (strictQueryBase (base + 1) + stage) base roots
    (Nat.le_add_right (strictQueryBase (base + 1)) stage)
    hroots left right] at hbound
  simpa only [adjacentEvenOneStepCenteredPairEvent] using hbound

#print axioms adjacentEvenOneStepRadius_eq
#print axioms adjacentEvenOneStepCenteredRoots_canonical
#print axioms adjacentEvenOneStepCenteredRoots_inside_originBox
#print axioms adjacentEvenStrictLowerCanonicalRoot_eq_transport_centeredOneStep
#print axioms adjacentEvenStrictUpperCanonicalRoot_eq_transport_centeredOneStep
#print axioms adjacentEvenStrictJointCylinderRoots_eq_transported_centeredOneStep
#print axioms adjacentEvenStrictJointSlabEvent_eq_transportedCenteredOneStep
#print axioms couplingParametricKCompatibleAdjacentEvenStrictJoint_cross_centered_abs_sub_le
#print axioms couplingPhysicalAdjacentEvenStrictJoint_cross_centered_abs_sub_le
#print axioms couplingPhysicalAdjacentEvenStrictJointPair_cross_centered_abs_sub_le

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepVolumeComparison
