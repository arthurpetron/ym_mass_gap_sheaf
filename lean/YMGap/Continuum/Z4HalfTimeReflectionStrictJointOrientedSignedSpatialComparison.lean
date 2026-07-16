/-
# Oriented two-presentation signed spatial comparison

The doubled-time signed-spatial descent was originally wrapped around one
root list used on both sides of a reflection diagonal.  Its quantitative
finite-volume theorem is more general: it compares any signed-centered
presentation with the presentation obtained by applying the canonical
spatial root transport, without inspecting the Boolean predicate.

This file removes the diagonal wrapper.  The source chart has lower roots
from one strict presentation and upper roots from a second presentation.
After a simultaneous time translation by `shift`, its target chart has the
corresponding translated lower and upper roots.  Root by root, the existing
doubled-time geometry identifies the target with the pure spatial translate
of the source.  The generic signed-spatial boundary estimate therefore gives
an explicit comparison modulus, and hence equality of the two constructive-
real signed presentation values.

This is the geometric/law component needed for an oriented matrix
coefficient.  It does not by itself identify either signed value with a
strict-cylinder bilinear form, and it does not assert symmetry after swapping
the two input presentations.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialDescent

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedSignedSpatialComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialComparison
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialStageRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

/-! ## 1. Heterogeneous mixed and translated root lists -/

/-- Lower roots from `leftRoots`, upper roots from `rightRoots`, in the
aligned mixed signed chart at source stage `stage`. -/
def orientedDoubledTimeMixedCenteredRoots
    (base shift stage : Nat)
    (leftRoots rightRoots : List (List Nat)) : List (List Nat) :=
  leftRoots.map
      (strictJointDoubledTimeMixedCenteredLowerRoot base shift stage) ++
    rightRoots.map
      (strictJointDoubledTimeMixedCenteredUpperRoot base shift stage)

@[simp] theorem orientedDoubledTimeMixedCenteredRoots_length
    (base shift stage : Nat)
    (leftRoots rightRoots : List (List Nat)) :
    (orientedDoubledTimeMixedCenteredRoots
      base shift stage leftRoots rightRoots).length =
        leftRoots.length + rightRoots.length := by
  simp [orientedDoubledTimeMixedCenteredRoots]

/-- The mixed heterogeneous root list is canonical in the same source box
as the diagonal chart. -/
theorem orientedDoubledTimeMixedCenteredRoots_canonical
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {leftRoots rightRoots : List (List Nat)}
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target,
      target ∈ orientedDoubledTimeMixedCenteredRoots
          base shift stage leftRoots rightRoots →
        target ∈ canonicalSurfacePolymers
          (centeredBoxBase (strictQueryBase base + stage)) := by
  intro target htarget
  rcases List.mem_append.mp htarget with hlower | hupper
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hlower
    exact strictJointDoubledTimeMixedCenteredLowerRoot_canonical
      (shift := shift) (stage := stage) (hleft root hroot)
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hupper
    exact strictJointDoubledTimeMixedCenteredUpperRoot_canonical
      hstage (hright root hroot)

/-- The actual simultaneously translated heterogeneous lower/upper chart. -/
def orientedTimeTranslatedCenteredRoots
    (base shift stage : Nat)
    (leftRoots rightRoots : List (List Nat)) : List (List Nat) :=
  leftRoots.map
      (fun root => centralStrictLowerCenteredStageRoot
        (base + shift) stage (timeShiftCanonicalRoot shift base root)) ++
    rightRoots.map
      (fun root => centralStrictUpperCenteredStageRoot
        (base + shift) stage (timeShiftCanonicalRoot shift base root))

/-- Root-list form of heterogeneous doubled-time geometry: simultaneous
translation of the two arguments is a single pure spatial translation of
the oriented mixed chart. -/
theorem orientedTimeTranslatedCenteredRoots_eq_spatialMixed
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {leftRoots rightRoots : List (List Nat)}
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    orientedTimeTranslatedCenteredRoots
        base shift stage leftRoots rightRoots =
      (orientedDoubledTimeMixedCenteredRoots
        base shift stage leftRoots rightRoots).map
          (spatialShiftCanonicalRoot shift
            (centeredBoxBase (strictQueryBase base + stage))) := by
  unfold orientedTimeTranslatedCenteredRoots
    orientedDoubledTimeMixedCenteredRoots
  rw [List.map_append, List.map_map, List.map_map]
  have hlower :
      leftRoots.map
          (fun root => centralStrictLowerCenteredStageRoot
            (base + shift) stage
              (timeShiftCanonicalRoot shift base root)) =
        leftRoots.map
          (spatialShiftCanonicalRoot shift
              (centeredBoxBase (strictQueryBase base + stage)) ∘
            strictJointDoubledTimeMixedCenteredLowerRoot
              base shift stage) := by
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact timeTranslatedStrictJointLowerCenteredRoot_eq_spatialMixed
      hstage (hleft root hroot)
  have hupper :
      rightRoots.map
          (fun root => centralStrictUpperCenteredStageRoot
            (base + shift) stage
              (timeShiftCanonicalRoot shift base root)) =
        rightRoots.map
          (spatialShiftCanonicalRoot shift
              (centeredBoxBase (strictQueryBase base + stage)) ∘
            strictJointDoubledTimeMixedCenteredUpperRoot
              base shift stage) := by
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact timeTranslatedStrictJointUpperCenteredRoot_eq_spatialMixed
      hstage (hright root hroot)
  rw [hlower, hupper]

/-- Canonicality of the physical translated heterogeneous root list. -/
theorem orientedTimeTranslatedCenteredRoots_canonical
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {leftRoots rightRoots : List (List Nat)}
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target,
      target ∈ orientedTimeTranslatedCenteredRoots
          base shift stage leftRoots rightRoots →
        target ∈ canonicalSurfacePolymers
          (centeredBoxBase
            ((strictQueryBase base + stage) + shift)) := by
  have hsource := orientedDoubledTimeMixedCenteredRoots_canonical
    hstage hleft hright
  have htarget := signedSpatialTargetRoots_canonical
    (shift := shift) hsource
  rw [orientedTimeTranslatedCenteredRoots_eq_spatialMixed
      hstage hleft hright]
  intro target htargetMem
  have hcanonical := htarget target htargetMem
  rw [signedSpatialTargetBase,
    uniformPaddedBase_centeredBoxBase] at hcanonical
  exact hcanonical

/-! ## 2. Signed charts and exact spatial recoding -/

def orientedDoubledTimeMixedSignedChart
    (base shift stage : Nat)
    (leftRoots rightRoots : List (List Nat))
    (hstage : shift + shift ≤ stage)
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    SignedCenteredCylinderChart where
  center := signedNaturalCornerCenter (strictQueryBase base + stage)
  radius := strictQueryBase base + stage
  roots := orientedDoubledTimeMixedCenteredRoots
    base shift stage leftRoots rightRoots
  rootsCanonical :=
    orientedDoubledTimeMixedCenteredRoots_canonical hstage hleft hright

def orientedTimeTranslatedSignedChart
    (base shift stage : Nat)
    (leftRoots rightRoots : List (List Nat))
    (hstage : shift + shift ≤ stage)
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    SignedCenteredCylinderChart where
  center := signedNaturalCornerCenter
    ((strictQueryBase base + stage) + shift)
  radius := (strictQueryBase base + stage) + shift
  roots := orientedTimeTranslatedCenteredRoots
    base shift stage leftRoots rightRoots
  rootsCanonical :=
    orientedTimeTranslatedCenteredRoots_canonical hstage hleft hright

/-- The target chart's numerical roots are exactly the generic signed-spatial
transport of the source chart's roots. -/
theorem orientedTimeTranslatedSignedChart_roots_eq_spatialTarget
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {leftRoots rightRoots : List (List Nat)}
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    (orientedTimeTranslatedSignedChart
        base shift stage leftRoots rightRoots
        hstage hleft hright).roots =
      signedSpatialTargetRoots
        (signedCenteredPresentationDiagonalBase
          ⟨orientedDoubledTimeMixedSignedChart
              base shift stage leftRoots rightRoots
              hstage hleft hright,
            fun _ => true⟩)
        shift
        (orientedDoubledTimeMixedSignedChart
          base shift stage leftRoots rightRoots
          hstage hleft hright).roots := by
  change orientedTimeTranslatedCenteredRoots
      base shift stage leftRoots rightRoots =
    signedSpatialTargetRoots
      (centeredBoxBase (strictQueryBase base + stage)) shift
      (orientedDoubledTimeMixedCenteredRoots
        base shift stage leftRoots rightRoots)
  exact orientedTimeTranslatedCenteredRoots_eq_spatialMixed
    hstage hleft hright

/-- The corresponding absolute signed supports are translated by the common
vector `(shift,shift,shift,0)`. -/
theorem orientedTimeTranslatedSignedChart_supportTranslated
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {leftRoots rightRoots : List (List Nat)}
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    SignedCenteredChartSupportTranslated
      (signedNatSpatialShift shift)
      (orientedDoubledTimeMixedSignedChart
        base shift stage leftRoots rightRoots hstage hleft hright)
      (orientedTimeTranslatedSignedChart
        base shift stage leftRoots rightRoots hstage hleft hright) := by
  let recode := spatialShiftCanonicalRoot shift
    (centeredBoxBase (strictQueryBase base + stage))
  refine ⟨recode, ?_, ?_⟩
  · exact orientedTimeTranslatedCenteredRoots_eq_spatialMixed
      hstage hleft hright
  · intro root hroot plaquette
    have hcanonical :=
      (orientedDoubledTimeMixedSignedChart
        base shift stage leftRoots rightRoots
        hstage hleft hright).rootsCanonical root hroot
    simpa only [SignedCenteredCylinderChart.rootSupport,
      orientedDoubledTimeMixedSignedChart,
      orientedTimeTranslatedSignedChart, recode] using
      (spatialShiftCanonicalRoot_absoluteSignedSupport_iff
        hcanonical plaquette)

/-! ## 3. Derived comparison modulus and constructive-real equality -/

def orientedDoubledTimeMixedSignedPresentation
    (base shift stage : Nat)
    (leftRoots rightRoots : List (List Nat))
    (predicate : List Bool → Bool)
    (hstage : shift + shift ≤ stage)
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    SignedCenteredCylinderPresentation :=
  ⟨orientedDoubledTimeMixedSignedChart
      base shift stage leftRoots rightRoots hstage hleft hright,
    predicate⟩

def orientedTimeTranslatedSignedPresentation
    (base shift stage : Nat)
    (leftRoots rightRoots : List (List Nat))
    (predicate : List Bool → Bool)
    (hstage : shift + shift ≤ stage)
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    SignedCenteredCylinderPresentation :=
  ⟨orientedTimeTranslatedSignedChart
      base shift stage leftRoots rightRoots hstage hleft hright,
    predicate⟩

/-- The already-derived signed-spatial finite-volume estimates apply to the
heterogeneous oriented chart without any new physical assumption. -/
theorem orientedSignedSpatialPresentationComparisonModulus
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {leftRoots rightRoots : List (List Nat)}
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    SignedCenteredPresentationComparisonModulus coupling hcoupling
      (orientedTimeTranslatedSignedPresentation
        base shift stage leftRoots rightRoots predicate
        hstage hleft hright)
      (orientedDoubledTimeMixedSignedPresentation
        base shift stage leftRoots rightRoots predicate
        hstage hleft hright) := by
  apply signedSpatialPresentationComparisonModulus_of_data
    hcoupling hle (shift := shift)
  · dsimp only [orientedTimeTranslatedSignedPresentation,
      orientedDoubledTimeMixedSignedPresentation,
      signedCenteredPresentationDiagonalBase,
      orientedTimeTranslatedSignedChart,
      orientedDoubledTimeMixedSignedChart,
      signedSpatialTargetBase]
    exact (uniformPaddedBase_centeredBoxBase
      (strictQueryBase base + stage) shift).symm
  · change orientedTimeTranslatedCenteredRoots
        base shift stage leftRoots rightRoots =
      signedSpatialTargetRoots
        (centeredBoxBase (strictQueryBase base + stage)) shift
        (orientedDoubledTimeMixedCenteredRoots
          base shift stage leftRoots rightRoots)
    exact orientedTimeTranslatedCenteredRoots_eq_spatialMixed
      hstage hleft hright
  · rfl

/-- Constructive-real equality of the oriented mixed signed cylinder and its
simultaneously translated target. -/
theorem orientedSignedSpatialValue_equiv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {leftRoots rightRoots : List (List Nat)}
    (hleft : ∀ root, root ∈ leftRoots →
      root ∈ canonicalSurfacePolymers base)
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (orientedTimeTranslatedSignedPresentation
          base shift stage leftRoots rightRoots predicate
          hstage hleft hright))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (orientedDoubledTimeMixedSignedPresentation
          base shift stage leftRoots rightRoots predicate
          hstage hleft hright)) := by
  let target := orientedTimeTranslatedSignedPresentation
    base shift stage leftRoots rightRoots predicate hstage hleft hright
  let source := orientedDoubledTimeMixedSignedPresentation
    base shift stage leftRoots rightRoots predicate hstage hleft hright
  have htarget := signedCenteredPresentationVolumeModulus_of_anchor
    hcoupling hle target
  have hsource := signedCenteredPresentationVolumeModulus_of_anchor
    hcoupling hle source
  have hcomparison : SignedCenteredPresentationComparisonModulus
      coupling hcoupling target source :=
    orientedSignedSpatialPresentationComparisonModulus
      hcoupling hle hstage hleft hright predicate
  exact couplingParametricSignedCenteredPresentationValue_equiv_of_comparison
    hcoupling hle htarget hsource hcomparison

#print axioms orientedDoubledTimeMixedCenteredRoots_canonical
#print axioms orientedTimeTranslatedCenteredRoots_eq_spatialMixed
#print axioms orientedTimeTranslatedCenteredRoots_canonical
#print axioms orientedTimeTranslatedSignedChart_supportTranslated
#print axioms orientedSignedSpatialPresentationComparisonModulus
#print axioms orientedSignedSpatialValue_equiv

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedSignedSpatialComparison
