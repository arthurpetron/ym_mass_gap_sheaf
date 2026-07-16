/-
# Finite-stage signed recoding and the translated-law frontier

The doubled-time strict chart has already been recoded into a signed-centered
chart whose absolute plaquette supports are spatial translates of the target
supports.  This file records the strongest consequence available before any
new physical law is supplied:

* the marked-root Boolean event is transported exactly by a constructive
  preimage-family recoding at every finite stage; and
* this support recoding is not the literal presentation translation used by
  the existing common-refinement theorem.

The remaining input is therefore stated at the law, rather than event,
level.  A dyadically decaying comparison modulus for the two rational stage
laws is sufficient for equality of their constructive-real limits.  No
finite-cylinder event identity is postulated.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedLawFrontier

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4SignedCenteredFiniteColimitDescent
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

/-! ## 1. Exact finite-stage event recoding -/

/-- A constructive existential witness for everything that support
translation implies at one finite marked-root stage.  The event identity is
deliberately between the target family and a recoded preimage family; it is
not equality of the two events on the same ambient family. -/
def SignedCenteredFiniteStageSupportTranslationRecoding
    (shift : SignedZ4Vector)
    (source target : SignedCenteredCylinderPresentation) : Prop :=
  ∃ recode : List Nat → List Nat,
    source.predicate = target.predicate ∧
    target.chart.roots = source.chart.roots.map recode ∧
    (∀ root, root ∈ source.chart.roots →
      ∀ plaquette : SignedZ4Plaq,
        plaquette ∈ target.chart.rootSupport (recode root) ↔
          plaquette ∈
            (source.chart.rootSupport root).map
              (signedTranslatePlaquette shift)) ∧
    ∀ targetFamily : List (List Nat),
      cylinderEvent target.chart.roots target.predicate targetFamily =
        cylinderEvent source.chart.roots source.predicate
          (markedPreimageFamily source.chart.roots [] recode targetFamily)

/-- Same predicate plus translated support gives an exact marked-family
preimage recoding of the finite Boolean event.  This is the strongest generic
finite-stage statement furnished by the current syntax alone. -/
theorem signedCenteredFiniteStageSupportTranslationRecoding_of_supportTranslated
    {shift : SignedZ4Vector}
    {source target : SignedCenteredCylinderPresentation}
    (hpredicate : source.predicate = target.predicate)
    (hsupport : SignedCenteredChartSupportTranslated
      shift source.chart target.chart) :
    SignedCenteredFiniteStageSupportTranslationRecoding
      shift source target := by
  rcases hsupport with ⟨recode, hroots, hsupport⟩
  refine ⟨recode, hpredicate, hroots, hsupport, ?_⟩
  intro targetFamily
  unfold cylinderEvent
  rw [hroots, ← hpredicate]
  exact congrArg source.predicate
    (familyOccurrenceFingerprint_markedPreimage_left
      source.chart.roots [] recode targetFamily).symm

/-- The strict doubled-time source and translated target have the exact
finite-stage support/event recoding, with no new law hypothesis. -/
theorem strictJointDoubledTime_signedFiniteStageSupportTranslationRecoding
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    SignedCenteredFiniteStageSupportTranslationRecoding
      (signedNatSpatialShift shift)
      (strictJointDoubledTimeMixedSignedPresentation
        base shift stage roots predicate hstage hroots)
      (timeTranslatedStrictJointSignedPresentation
        base shift stage roots predicate hroots) := by
  exact
    signedCenteredFiniteStageSupportTranslationRecoding_of_supportTranslated
      (shift := signedNatSpatialShift shift)
      (source := strictJointDoubledTimeMixedSignedPresentation
        base shift stage roots predicate hstage hroots)
      (target := timeTranslatedStrictJointSignedPresentation
        base shift stage roots predicate hroots)
      rfl
      (timeTranslatedStrictJointSignedChart_supportTranslated
        hstage hroots)

/-! ## 2. Literal translation is a different representation operation -/

/-- Forgetting the signed center makes literal presentation translation
invisible to the historical finite-cylinder presentation. -/
@[simp] theorem signedCenteredFinitePresentation_translate_eq
    (shift : SignedZ4Vector)
    (presentation : SignedCenteredCylinderPresentation) :
    signedCenteredFinitePresentation (presentation.translate shift) =
      signedCenteredFinitePresentation presentation := by
  rfl

/-- Presentation-level form of the radius obstruction: for positive shift,
the strict target presentation is not the literal translate of the mixed
source presentation. -/
theorem timeTranslatedStrictJointSignedPresentation_ne_literalTranslate
    {base shift stage : Nat} (hshift : 0 < shift)
    {roots : List (List Nat)}
    (hstage : shift + shift ≤ stage)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    timeTranslatedStrictJointSignedPresentation
        base shift stage roots predicate hroots ≠
      (strictJointDoubledTimeMixedSignedPresentation
        base shift stage roots predicate hstage hroots).translate
          (signedNatSpatialShift shift) := by
  intro hequal
  apply timeTranslatedStrictJointSignedChart_ne_literalTranslate
    hshift hstage hroots
  exact congrArg SignedCenteredCylinderPresentation.chart hequal

/-- Machine-checked separation of the two notions used by the APIs.  The
target is support-translated from the source but is not its literal
presentation translate, while literal translation itself is erased by the
historical finite-presentation functor. -/
theorem strictJointDoubledTime_signedSupportTranslation_separates_literal
    {base shift stage : Nat} (hshift : 0 < shift)
    {roots : List (List Nat)}
    (hstage : shift + shift ≤ stage)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let source := strictJointDoubledTimeMixedSignedPresentation
      base shift stage roots predicate hstage hroots
    let target := timeTranslatedStrictJointSignedPresentation
      base shift stage roots predicate hroots
    SignedCenteredChartSupportTranslated
        (signedNatSpatialShift shift) source.chart target.chart ∧
      target ≠ source.translate (signedNatSpatialShift shift) ∧
      signedCenteredFinitePresentation
          (source.translate (signedNatSpatialShift shift)) =
        signedCenteredFinitePresentation source := by
  dsimp only
  exact ⟨timeTranslatedStrictJointSignedChart_supportTranslated
      hstage hroots,
    timeTranslatedStrictJointSignedPresentation_ne_literalTranslate
      hshift hstage hroots predicate,
    signedCenteredFinitePresentation_translate_eq
      (signedNatSpatialShift shift)
      (strictJointDoubledTimeMixedSignedPresentation
        base shift stage roots predicate hstage hroots)⟩

/-! ## 3. Minimal law-covariance frontier and constructive-real descent -/

/-- The missing physical statement, expressed at exactly the strength used by
constructive-real descent.  For support-translated presentations in the
anchor corridor, their rational finite-volume laws differ by the existing
dyadic comparison envelope.  The comparison is with the literal translate
of the source so its geometric meaning remains explicit.

Unlike `SignedCenteredSupportTranslationDescent`, this does not assert that
two translated cylinder events are the same Boolean event after
zero-extension. -/
def SignedCenteredSupportTranslationLawCovariance : Prop :=
  ∀ {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (_ : coupling ≤ anchorCoupling)
    (shift : SignedZ4Vector)
    (source target : SignedCenteredCylinderPresentation),
    source.predicate = target.predicate →
    SignedCenteredChartSupportTranslated
      shift source.chart target.chart →
    SignedCenteredPresentationComparisonModulus
      coupling hcoupling target (source.translate shift)

/-- The law-covariance modulus closes the generic translated-support descent
to equality of the already constructed signed-centered values. -/
theorem signedCenteredValue_equiv_of_supportTranslationLawCovariance
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (hlaw : SignedCenteredSupportTranslationLawCovariance)
    (shift : SignedZ4Vector)
    (source target : SignedCenteredCylinderPresentation)
    (hpredicate : source.predicate = target.predicate)
    (hsupport : SignedCenteredChartSupportTranslated
      shift source.chart target.chart) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle target)
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle source) := by
  have hrepresentation :=
    couplingParametricSignedCenteredPresentationValue_equiv_of_comparison
      hcoupling hle
      (signedCenteredPresentationVolumeModulus_of_anchor
        hcoupling hle target)
      (signedCenteredPresentationVolumeModulus_of_anchor
        hcoupling hle (source.translate shift))
      (hlaw hcoupling hle shift source target hpredicate hsupport)
  have htranslation :=
    couplingParametricSignedCenteredPresentationValueAtAnchor_translate
      hcoupling hle shift source
  exact CReal.Equiv.trans hrepresentation htranslation

/-- Specialization of the law frontier to the strict doubled-time reflection
pair.  Once the comparison modulus is derived, no further chart, colimit, or
constructive-real argument remains. -/
theorem strictJointDoubledTime_signedValue_equiv_of_supportTranslationLawCovariance
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (hlaw : SignedCenteredSupportTranslationLawCovariance)
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (timeTranslatedStrictJointSignedPresentation
          base shift stage roots predicate hroots))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (strictJointDoubledTimeMixedSignedPresentation
          base shift stage roots predicate hstage hroots)) := by
  apply signedCenteredValue_equiv_of_supportTranslationLawCovariance
    hcoupling hle hlaw (signedNatSpatialShift shift)
    (strictJointDoubledTimeMixedSignedPresentation
      base shift stage roots predicate hstage hroots)
    (timeTranslatedStrictJointSignedPresentation
      base shift stage roots predicate hroots)
    rfl
  exact timeTranslatedStrictJointSignedChart_supportTranslated
    hstage hroots

#print axioms signedCenteredFiniteStageSupportTranslationRecoding_of_supportTranslated
#print axioms strictJointDoubledTime_signedFiniteStageSupportTranslationRecoding
#print axioms signedCenteredFinitePresentation_translate_eq
#print axioms timeTranslatedStrictJointSignedPresentation_ne_literalTranslate
#print axioms strictJointDoubledTime_signedSupportTranslation_separates_literal
#print axioms signedCenteredValue_equiv_of_supportTranslationLawCovariance
#print axioms strictJointDoubledTime_signedValue_equiv_of_supportTranslationLawCovariance

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedLawFrontier
