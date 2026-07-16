/-
# Radius-indexed positive-time translation for strict cylinders

The global strict-cylinder semantic relation quantifies over every support
radius.  Positive-time translation is not known to preserve that global
relation at the small radii.  The exact geometric theorem instead gives an
honest indexed map: a presentation at `(base, radius)` is sent to one at
`(base + shift, radius + shift)`, and every target support is pulled back to
one source support at `radius`.

This module packages that fact as a quotient-free radius-indexed relation.  It
also records the finite normalized reflection bilinear and quadratic forms on
the indexed carrier, their presentation independence, positivity, and the
additive/rational-linear covariance genuinely inherited from presentation
translation.  There is no comparison with the unshifted form and no claim of
invariance, contraction, norm preservation, or a translation semigroup.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationSemanticDescent

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslation

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The radius-indexed semantic relation -/

/-- Pull a strict-cylinder coefficient table back to the complete support
space at one specified radius. -/
def strictJointCylinderRadiusCoefficient
    {base : Nat} (radius : Nat)
    (vector : StrictJointCylinderVector base) : List Nat → Q' :=
  centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base vector.roots)
    vector.coefficient

/-- Semantic equality at one support radius.  Unlike
`StrictJointCylinderVectorEquivalent`, this relation makes no assertion at
any other radius. -/
def StrictJointCylinderVectorEquivalentAtRadius
    {base : Nat} (radius : Nat)
    (left right : StrictJointCylinderVector base) : Prop :=
  ∀ support,
    strictJointCylinderRadiusCoefficient radius left support ≈
      strictJointCylinderRadiusCoefficient radius right support

theorem strictJointCylinderVectorEquivalentAtRadius_refl
    {base radius : Nat} (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalentAtRadius radius vector vector := by
  intro support
  exact Q'.eqv_refl _

theorem strictJointCylinderVectorEquivalentAtRadius_symm
    {base radius : Nat} {left right : StrictJointCylinderVector base}
    (h : StrictJointCylinderVectorEquivalentAtRadius radius left right) :
    StrictJointCylinderVectorEquivalentAtRadius radius right left := by
  intro support
  exact Q'.eqv_symm (h support)

theorem strictJointCylinderVectorEquivalentAtRadius_trans
    {base radius : Nat}
    {first middle last : StrictJointCylinderVector base}
    (hfirst : StrictJointCylinderVectorEquivalentAtRadius
      radius first middle)
    (hlast : StrictJointCylinderVectorEquivalentAtRadius
      radius middle last) :
    StrictJointCylinderVectorEquivalentAtRadius radius first last := by
  intro support
  exact Q'.eqv_trans _ _ _ (hfirst support) (hlast support)

theorem strictJointCylinderVectorEquivalentAtRadius_equivalence
    (base radius : Nat) :
    Equivalence
      (@StrictJointCylinderVectorEquivalentAtRadius base radius) :=
  ⟨strictJointCylinderVectorEquivalentAtRadius_refl,
    @strictJointCylinderVectorEquivalentAtRadius_symm base radius,
    @strictJointCylinderVectorEquivalentAtRadius_trans base radius⟩

theorem strictJointCylinderVectorEquivalentAtRadius_of_equivalent
    {base radius : Nat} {left right : StrictJointCylinderVector base}
    (h : StrictJointCylinderVectorEquivalent left right) :
    StrictJointCylinderVectorEquivalentAtRadius radius left right := by
  intro support
  exact h radius support

theorem strictJointCylinderVectorEquivalent_iff_forall_atRadius
    {base : Nat} {left right : StrictJointCylinderVector base} :
    StrictJointCylinderVectorEquivalent left right ↔
      ∀ radius,
        StrictJointCylinderVectorEquivalentAtRadius radius left right := by
  constructor
  · intro h radius
    exact strictJointCylinderVectorEquivalentAtRadius_of_equivalent h
  · intro h radius support
    exact h radius support

theorem strictJointCylinderVectorEquivalentAtRadius_add
    {base radius : Nat}
    {left left' right right' : StrictJointCylinderVector base}
    (hleft : StrictJointCylinderVectorEquivalentAtRadius
      radius left left')
    (hright : StrictJointCylinderVectorEquivalentAtRadius
      radius right right') :
    StrictJointCylinderVectorEquivalentAtRadius radius
      (left.add right) (left'.add right') := by
  intro support
  exact Q'.eqv_trans _ _ _
    (StrictJointCylinderVector.add_coefficient_code
      left right radius support)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (hleft support) (hright support))
      (Q'.eqv_symm
        (StrictJointCylinderVector.add_coefficient_code
          left' right' radius support)))

theorem strictJointCylinderVectorEquivalentAtRadius_smul
    {base radius : Nat} (scalar : Q')
    {left right : StrictJointCylinderVector base}
    (h : StrictJointCylinderVectorEquivalentAtRadius radius left right) :
    StrictJointCylinderVectorEquivalentAtRadius radius
      (left.smul scalar) (right.smul scalar) := by
  intro support
  exact Q'.mul_eqv_congr_left _ _ _ (h support)

/-! ## 2. The correctly indexed positive-time map -/

/-- Positive-time translation respects semantic equality after enlarging the
support radius by exactly the translation distance.  The direction on
supports is contravariant: an arbitrary target support is reconstructed as
one source support shared by both presentations. -/
theorem timeTranslateStrictJointCylinderVector_equivalentAtRadius
    {base radius shift : Nat} (hbase : strictQueryBase base ≤ radius)
    {left right : StrictJointCylinderVector base}
    (h : StrictJointCylinderVectorEquivalentAtRadius radius left right) :
    StrictJointCylinderVectorEquivalentAtRadius (radius + shift)
      (timeTranslateStrictJointCylinderVector shift left)
      (timeTranslateStrictJointCylinderVector shift right) := by
  intro targetSupport
  change left.coefficient
      (centralStrictLocalQueryCode (radius + shift) (base + shift)
        (left.roots.map (timeShiftCanonicalRoot shift base))
        targetSupport) ≈
    right.coefficient
      (centralStrictLocalQueryCode (radius + shift) (base + shift)
        (right.roots.map (timeShiftCanonicalRoot shift base))
        targetSupport)
  rw [centralStrictLocalQueryCode_timeShift_completeLowerSupport
    hbase left.rootsCanonical targetSupport]
  rw [centralStrictLocalQueryCode_timeShift_completeLowerSupport
    hbase right.rootsCanonical targetSupport]
  exact h
    (centralSpatialPullbackLowerSupport radius shift
      (centralLowerSupportAmbientFaces (radius + shift) targetSupport))

/-! ## 3. Exact finite reflection forms on one indexed carrier -/

def strictJointCylinderRadiusReflectionQuadratic
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius : Nat) {base : Nat}
    (vector : StrictJointCylinderVector base) : Q' :=
  centralNormalizedSupportReflectionQuadratic
    coupling hcoupling cutoff radius
    (strictJointCylinderRadiusCoefficient radius vector)

def strictJointCylinderRadiusReflectionBilinear
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius : Nat) {base : Nat}
    (left right : StrictJointCylinderVector base) : Q' :=
  centralNormalizedSupportReflectionBilinear
    coupling hcoupling cutoff radius
    (strictJointCylinderRadiusCoefficient radius left)
    (strictJointCylinderRadiusCoefficient radius right)

theorem strictJointCylinderRadiusReflectionQuadratic_eqv_of_equivalent
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {cutoff radius base : Nat}
    {left right : StrictJointCylinderVector base}
    (h : StrictJointCylinderVectorEquivalentAtRadius radius left right) :
    strictJointCylinderRadiusReflectionQuadratic
        coupling hcoupling cutoff radius left ≈
      strictJointCylinderRadiusReflectionQuadratic
        coupling hcoupling cutoff radius right := by
  unfold strictJointCylinderRadiusReflectionQuadratic
  exact centralNormalizedSupportReflectionQuadratic_coefficient_eqv
    coupling hcoupling cutoff radius _ _ h

theorem strictJointCylinderRadiusReflectionBilinear_eqv_of_equivalent
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {cutoff radius base : Nat}
    {left left' right right' : StrictJointCylinderVector base}
    (hleft : StrictJointCylinderVectorEquivalentAtRadius
      radius left left')
    (hright : StrictJointCylinderVectorEquivalentAtRadius
      radius right right') :
    strictJointCylinderRadiusReflectionBilinear
        coupling hcoupling cutoff radius left right ≈
      strictJointCylinderRadiusReflectionBilinear
        coupling hcoupling cutoff radius left' right' := by
  unfold strictJointCylinderRadiusReflectionBilinear
  exact centralNormalizedSupportReflectionBilinear_coefficient_eqv
    coupling hcoupling cutoff radius _ _ _ _ hleft hright

theorem strictJointCylinderRadiusReflectionBilinear_self
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius : Nat) {base : Nat}
    (vector : StrictJointCylinderVector base) :
    strictJointCylinderRadiusReflectionBilinear
        coupling hcoupling cutoff radius vector vector ≈
      strictJointCylinderRadiusReflectionQuadratic
        coupling hcoupling cutoff radius vector := by
  unfold strictJointCylinderRadiusReflectionBilinear
    strictJointCylinderRadiusReflectionQuadratic
  exact centralNormalizedSupportReflectionBilinear_self
    coupling hcoupling cutoff radius _

theorem strictJointCylinderRadiusReflectionQuadratic_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius : Nat) {base : Nat}
    (vector : StrictJointCylinderVector base) :
    (0 : Q') ≤ strictJointCylinderRadiusReflectionQuadratic
      coupling hcoupling cutoff radius vector := by
  unfold strictJointCylinderRadiusReflectionQuadratic
  exact centralNormalizedSupportReflectionQuadratic_nonnegative
    coupling hcoupling cutoff radius _

theorem strictJointCylinderRadiusReflectionBilinear_add_left
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius : Nat) {base : Nat}
    (first second right : StrictJointCylinderVector base) :
    strictJointCylinderRadiusReflectionBilinear coupling hcoupling
        cutoff radius (first.add second) right ≈
      strictJointCylinderRadiusReflectionBilinear coupling hcoupling
          cutoff radius first right +
        strictJointCylinderRadiusReflectionBilinear coupling hcoupling
          cutoff radius second right := by
  let firstCoefficient := strictJointCylinderRadiusCoefficient radius first
  let secondCoefficient := strictJointCylinderRadiusCoefficient radius second
  let rightCoefficient := strictJointCylinderRadiusCoefficient radius right
  let combinedCoefficient :=
    strictJointCylinderRadiusCoefficient radius (first.add second)
  have hcombined : ∀ support,
      combinedCoefficient support ≈
        firstCoefficient support + secondCoefficient support := by
    intro support
    exact StrictJointCylinderVector.add_coefficient_code
      first second radius support
  have hcoefficient :=
    centralNormalizedSupportReflectionBilinear_coefficient_eqv
      coupling hcoupling cutoff radius
      combinedCoefficient
      (fun support => firstCoefficient support + secondCoefficient support)
      rightCoefficient rightCoefficient hcombined
      (fun support => Q'.eqv_refl _)
  have hadd := centralNormalizedSupportReflectionBilinear_add_left
    coupling hcoupling cutoff radius
    firstCoefficient secondCoefficient rightCoefficient
  exact Q'.eqv_trans _ _ _ hcoefficient hadd

theorem strictJointCylinderRadiusReflectionBilinear_smul_left
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius : Nat) {base : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    strictJointCylinderRadiusReflectionBilinear coupling hcoupling
        cutoff radius (left.smul scalar) right ≈
      scalar * strictJointCylinderRadiusReflectionBilinear
        coupling hcoupling cutoff radius left right := by
  let leftCoefficient := strictJointCylinderRadiusCoefficient radius left
  let rightCoefficient := strictJointCylinderRadiusCoefficient radius right
  let scaledCoefficient :=
    strictJointCylinderRadiusCoefficient radius (left.smul scalar)
  have hscaled : ∀ support,
      scaledCoefficient support ≈ scalar * leftCoefficient support := by
    intro support
    exact Q'.eqv_refl _
  have hcoefficient :=
    centralNormalizedSupportReflectionBilinear_coefficient_eqv
      coupling hcoupling cutoff radius
      scaledCoefficient (fun support => scalar * leftCoefficient support)
      rightCoefficient rightCoefficient hscaled
      (fun support => Q'.eqv_refl _)
  have hsmul := centralNormalizedSupportReflectionBilinear_smul_left
    coupling hcoupling cutoff radius scalar
    leftCoefficient rightCoefficient
  exact Q'.eqv_trans _ _ _ hcoefficient hsmul

theorem strictJointCylinderRadiusReflectionBilinear_add_right
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius : Nat) {base : Nat}
    (left first second : StrictJointCylinderVector base) :
    strictJointCylinderRadiusReflectionBilinear coupling hcoupling
        cutoff radius left (first.add second) ≈
      strictJointCylinderRadiusReflectionBilinear coupling hcoupling
          cutoff radius left first +
        strictJointCylinderRadiusReflectionBilinear coupling hcoupling
          cutoff radius left second := by
  let leftCoefficient := strictJointCylinderRadiusCoefficient radius left
  let firstCoefficient := strictJointCylinderRadiusCoefficient radius first
  let secondCoefficient := strictJointCylinderRadiusCoefficient radius second
  let combinedCoefficient :=
    strictJointCylinderRadiusCoefficient radius (first.add second)
  have hcombined : ∀ support,
      combinedCoefficient support ≈
        firstCoefficient support + secondCoefficient support := by
    intro support
    exact StrictJointCylinderVector.add_coefficient_code
      first second radius support
  have hcoefficient :=
    centralNormalizedSupportReflectionBilinear_coefficient_eqv
      coupling hcoupling cutoff radius
      leftCoefficient leftCoefficient
      combinedCoefficient
      (fun support => firstCoefficient support + secondCoefficient support)
      (fun support => Q'.eqv_refl _) hcombined
  have hadd := centralNormalizedSupportReflectionBilinear_add_right
    coupling hcoupling cutoff radius
    leftCoefficient firstCoefficient secondCoefficient
  exact Q'.eqv_trans _ _ _ hcoefficient hadd

theorem strictJointCylinderRadiusReflectionBilinear_smul_right
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius : Nat) {base : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    strictJointCylinderRadiusReflectionBilinear coupling hcoupling
        cutoff radius left (right.smul scalar) ≈
      scalar * strictJointCylinderRadiusReflectionBilinear
        coupling hcoupling cutoff radius left right := by
  let leftCoefficient := strictJointCylinderRadiusCoefficient radius left
  let rightCoefficient := strictJointCylinderRadiusCoefficient radius right
  let scaledCoefficient :=
    strictJointCylinderRadiusCoefficient radius (right.smul scalar)
  have hscaled : ∀ support,
      scaledCoefficient support ≈ scalar * rightCoefficient support := by
    intro support
    exact Q'.eqv_refl _
  have hcoefficient :=
    centralNormalizedSupportReflectionBilinear_coefficient_eqv
      coupling hcoupling cutoff radius
      leftCoefficient leftCoefficient
      scaledCoefficient (fun support => scalar * rightCoefficient support)
      (fun support => Q'.eqv_refl _) hscaled
  have hsmul := centralNormalizedSupportReflectionBilinear_smul_right
    coupling hcoupling cutoff radius scalar
    leftCoefficient rightCoefficient
  exact Q'.eqv_trans _ _ _ hcoefficient hsmul

/-! ## 4. Synchronized translated forms on the source indexed carrier -/

/-- The target finite bilinear form after synchronously translating both
source presentations.  This is a new indexed form, not asserted equal to the
source form. -/
def strictJointCylinderRadiusTimeTranslatedReflectionBilinear
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (left right : StrictJointCylinderVector base) : Q' :=
  strictJointCylinderRadiusReflectionBilinear coupling hcoupling cutoff
    (radius + shift)
    (timeTranslateStrictJointCylinderVector shift left)
    (timeTranslateStrictJointCylinderVector shift right)

/-- The target finite quadratic form after positive-time translation.  No
comparison with the unshifted quadratic is part of this definition. -/
def strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (vector : StrictJointCylinderVector base) : Q' :=
  strictJointCylinderRadiusReflectionQuadratic coupling hcoupling cutoff
    (radius + shift)
    (timeTranslateStrictJointCylinderVector shift vector)

theorem strictJointCylinderRadiusTimeTranslatedReflectionBilinear_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {cutoff radius shift base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    {left left' right right' : StrictJointCylinderVector base}
    (hleft : StrictJointCylinderVectorEquivalentAtRadius
      radius left left')
    (hright : StrictJointCylinderVectorEquivalentAtRadius
      radius right right') :
    strictJointCylinderRadiusTimeTranslatedReflectionBilinear
        coupling hcoupling cutoff radius shift left right ≈
      strictJointCylinderRadiusTimeTranslatedReflectionBilinear
        coupling hcoupling cutoff radius shift left' right' := by
  exact strictJointCylinderRadiusReflectionBilinear_eqv_of_equivalent
    coupling hcoupling
    (timeTranslateStrictJointCylinderVector_equivalentAtRadius hbase hleft)
    (timeTranslateStrictJointCylinderVector_equivalentAtRadius hbase hright)

theorem strictJointCylinderRadiusTimeTranslatedReflectionQuadratic_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {cutoff radius shift base : Nat}
    (hbase : strictQueryBase base ≤ radius)
    {left right : StrictJointCylinderVector base}
    (h : StrictJointCylinderVectorEquivalentAtRadius radius left right) :
    strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
        coupling hcoupling cutoff radius shift left ≈
      strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
        coupling hcoupling cutoff radius shift right := by
  exact strictJointCylinderRadiusReflectionQuadratic_eqv_of_equivalent
    coupling hcoupling
    (timeTranslateStrictJointCylinderVector_equivalentAtRadius hbase h)

theorem strictJointCylinderRadiusTimeTranslatedReflectionBilinear_self
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (vector : StrictJointCylinderVector base) :
    strictJointCylinderRadiusTimeTranslatedReflectionBilinear
        coupling hcoupling cutoff radius shift vector vector ≈
      strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
        coupling hcoupling cutoff radius shift vector := by
  exact strictJointCylinderRadiusReflectionBilinear_self
    coupling hcoupling cutoff (radius + shift)
    (timeTranslateStrictJointCylinderVector shift vector)

theorem strictJointCylinderRadiusTimeTranslatedReflectionQuadratic_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (vector : StrictJointCylinderVector base) :
    (0 : Q') ≤
      strictJointCylinderRadiusTimeTranslatedReflectionQuadratic
        coupling hcoupling cutoff radius shift vector := by
  exact strictJointCylinderRadiusReflectionQuadratic_nonnegative
    coupling hcoupling cutoff (radius + shift)
    (timeTranslateStrictJointCylinderVector shift vector)

theorem strictJointCylinderRadiusTimeTranslatedReflectionBilinear_add_left
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (first second right : StrictJointCylinderVector base) :
    strictJointCylinderRadiusTimeTranslatedReflectionBilinear
        coupling hcoupling cutoff radius shift (first.add second) right ≈
      strictJointCylinderRadiusTimeTranslatedReflectionBilinear
          coupling hcoupling cutoff radius shift first right +
        strictJointCylinderRadiusTimeTranslatedReflectionBilinear
          coupling hcoupling cutoff radius shift second right := by
  rw [strictJointCylinderRadiusTimeTranslatedReflectionBilinear,
    timeTranslateStrictJointCylinderVector_add]
  exact strictJointCylinderRadiusReflectionBilinear_add_left
    coupling hcoupling cutoff (radius + shift)
    (timeTranslateStrictJointCylinderVector shift first)
    (timeTranslateStrictJointCylinderVector shift second)
    (timeTranslateStrictJointCylinderVector shift right)

theorem strictJointCylinderRadiusTimeTranslatedReflectionBilinear_smul_left
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    strictJointCylinderRadiusTimeTranslatedReflectionBilinear
        coupling hcoupling cutoff radius shift (left.smul scalar) right ≈
      scalar * strictJointCylinderRadiusTimeTranslatedReflectionBilinear
        coupling hcoupling cutoff radius shift left right := by
  rw [strictJointCylinderRadiusTimeTranslatedReflectionBilinear,
    timeTranslateStrictJointCylinderVector_smul]
  exact strictJointCylinderRadiusReflectionBilinear_smul_left
    coupling hcoupling cutoff (radius + shift) scalar
    (timeTranslateStrictJointCylinderVector shift left)
    (timeTranslateStrictJointCylinderVector shift right)

theorem strictJointCylinderRadiusTimeTranslatedReflectionBilinear_add_right
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat}
    (left first second : StrictJointCylinderVector base) :
    strictJointCylinderRadiusTimeTranslatedReflectionBilinear
        coupling hcoupling cutoff radius shift left (first.add second) ≈
      strictJointCylinderRadiusTimeTranslatedReflectionBilinear
          coupling hcoupling cutoff radius shift left first +
        strictJointCylinderRadiusTimeTranslatedReflectionBilinear
          coupling hcoupling cutoff radius shift left second := by
  rw [strictJointCylinderRadiusTimeTranslatedReflectionBilinear,
    timeTranslateStrictJointCylinderVector_add]
  exact strictJointCylinderRadiusReflectionBilinear_add_right
    coupling hcoupling cutoff (radius + shift)
    (timeTranslateStrictJointCylinderVector shift left)
    (timeTranslateStrictJointCylinderVector shift first)
    (timeTranslateStrictJointCylinderVector shift second)

theorem strictJointCylinderRadiusTimeTranslatedReflectionBilinear_smul_right
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff radius shift : Nat) {base : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    strictJointCylinderRadiusTimeTranslatedReflectionBilinear
        coupling hcoupling cutoff radius shift left (right.smul scalar) ≈
      scalar * strictJointCylinderRadiusTimeTranslatedReflectionBilinear
        coupling hcoupling cutoff radius shift left right := by
  rw [strictJointCylinderRadiusTimeTranslatedReflectionBilinear,
    timeTranslateStrictJointCylinderVector_smul]
  exact strictJointCylinderRadiusReflectionBilinear_smul_right
    coupling hcoupling cutoff (radius + shift) scalar
    (timeTranslateStrictJointCylinderVector shift left)
    (timeTranslateStrictJointCylinderVector shift right)

#print axioms strictJointCylinderVectorEquivalentAtRadius_equivalence
#print axioms strictJointCylinderVectorEquivalent_iff_forall_atRadius
#print axioms strictJointCylinderVectorEquivalentAtRadius_add
#print axioms strictJointCylinderVectorEquivalentAtRadius_smul
#print axioms timeTranslateStrictJointCylinderVector_equivalentAtRadius
#print axioms strictJointCylinderRadiusReflectionBilinear_eqv_of_equivalent
#print axioms strictJointCylinderRadiusReflectionQuadratic_eqv_of_equivalent
#print axioms strictJointCylinderRadiusReflectionBilinear_self
#print axioms strictJointCylinderRadiusReflectionQuadratic_nonnegative
#print axioms strictJointCylinderRadiusTimeTranslatedReflectionBilinear_eqv
#print axioms strictJointCylinderRadiusTimeTranslatedReflectionQuadratic_eqv
#print axioms strictJointCylinderRadiusTimeTranslatedReflectionBilinear_self
#print axioms strictJointCylinderRadiusTimeTranslatedReflectionQuadratic_nonnegative
#print axioms strictJointCylinderRadiusTimeTranslatedReflectionBilinear_add_left
#print axioms strictJointCylinderRadiusTimeTranslatedReflectionBilinear_smul_left
#print axioms strictJointCylinderRadiusTimeTranslatedReflectionBilinear_add_right
#print axioms strictJointCylinderRadiusTimeTranslatedReflectionBilinear_smul_right

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslation
