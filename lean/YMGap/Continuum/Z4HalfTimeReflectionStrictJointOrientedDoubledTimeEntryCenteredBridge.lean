/-
# Centered-limit bridge for heterogeneous oriented OS entries

This file expands an oriented strict-cylinder bilinear approximant with
different left and right presentations into the heterogeneous finite
bipushforward.  Each entry is then identified with its literal corrected-
slab cylinder and compared to the centered ordinary joint chart by the
existing derived half-power boundary estimate.

The result is the entrywise quantitative bridge needed for finite assembly.
No covariance or self-adjointness statement is assumed.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointCenteredBridge

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeEntryCenteredBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipairConditional
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSEntryEvent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointCenteredBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Heterogeneous finite entry expansion -/

def orientedDoubledTimeEntrySequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) (stage : Nat) : Q' :=
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  centralNormalizedSupportBipairLaw coupling hcoupling
    (centralStrictJointCenteredStageCutoff outer stage) radius
    (centralStrictLocalQueryCode radius outer
      (orientedDoubledTimeSource shift left).roots)
    (centralStrictLocalQueryCode radius outer
      (orientedDoubledTimeTarget shift right).roots)
    leftBits rightBits

/-- Every oriented mixed strict bilinear approximant is the finite cross form
over separate left and right fingerprint spaces. -/
theorem orientedDoubledTimeReflectionBilinearSequence_eqv_entries
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (stage : Nat) :
    strictJointCylinderReflectionBilinearSequence
        coupling hcoupling
        (orientedDoubledTimeSource shift left)
        (orientedDoubledTimeTarget shift right) stage ≈
      finiteHeterogeneousCrossBilinear
        (strictJointFingerprintSpace left.roots.length)
        (strictJointFingerprintSpace right.roots.length)
        left.coefficient right.coefficient
        (fun leftBits rightBits =>
          orientedDoubledTimeEntrySequence
            coupling hcoupling shift left right
            leftBits rightBits stage) := by
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  let leftCode := centralStrictLocalQueryCode radius outer
    (orientedDoubledTimeSource shift left).roots
  let rightCode := centralStrictLocalQueryCode radius outer
    (orientedDoubledTimeTarget shift right).roots
  have hleftLength :
      (orientedDoubledTimeSource shift left).roots.length =
        left.roots.length := by
    unfold orientedDoubledTimeSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
    simp only [List.length_map]
  have hrightLength :
      (orientedDoubledTimeTarget shift right).roots.length =
        right.roots.length := by
    unfold orientedDoubledTimeTarget
    exact timeTranslateStrictJointCylinderVector_roots_length right
  have hleft : ∀ support, support ∈ centralHalfSupportSpace radius →
      leftCode support ∈ strictJointFingerprintSpace left.roots.length := by
    intro support hsupport
    rw [← hleftLength]
    exact centralStrictLocalQueryCode_mem_fixedSpace
      radius outer (orientedDoubledTimeSource shift left).roots support
  have hright : ∀ support, support ∈ centralHalfSupportSpace radius →
      rightCode support ∈ strictJointFingerprintSpace right.roots.length := by
    intro support hsupport
    rw [← hrightLength]
    exact centralStrictLocalQueryCode_mem_fixedSpace
      radius outer (orientedDoubledTimeTarget shift right).roots support
  have hfinite :=
    centralNormalizedSupportReflectionBilinear_eqv_heterogeneousBipair
      coupling hcoupling
      (centralStrictJointCenteredStageCutoff outer stage) radius
      leftCode rightCode
      (strictJointFingerprintSpace left.roots.length)
      (strictJointFingerprintSpace right.roots.length)
      (strictJointFingerprintSpace_nodup left.roots.length)
      (strictJointFingerprintSpace_nodup right.roots.length)
      hleft hright left.coefficient right.coefficient
  simpa only [strictJointCylinderReflectionBilinearSequence,
    centralLocalSupportCoefficient,
    centralNormalizedSupportHeterogeneousBipairLaw,
    centralNormalizedSupportBipairLaw,
    finiteJointKernelHeterogeneousBipushforward,
    finiteJointKernelBipushforward,
    orientedDoubledTimeEntrySequence,
    outer, radius, leftCode, rightCode] using hfinite

/-! ## 2. Literal corrected-slab entry -/

theorem orientedDoubledTimeEntrySequence_eqv_cylinder
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) (stage : Nat) :
    orientedDoubledTimeEntrySequence
        coupling hcoupling shift left right leftBits rightBits stage ≈
      couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling
        (centralStrictJointCenteredStageCutoff
          (base + (shift + shift)) stage)
        (centralExtent
          (strictQueryBase (base + (shift + shift)) + stage))
        (sourceCylinderEvent
          (orientedDoubledTimeCommonCylinderRoots
            (strictQueryBase (base + (shift + shift)) + stage)
            shift left right)
          (centralStrictJointPairPredicate
            left.roots.length leftBits rightBits)) := by
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  have hbase : strictQueryBase outer ≤ radius :=
    Nat.le_add_right (strictQueryBase outer) stage
  have hentry := centralNormalizedSupportBipairLaw_eq_physicalGivenSlab
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff outer stage) radius
    (centralStrictLocalQueryCode radius outer
      (orientedDoubledTimeSource shift left).roots)
    (centralStrictLocalQueryCode radius outer
      (orientedDoubledTimeTarget shift right).roots)
    leftBits rightBits
  have hevent := couplingPhysicalGivenSlab_strictBipair_eq_cylinder
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff outer stage)
    hbase hbase
    (orientedDoubledTimeSource shift left).rootsCanonical
    (orientedDoubledTimeTarget shift right).rootsCanonical
    leftBits rightBits
  rw [hevent] at hentry
  simpa only [orientedDoubledTimeEntrySequence,
    orientedDoubledTimeCommonCylinderRoots,
    orientedDoubledTimeSource, orientedDoubledTimeTarget,
    boxTransportStrictJointCylinderVector_roots,
    timeTranslateStrictJointCylinderVector_roots,
    transportedCylinderRoots, List.length_map,
    outer, radius] using hentry

/-! ## 3. Quantitative centered bridge -/

/-- Each heterogeneous oriented entry approaches the centered limit of its
projected ordinary joint chart with an explicit derived half-power modulus. -/
theorem orientedDoubledTimeEntrySequence_abs_sub_jointCentered_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) (stage : Nat) :
    Q'.abs
        (orientedDoubledTimeEntrySequence
            coupling hcoupling shift left right leftBits rightBits stage -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling (base + (shift + shift))
            (orientedDoubledTimeJointRoots shift left right)
            (orientedDoubledTimeJointPredicate
              left.roots.length right.roots.length leftBits rightBits)
            stage) ≤
      strictJointConditionalCenteredCoefficient
          ((orientedDoubledTimeJointRoots shift left right).length +
            (orientedDoubledTimeJointRoots shift left right).length) *
        HalfPow.half ^ stage := by
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  let roots := orientedDoubledTimeJointRoots shift left right
  let predicate := orientedDoubledTimeJointPredicate
    left.roots.length right.roots.length leftBits rightBits
  have hcanonical := orientedDoubledTimeJointRoots_canonical
    shift left right
  have hentry := orientedDoubledTimeEntrySequence_eqv_cylinder
    hcoupling shift left right leftBits rightBits stage
  have hevent := orientedDoubledTimeJointEvent_eq_common
    shift radius left right leftBits rightBits
  have hmarked :
      slabMarkedCylinderEvent
          (centralStrictJointCanonicalAtoms radius outer roots
            (Nat.le_add_right (strictQueryBase outer) stage) hcanonical)
          predicate =
        sourceCylinderEvent
          (centralStrictJointCylinderRoots radius outer roots)
          predicate := by
    funext family
    unfold slabMarkedCylinderEvent sourceCylinderEvent
    exact congrArg
      (fun markedRoots => cylinderEvent markedRoots predicate family)
      (centralStrictJointCanonicalAtoms_values
        radius outer roots
        (Nat.le_add_right (strictQueryBase outer) stage) hcanonical)
  have hraw :=
    couplingPhysicalGivenSlabStrictJointPredicate_to_centeredSequence_half_pow
      hcoupling hle hcanonical predicate (stage := stage)
  dsimp only at hraw
  have heventMarked :
      slabMarkedCylinderEvent
          (centralStrictJointCanonicalAtoms radius outer roots
            (Nat.le_add_right (strictQueryBase outer) stage) hcanonical)
          predicate =
        sourceCylinderEvent
          (orientedDoubledTimeCommonCylinderRoots
            radius shift left right)
          (centralStrictJointPairPredicate
            left.roots.length leftBits rightBits) :=
    hmarked.trans hevent
  rw [heventMarked] at hraw
  have hdifference :
      orientedDoubledTimeEntrySequence
            coupling hcoupling shift left right leftBits rightBits stage -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling outer roots predicate stage ≈
        couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling
            (centralStrictJointCenteredStageCutoff outer stage)
            (centralExtent radius)
            (sourceCylinderEvent
              (orientedDoubledTimeCommonCylinderRoots
                radius shift left right)
              (centralStrictJointPairPredicate
                left.roots.length leftBits rightBits)) -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling outer roots predicate stage :=
    Q'.add_eqv_congr_right _ _ _ hentry
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (by simpa only [outer, radius, roots, predicate] using hraw)

#print axioms orientedDoubledTimeReflectionBilinearSequence_eqv_entries
#print axioms orientedDoubledTimeEntrySequence_eqv_cylinder
#print axioms orientedDoubledTimeEntrySequence_abs_sub_jointCentered_le

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeEntryCenteredBridge
