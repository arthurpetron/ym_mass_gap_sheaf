/-
# Finite oriented entries of the doubled-time OS bilinear

The direct support-polarized OS approximant is rewritten as a finite
quadratic over a two-code pushforward law.  Its left code is the transported
source cylinder and its right code is the doubled-time translated target
cylinder.  This leaves only an entrywise cofinal comparison with the signed
mixed chart.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipushforward
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-- A common positive denominator factors through an oriented finite cross
form. -/
theorem finiteJointCrossBilinear_divPos_kernel_eqv
    {State : Type} (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (numerator : State → State → Q')
    (denominator : Q') (hdenominator : (0 : Q') < denominator) :
    finiteJointCrossBilinear states leftCoefficient rightCoefficient
        (fun left right =>
          Q'.divPos (numerator left right) denominator hdenominator) ≈
      Q'.divPos
        (finiteJointCrossBilinear
          states leftCoefficient rightCoefficient numerator)
        denominator hdenominator := by
  unfold finiteJointCrossBilinear Q'.divPos
  have hrow : ∀ left,
      listQSum (fun right =>
        (leftCoefficient left * rightCoefficient right) *
          (numerator left right * Q'.recipPos denominator hdenominator))
          states ≈
        listQSum (fun right =>
          (leftCoefficient left * rightCoefficient right) *
            numerator left right) states *
          Q'.recipPos denominator hdenominator := by
    intro left
    refine Q'.eqv_trans _
      (listQSum (fun right =>
        ((leftCoefficient left * rightCoefficient right) *
          numerator left right) * Q'.recipPos denominator hdenominator)
        states) _ ?_ ?_
    · apply listQSum_congr
      intro right
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    · exact listQSum_mul_right _ _ states
  refine Q'.eqv_trans _
    (listQSum (fun left =>
      listQSum (fun right =>
        (leftCoefficient left * rightCoefficient right) *
          numerator left right) states *
        Q'.recipPos denominator hdenominator) states) _ ?_ ?_
  · apply listQSum_congr
    intro left
    exact hrow left
  · exact listQSum_mul_right _ _ states

/-- Normalized two-code support law. -/
def centralNormalizedSupportBipairLaw
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) : Q' :=
  finiteJointKernelBipushforward
    (centralHalfSupportSpace half)
    (centralNormalizedSupportPairLaw coupling hcoupling cutoff half)
    leftCode rightCode left right

/-- The normalized support-polarized form is the finite quadratic of its
oriented two-code pushforward law. -/
theorem centralNormalizedSupportReflectionBilinear_eqv_bipair
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCode rightCode : List Nat → List Bool)
    (targets : List (List Bool)) (hnodup : targets.Nodup)
    (hleft : ∀ support, support ∈ centralHalfSupportSpace half →
      leftCode support ∈ targets)
    (hright : ∀ support, support ∈ centralHalfSupportSpace half →
      rightCode support ∈ targets)
    (coefficient : List Bool → Q') :
    centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
        (centralLocalSupportCoefficient leftCode coefficient)
        (centralLocalSupportCoefficient rightCode coefficient) ≈
      finiteJointQuadratic targets coefficient
        (centralNormalizedSupportBipairLaw
          coupling hcoupling cutoff half leftCode rightCode) := by
  let denominator := slabParametricKPhysicalPartition
    coupling cutoff (centralExtent half)
  have hdenominator : (0 : Q') < denominator :=
    slabParametricKPhysicalPartition_pos
      hcoupling cutoff (centralExtent half)
  let raw := centralSupportReflectedKernel coupling cutoff half
  let normalized := centralNormalizedSupportPairLaw
    coupling hcoupling cutoff half
  have hpolarized :=
    finiteJointPolarizedBilinear_eqv_cross_of_joint_symm
      (centralHalfSupportSpace half)
      (centralLocalSupportCoefficient leftCode coefficient)
      (centralLocalSupportCoefficient rightCode coefficient)
      raw
      (fun left _ right _ =>
        centralSupportReflectedKernel_symm
          coupling cutoff half left right)
  have hnormalized :
      finiteJointCrossBilinear
          (centralHalfSupportSpace half)
          (centralLocalSupportCoefficient leftCode coefficient)
          (centralLocalSupportCoefficient rightCode coefficient)
          normalized ≈
        Q'.divPos
          (finiteJointCrossBilinear
            (centralHalfSupportSpace half)
            (centralLocalSupportCoefficient leftCode coefficient)
            (centralLocalSupportCoefficient rightCode coefficient)
            raw)
          denominator hdenominator := by
    simpa only [normalized, raw, denominator,
      centralNormalizedSupportPairLaw] using
      (finiteJointCrossBilinear_divPos_kernel_eqv
        (centralHalfSupportSpace half)
        (centralLocalSupportCoefficient leftCode coefficient)
        (centralLocalSupportCoefficient rightCode coefficient)
        raw denominator hdenominator)
  have hpush := finiteJointQuadratic_bipushforward_eqv_cross
    (centralHalfSupportSpace half) normalized leftCode rightCode
    targets hnodup hleft hright coefficient
  unfold centralNormalizedSupportReflectionBilinear Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hpolarized) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hnormalized) ?_
  exact Q'.eqv_symm hpush

/-- The oriented support-law entry for the common doubled-time source/target
presentation at one strict OS stage. -/
def strictJointDoubledTimeMixedOSOrientedEntrySequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) (stage : Nat) : Q' :=
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  centralNormalizedSupportBipairLaw coupling hcoupling
    (centralStrictJointCenteredStageCutoff outer stage) radius
    (centralStrictLocalQueryCode radius outer
      (strictJointDoubledTimeMixedSource shift vector).roots)
    (centralStrictLocalQueryCode radius outer
      (strictJointDoubledTimeMixedTarget shift vector).roots)
    left right

/-- Every direct mixed OS bilinear approximant is the finite quadratic over
the oriented mixed entry sequence. -/
theorem strictJointDoubledTimeMixedOSBilinearSequence_eqv_entries
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (stage : Nat) :
    strictJointCylinderReflectionBilinearSequence
        coupling hcoupling
        (strictJointDoubledTimeMixedSource shift vector)
        (strictJointDoubledTimeMixedTarget shift vector) stage ≈
      finiteJointQuadratic
        (strictJointFingerprintSpace vector.roots.length)
        vector.coefficient
        (fun left right =>
          strictJointDoubledTimeMixedOSOrientedEntrySequence
            coupling hcoupling shift vector left right stage) := by
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  let leftCode := centralStrictLocalQueryCode radius outer
    (strictJointDoubledTimeMixedSource shift vector).roots
  let rightCode := centralStrictLocalQueryCode radius outer
    (strictJointDoubledTimeMixedTarget shift vector).roots
  have hleftLength :
      (strictJointDoubledTimeMixedSource shift vector).roots.length =
        vector.roots.length := by
    unfold strictJointDoubledTimeMixedSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
    simp only [List.length_map]
  have hrightLength :
      (strictJointDoubledTimeMixedTarget shift vector).roots.length =
        vector.roots.length := by
    unfold strictJointDoubledTimeMixedTarget
    exact timeTranslateStrictJointCylinderVector_roots_length vector
  have hleft : ∀ support, support ∈ centralHalfSupportSpace radius →
      leftCode support ∈ strictJointFingerprintSpace vector.roots.length := by
    intro support hsupport
    rw [← hleftLength]
    exact centralStrictLocalQueryCode_mem_fixedSpace
      radius outer (strictJointDoubledTimeMixedSource shift vector).roots support
  have hright : ∀ support, support ∈ centralHalfSupportSpace radius →
      rightCode support ∈ strictJointFingerprintSpace vector.roots.length := by
    intro support hsupport
    rw [← hrightLength]
    exact centralStrictLocalQueryCode_mem_fixedSpace
      radius outer (strictJointDoubledTimeMixedTarget shift vector).roots support
  have hfinite := centralNormalizedSupportReflectionBilinear_eqv_bipair
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff outer stage) radius
    leftCode rightCode
    (strictJointFingerprintSpace vector.roots.length)
    (strictJointFingerprintSpace_nodup vector.roots.length)
    hleft hright vector.coefficient
  simpa only [strictJointCylinderReflectionBilinearSequence,
    strictJointDoubledTimeMixedOSOrientedEntrySequence,
    strictJointDoubledTimeMixedSource,
    strictJointDoubledTimeMixedTarget, outer, radius, leftCode, rightCode]
    using hfinite

#print axioms finiteJointCrossBilinear_divPos_kernel_eqv
#print axioms centralNormalizedSupportReflectionBilinear_eqv_bipair
#print axioms strictJointDoubledTimeMixedOSBilinearSequence_eqv_entries

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries
