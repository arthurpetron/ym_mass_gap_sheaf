/-
# Thermodynamic diagonal for the strict signed covariance

This module connects the arbitrary-cutoff geometric covariance to the
centered thermodynamic schedules used by the Osterwalder--Schrader transfer
construction.  The central even-volume sequence uses the same selected
lower-source and upper-target roots as the geometric theorem.  Entrywise
adjacent-volume comparison then relates it to the ordinary centered joint
bilinear with an explicit half-power error.

The final goal of this file is a constructed receding-volume connected
`CReal`, its `1/16` geometric bound, and its exact identification with the
dense connected transfer form.  No presentation-independent completed-space
bound or continuum gap is asserted.
-/

import YMGap.Continuum.Z4CouplingParametricTwoBlockObservableCovariance
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointConnectedTwoStepMoment
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly

namespace YMGap.Continuum.Z4CouplingParametricSignedThermodynamicClustering

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricTwoBlockObservableCovariance
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointConnectedTwoStepMoment
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The selected central even-volume cross form -/

def orientedDoubledTimeCentralBilinearSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (stage : Nat) : Q' :=
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  let cutoff := centralStrictJointCenteredStageCutoff outer stage
  finiteHeterogeneousCrossBilinear
    (strictJointFingerprintSpace left.roots.length)
    (strictJointFingerprintSpace right.roots.length)
    left.coefficient right.coefficient
    (fun leftBits rightBits =>
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff (centralAmbient radius)
        (sourceCylinderEvent
          (orientedDoubledTimeCommonCylinderRoots
            radius shift left right)
          (centralStrictJointPairPredicate
            left.roots.length leftBits rightBits)))

/-- The selected central event is literally the projected ordinary-joint
event used by the adjacent odd/even comparison theorem. -/
theorem orientedDoubledTimeCentralEvent_eq_projectedJoint
    {base : Nat} (shift stage : Nat)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) :
    let outer := base + (shift + shift)
    let radius := strictQueryBase outer + stage
    let roots := orientedDoubledTimeJointRoots shift left right
    let hroots := orientedDoubledTimeJointRoots_canonical shift left right
    slabMarkedCylinderEvent
        (centralStrictJointCanonicalAtoms radius outer roots
          (Nat.le_add_right (strictQueryBase outer) stage) hroots)
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) =
      sourceCylinderEvent
        (orientedDoubledTimeCommonCylinderRoots
          radius shift left right)
        (centralStrictJointPairPredicate
          left.roots.length leftBits rightBits) := by
  dsimp only
  unfold slabMarkedCylinderEvent
  calc
    cylinderEvent
        ((centralStrictJointCanonicalAtoms
          (strictQueryBase (base + (shift + shift)) + stage)
          (base + (shift + shift))
          (orientedDoubledTimeJointRoots shift left right)
          (Nat.le_add_right (strictQueryBase (base + (shift + shift))) stage)
          (orientedDoubledTimeJointRoots_canonical shift left right)).map
            Subtype.val)
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) =
      cylinderEvent
        (centralStrictJointCylinderRoots
          (strictQueryBase (base + (shift + shift)) + stage)
          (base + (shift + shift))
          (orientedDoubledTimeJointRoots shift left right))
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) := by
      apply congrArg (fun markedRoots => cylinderEvent markedRoots
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits))
      exact centralStrictJointCanonicalAtoms_values
        (strictQueryBase (base + (shift + shift)) + stage)
        (base + (shift + shift))
        (orientedDoubledTimeJointRoots shift left right)
        (Nat.le_add_right (strictQueryBase (base + (shift + shift))) stage)
        (orientedDoubledTimeJointRoots_canonical shift left right)
    _ = _ := orientedDoubledTimeJointEvent_eq_common
      shift (strictQueryBase (base + (shift + shift)) + stage)
      left right leftBits rightBits

def orientedDoubledTimeCentralToCenteredCoefficient
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) : Q' :=
  heterogeneousCoefficientPairL1
      (strictJointFingerprintSpace left.roots.length)
      (strictJointFingerprintSpace right.roots.length)
      left.coefficient right.coefficient *
    spinSummedCylinderBoundaryCoefficient
      ((orientedDoubledTimeJointRoots shift left right).length +
        (orientedDoubledTimeJointRoots shift left right).length)

theorem orientedDoubledTimeCentralToCenteredCoefficient_nonnegative
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    (0 : Q') ≤ orientedDoubledTimeCentralToCenteredCoefficient
      shift left right := by
  unfold orientedDoubledTimeCentralToCenteredCoefficient
  exact Q'.mul_nonneg _ _
    (heterogeneousCoefficientPairL1_nonnegative
      (strictJointFingerprintSpace left.roots.length)
      (strictJointFingerprintSpace right.roots.length)
      left.coefficient right.coefficient)
    (spinSummedCylinderBoundaryCoefficient_nonnegative
      ((orientedDoubledTimeJointRoots shift left right).length +
        (orientedDoubledTimeJointRoots shift left right).length))

/-- At every stage, the central even-volume cross form differs from the
ordinary centered joint bilinear by an explicit dyadic boundary term. -/
theorem orientedDoubledTimeCentralBilinearSequence_abs_sub_centered_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base)
    (stage : Nat) :
    Q'.abs
        (orientedDoubledTimeCentralBilinearSequence
            coupling hcoupling shift left right stage -
          (orientedDoubledTimeJointCenteredBilinear
            coupling hcoupling hle shift left right).approx stage) ≤
      orientedDoubledTimeCentralToCenteredCoefficient shift left right *
        HalfPow.half ^ stage := by
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  let cutoff := centralStrictJointCenteredStageCutoff outer stage
  let roots := orientedDoubledTimeJointRoots shift left right
  let hroots := orientedDoubledTimeJointRoots_canonical shift left right
  let statesLeft := strictJointFingerprintSpace left.roots.length
  let statesRight := strictJointFingerprintSpace right.roots.length
  let centralLaw : List Bool → List Bool → Q' :=
    fun leftBits rightBits =>
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff (centralAmbient radius)
        (sourceCylinderEvent
          (orientedDoubledTimeCommonCylinderRoots
            radius shift left right)
          (centralStrictJointPairPredicate
            left.roots.length leftBits rightBits))
  let centeredLaw : List Bool → List Bool → Q' :=
    fun leftBits rightBits =>
      couplingParametricStrictJointCenteredSequence
        coupling hcoupling outer roots
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) stage
  let epsilon := spinSummedCylinderBoundaryEpsilon
    (roots.length + roots.length) stage
  have hcentered :
      (orientedDoubledTimeJointCenteredBilinear
          coupling hcoupling hle shift left right).approx stage ≈
        finiteHeterogeneousCrossBilinear
          statesLeft statesRight left.coefficient right.coefficient
          centeredLaw := by
    simpa only [statesLeft, statesRight, centeredLaw, roots, outer] using
      (orientedDoubledTimeJointCenteredBilinear_approx_eqv
        hcoupling hle left right (shift := shift) (stage := stage))
  have hentry : ∀ leftBits rightBits,
      leftBits ∈ statesLeft → rightBits ∈ statesRight →
      Q'.abs (centralLaw leftBits rightBits -
        centeredLaw leftBits rightBits) ≤ epsilon := by
    intro leftBits rightBits hleft hright
    have hraw :=
      couplingParametricKCompatibleStrictJoint_cross_centered_abs_sub_le
        hcoupling hle cutoff hroots
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits)
        (stage := stage)
    rw [orientedDoubledTimeCentralEvent_eq_projectedJoint
      shift stage left right leftBits rightBits] at hraw
    simpa only [centralLaw, centeredLaw, epsilon,
      couplingParametricStrictJointCenteredSequence,
      outer, radius, roots, hroots, cutoff,
      centralStrictJointCenteredCylinderEvent] using hraw
  have hfinite := finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1
    statesLeft statesRight left.coefficient right.coefficient
    centralLaw centeredLaw epsilon hentry
  have hleft :
      orientedDoubledTimeCentralBilinearSequence
          coupling hcoupling shift left right stage =
        finiteHeterogeneousCrossBilinear
          statesLeft statesRight left.coefficient right.coefficient
          centralLaw := by rfl
  have hdifference :
      orientedDoubledTimeCentralBilinearSequence
            coupling hcoupling shift left right stage -
          (orientedDoubledTimeJointCenteredBilinear
            coupling hcoupling hle shift left right).approx stage ≈
        finiteHeterogeneousCrossBilinear
            statesLeft statesRight left.coefficient right.coefficient
            centralLaw -
          finiteHeterogeneousCrossBilinear
            statesLeft statesRight left.coefficient right.coefficient
            centeredLaw := by
    rw [hleft]
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ hcentered)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (Q'.le_trans' _ _ _ hfinite ?_)
  unfold orientedDoubledTimeCentralToCenteredCoefficient
  have hboundary : epsilon ≤
      spinSummedCylinderBoundaryCoefficient
          (roots.length + roots.length) * HalfPow.half ^ stage := by
    exact spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      (roots.length + roots.length) stage
  have hmul := Q'.mul_le_mul_of_nonneg_left
    epsilon
    (spinSummedCylinderBoundaryCoefficient
      (roots.length + roots.length) * HalfPow.half ^ stage)
    (heterogeneousCoefficientPairL1
      statesLeft statesRight left.coefficient right.coefficient)
    hboundary
    (heterogeneousCoefficientPairL1_nonnegative
      statesLeft statesRight left.coefficient right.coefficient)
  refine Q'.le_trans' _ _ _ hmul ?_
  exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv
    (heterogeneousCoefficientPairL1
      statesLeft statesRight left.coefficient right.coefficient)
    (spinSummedCylinderBoundaryCoefficient
      (roots.length + roots.length))
    (HalfPow.half ^ stage)))

#print axioms orientedDoubledTimeCentralEvent_eq_projectedJoint
#print axioms orientedDoubledTimeCentralBilinearSequence_abs_sub_centered_le

end YMGap.Continuum.Z4CouplingParametricSignedThermodynamicClustering
