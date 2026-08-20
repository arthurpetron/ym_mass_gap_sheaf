/-
# Arbitrary-cutoff signed cylinder covariance

Expand two rational cylinder observables over their finite Boolean
fingerprint spaces.  The uniform all-cutoff Boolean covariance estimate
controls every kernel entry, and finite bilinearity gives a signed covariance
bound with the product of the two presentation-level coefficient `l1` norms.

This does not identify that presentation norm with the reflection seminorm.
-/

import YMGap.Continuum.Z4CouplingParametricTwoBlockNormalizedCovariance
import YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance

namespace YMGap.Continuum.Z4CouplingParametricTwoBlockSignedCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance
open YMGap.Continuum.Z4CouplingParametricTwoBlockNormalizedCovariance
open YMGap.Continuum.Z4CouplingParametricTwoBlockProbabilityCovariance
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

def couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftBits rightBits : List Bool) : Q' :=
  couplingParametricKNormalizedTwoBlockFourCellCovariance hcoupling cutoff
    (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
    (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
    (exactFingerprintPredicate leftBits)
    (exactFingerprintPredicate rightBits)

def couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon
    (rootCount shift : Nat) : Q' :=
  Q'.ofNat rootCount *
    (anchorDecoratedEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2)

theorem couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon_nonnegative
    (rootCount shift : Nat) :
    (0 : Q') ≤
      couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon
        rootCount shift := by
  unfold couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon
  exact Q'.mul_nonneg _ _
    (YMGap.Constructive.ExpNeg.ofNat_nonneg' rootCount)
    (Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative _)
      (YMGap.Constructive.ExpNeg.ofNat_nonneg' 2))

theorem couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftBits rightBits : List Bool) :
    Q'.abs
        (couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel
          hcoupling cutoff hadmissible hroots leftBits rightBits) ≤
      couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon
        roots.length shift := by
  unfold couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel
    couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon
  change couplingParametricKNormalizedTwoBlockCovarianceMagnitude
      hcoupling cutoff
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      (exactFingerprintPredicate leftBits)
      (exactFingerprintPredicate rightBits) ≤ _
  exact
    couplingParametricKStrictDoubledTimeNormalizedCovarianceMagnitude_le_rootCount
      hcoupling hle cutoff hadmissible hroots
      (exactFingerprintPredicate leftBits)
      (exactFingerprintPredicate rightBits)

def couplingParametricKStrictDoubledTimeNormalizedSignedCovariance
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') : Q' :=
  finiteHeterogeneousCrossBilinear
    (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace roots.length)
    leftCoefficient rightCoefficient
    (couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel
      hcoupling cutoff hadmissible hroots)

def couplingParametricKStrictDoubledTimeBooleanCovarianceAssembly
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') : Q' :=
  finiteHeterogeneousCrossBilinear
    (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace roots.length)
    leftCoefficient rightCoefficient
    (fun leftBits rightBits =>
      couplingParametricKTwoBlockBooleanCovariance hcoupling cutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        (exactFingerprintPredicate leftBits)
        (exactFingerprintPredicate rightBits))

theorem couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel_eqv_boolean
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftBits rightBits : List Bool) :
    couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel
        hcoupling cutoff hadmissible hroots leftBits rightBits ≈
      couplingParametricKTwoBlockBooleanCovariance hcoupling cutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        (exactFingerprintPredicate leftBits)
        (exactFingerprintPredicate rightBits) := by
  unfold couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel
  exact Q'.eqv_symm
    (couplingParametricKTwoBlockBooleanCovariance_eqv_normalizedFourCell
      hcoupling cutoff
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      (exactFingerprintPredicate leftBits)
      (exactFingerprintPredicate rightBits))

theorem couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_eqv_booleanAssembly
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    couplingParametricKStrictDoubledTimeNormalizedSignedCovariance
        hcoupling cutoff hadmissible hroots
        leftCoefficient rightCoefficient ≈
      couplingParametricKStrictDoubledTimeBooleanCovarianceAssembly
        hcoupling cutoff hadmissible hroots
        leftCoefficient rightCoefficient := by
  unfold couplingParametricKStrictDoubledTimeNormalizedSignedCovariance
    couplingParametricKStrictDoubledTimeBooleanCovarianceAssembly
    finiteHeterogeneousCrossBilinear
  apply listQSum_congr
  intro leftBits
  apply listQSum_congr
  intro rightBits
  exact Q'.mul_eqv_congr_left _ _ _
    (couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel_eqv_boolean
      hcoupling cutoff hadmissible hroots leftBits rightBits)

private theorem add_neg_zero_eqv_local (value : Q') :
    value + (-(0 : Q')) ≈ value := by
  refine Q'.eqv_trans _ (value + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl value)
      (by decide : (-(0 : Q')) ≈ 0)
  · exact Q'.eqv_of_eq (Q'.add_zero' value)

private theorem finiteHeterogeneousCrossBilinear_zeroLaw_eqv
    {LeftState RightState : Type}
    (leftStates : List LeftState) (rightStates : List RightState)
    (leftCoefficient : LeftState → Q')
    (rightCoefficient : RightState → Q') :
    finiteHeterogeneousCrossBilinear
        leftStates rightStates leftCoefficient rightCoefficient
        (fun _ _ => (0 : Q')) ≈ 0 := by
  unfold finiteHeterogeneousCrossBilinear
  refine Q'.eqv_trans _
    (listQSum (fun _ : LeftState => (0 : Q')) leftStates) _ ?_
    (listQSum_zero leftStates)
  apply listQSum_congr_on
  intro left hleft
  refine Q'.eqv_trans _
    (listQSum (fun _ : RightState => (0 : Q')) rightStates) _ ?_
    (listQSum_zero rightStates)
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_zero_eqv
    (leftCoefficient left * rightCoefficient right)

theorem couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_abs_le_pairL1
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    Q'.abs
        (couplingParametricKStrictDoubledTimeNormalizedSignedCovariance
          hcoupling cutoff hadmissible hroots
          leftCoefficient rightCoefficient) ≤
      heterogeneousCoefficientPairL1
          (strictJointFingerprintSpace roots.length)
          (strictJointFingerprintSpace roots.length)
          leftCoefficient rightCoefficient *
        couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon
          roots.length shift := by
  let states := strictJointFingerprintSpace roots.length
  let covariance :=
    couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel
      hcoupling cutoff hadmissible hroots
  let zeroLaw : List Bool → List Bool → Q' := fun _ _ => 0
  let epsilon :=
    couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon
      roots.length shift
  have hfinite := finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1
    states states leftCoefficient rightCoefficient covariance zeroLaw epsilon
    (fun left right hleft hright => by
      have hdifference : covariance left right + (-zeroLaw left right) ≈
          covariance left right :=
        add_neg_zero_eqv_local (covariance left right)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
        (couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel_abs_le
          hcoupling hle cutoff hadmissible hroots left right))
  have hzero : finiteHeterogeneousCrossBilinear
      states states leftCoefficient rightCoefficient zeroLaw ≈ 0 :=
    finiteHeterogeneousCrossBilinear_zeroLaw_eqv
      states states leftCoefficient rightCoefficient
  have hdifference :
      finiteHeterogeneousCrossBilinear
          states states leftCoefficient rightCoefficient covariance +
        (-finiteHeterogeneousCrossBilinear
          states states leftCoefficient rightCoefficient zeroLaw) ≈
      finiteHeterogeneousCrossBilinear
        states states leftCoefficient rightCoefficient covariance := by
    refine Q'.eqv_trans _
      (finiteHeterogeneousCrossBilinear
          states states leftCoefficient rightCoefficient covariance +
        (-(0 : Q'))) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ hzero)
    · exact add_neg_zero_eqv_local _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr (Q'.eqv_symm hdifference)))
    (by simpa only
        [couplingParametricKStrictDoubledTimeNormalizedSignedCovariance,
          states, covariance, zeroLaw, epsilon] using hfinite)

theorem couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_abs_le_l1
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    Q'.abs
        (couplingParametricKStrictDoubledTimeNormalizedSignedCovariance
          hcoupling cutoff hadmissible hroots
          leftCoefficient rightCoefficient) ≤
      (coefficientL1
          (strictJointFingerprintSpace roots.length) leftCoefficient *
        coefficientL1
          (strictJointFingerprintSpace roots.length) rightCoefficient) *
        couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon
          roots.length shift := by
  refine Q'.le_trans' _ _ _
    (couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_abs_le_pairL1
      hcoupling hle cutoff hadmissible hroots
      leftCoefficient rightCoefficient) ?_
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (heterogeneousCoefficientPairL1_le_l1_mul_l1
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace roots.length)
      leftCoefficient rightCoefficient)
    (couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon_nonnegative
      roots.length shift)

#print axioms couplingParametricKStrictDoubledTimeNormalizedCovarianceKernel_abs_le
#print axioms couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_eqv_booleanAssembly
#print axioms couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_abs_le_pairL1
#print axioms couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_abs_le_l1

end YMGap.Continuum.Z4CouplingParametricTwoBlockSignedCovariance
