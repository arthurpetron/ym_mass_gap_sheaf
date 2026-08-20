/-
# Signed finite-cylinder covariance from Boolean atom bounds

Expand two rational cylinder observables over the exhaustive finite Boolean
fingerprint space.  Applying the normalized two-block indicator estimate to
each pair of fingerprint atoms and summing with absolute coefficients gives
an explicit signed covariance bound.  Its prefactor is the product of the two
finite coefficient `l1` norms.

This is an observable-dependent clustering estimate.  It does not compare the
coefficient `l1` norm with the reflection seminorm, so it is not yet an
operator contraction.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockProbabilityCovariance
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly

namespace YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockNormalizedCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockProbabilityCovariance
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-- The Boolean atom selecting one exact finite fingerprint. -/
def exactFingerprintPredicate (target : List Bool) : List Bool → Bool :=
  fun bits => decide (bits = target)

/-- Entrywise normalized covariance kernel between exact lower and upper
fingerprint atoms. -/
def strictDoubledTimeNormalizedCovarianceKernel
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftBits rightBits : List Bool) : Q' :=
  normalizedTwoBlockFourCellCovariance
    (centralAmbient radius)
    (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
    (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
    (exactFingerprintPredicate leftBits)
    (exactFingerprintPredicate rightBits)

/-- The common entrywise temporal envelope. -/
def strictDoubledTimeNormalizedCovarianceEpsilon
    (rootCount shift : Nat) : Q' :=
  Q'.ofNat rootCount *
    (anchorEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2)

theorem strictDoubledTimeNormalizedCovarianceEpsilon_nonnegative
    (rootCount shift : Nat) :
    (0 : Q') ≤
      strictDoubledTimeNormalizedCovarianceEpsilon rootCount shift := by
  unfold strictDoubledTimeNormalizedCovarianceEpsilon
  exact Q'.mul_nonneg _ _
    (YMGap.Constructive.ExpNeg.ofNat_nonneg' rootCount)
    (Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorEffectiveRatio
        anchorEffectiveRatio_nonnegative _)
      (YMGap.Constructive.ExpNeg.ofNat_nonneg' 2))

/-- Every exact fingerprint pair obeys the same ambient-volume-uniform
covariance bound. -/
theorem strictDoubledTimeNormalizedCovarianceKernel_abs_le
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftBits rightBits : List Bool) :
    Q'.abs (strictDoubledTimeNormalizedCovarianceKernel
        hadmissible hroots leftBits rightBits) ≤
      strictDoubledTimeNormalizedCovarianceEpsilon
        roots.length shift := by
  unfold strictDoubledTimeNormalizedCovarianceKernel
    strictDoubledTimeNormalizedCovarianceEpsilon
  change normalizedTwoBlockCovarianceMagnitude
      (centralAmbient radius)
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      (exactFingerprintPredicate leftBits)
      (exactFingerprintPredicate rightBits) ≤ _
  exact strictDoubledTimeNormalizedCovarianceMagnitude_le_rootCount
    hadmissible hroots
    (exactFingerprintPredicate leftBits)
    (exactFingerprintPredicate rightBits)

/-- Signed covariance obtained by finite Boolean-atom expansion. -/
def strictDoubledTimeNormalizedSignedCovariance
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') : Q' :=
  finiteHeterogeneousCrossBilinear
    (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace roots.length)
    leftCoefficient rightCoefficient
    (strictDoubledTimeNormalizedCovarianceKernel hadmissible hroots)

/-- The same signed assembly written entrywise with conventional Boolean
covariances `P(A ∩ B) - P(A)P(B)`. -/
def strictDoubledTimeBooleanCovarianceAssembly
    {radius base shift : Nat}
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
      anchorTwoBlockBooleanCovariance
        (centralAmbient radius)
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        (exactFingerprintPredicate leftBits)
        (exactFingerprintPredicate rightBits))

/-- Every kernel entry is exactly an ordinary finite-volume Boolean
covariance. -/
theorem strictDoubledTimeNormalizedCovarianceKernel_eqv_booleanCovariance
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftBits rightBits : List Bool) :
    strictDoubledTimeNormalizedCovarianceKernel
        hadmissible hroots leftBits rightBits ≈
      anchorTwoBlockBooleanCovariance
        (centralAmbient radius)
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        (exactFingerprintPredicate leftBits)
        (exactFingerprintPredicate rightBits) := by
  unfold strictDoubledTimeNormalizedCovarianceKernel
  exact Q'.eqv_symm
    (anchorTwoBlockBooleanCovariance_eqv_normalizedFourCell
      (centralAmbient radius)
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      (exactFingerprintPredicate leftBits)
      (exactFingerprintPredicate rightBits))

/-- The previously bounded signed determinant assembly is therefore exactly
a finite linear combination of conventional centered indicator moments. -/
theorem strictDoubledTimeNormalizedSignedCovariance_eqv_booleanAssembly
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    strictDoubledTimeNormalizedSignedCovariance
        hadmissible hroots leftCoefficient rightCoefficient ≈
      strictDoubledTimeBooleanCovarianceAssembly
        hadmissible hroots leftCoefficient rightCoefficient := by
  unfold strictDoubledTimeNormalizedSignedCovariance
    strictDoubledTimeBooleanCovarianceAssembly
    finiteHeterogeneousCrossBilinear
  apply listQSum_congr
  intro leftBits
  apply listQSum_congr
  intro rightBits
  exact Q'.mul_eqv_congr_left _ _ _
    (strictDoubledTimeNormalizedCovarianceKernel_eqv_booleanCovariance
      hadmissible hroots leftBits rightBits)

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

/-- A rectangular pair coefficient norm factors through the two ordinary
coefficient `l1` norms. -/
theorem heterogeneousCoefficientPairL1_le_l1_mul_l1
    {LeftState RightState : Type}
    (leftStates : List LeftState) (rightStates : List RightState)
    (leftCoefficient : LeftState → Q')
    (rightCoefficient : RightState → Q') :
    heterogeneousCoefficientPairL1
        leftStates rightStates leftCoefficient rightCoefficient ≤
      coefficientL1 leftStates leftCoefficient *
        coefficientL1 rightStates rightCoefficient := by
  have hpointwise :
      heterogeneousCoefficientPairL1
          leftStates rightStates leftCoefficient rightCoefficient ≤
        listQSum
          (fun left => listQSum
            (fun right =>
              Q'.abs (leftCoefficient left) *
                Q'.abs (rightCoefficient right))
            rightStates)
          leftStates := by
    unfold heterogeneousCoefficientPairL1
    apply listQSum_mono
    intro left hleft
    apply listQSum_mono
    intro right hright
    exact YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
      (leftCoefficient left) (rightCoefficient right)
  refine Q'.le_trans' _ _ _ hpointwise ?_
  exact Q'.le_of_eqv
    (listQSum_product
      (fun left => Q'.abs (leftCoefficient left))
      (fun right => Q'.abs (rightCoefficient right))
      leftStates rightStates)

/-- The finite signed-cylinder covariance is controlled by the literal
rectangular pair `l1` norm. -/
theorem strictDoubledTimeNormalizedSignedCovariance_abs_le_pairL1
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    Q'.abs (strictDoubledTimeNormalizedSignedCovariance
        hadmissible hroots leftCoefficient rightCoefficient) ≤
      heterogeneousCoefficientPairL1
          (strictJointFingerprintSpace roots.length)
          (strictJointFingerprintSpace roots.length)
          leftCoefficient rightCoefficient *
        strictDoubledTimeNormalizedCovarianceEpsilon
          roots.length shift := by
  let states := strictJointFingerprintSpace roots.length
  let covariance := strictDoubledTimeNormalizedCovarianceKernel
    hadmissible hroots
  let zeroLaw : List Bool → List Bool → Q' := fun _ _ => 0
  let epsilon := strictDoubledTimeNormalizedCovarianceEpsilon
    roots.length shift
  have hfinite := finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1
    states states leftCoefficient rightCoefficient covariance zeroLaw epsilon
    (fun left right hleft hright => by
      have hdifference : covariance left right + (-zeroLaw left right) ≈
          covariance left right := by
        exact add_neg_zero_eqv_local (covariance left right)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
        (strictDoubledTimeNormalizedCovarianceKernel_abs_le
          hadmissible hroots left right))
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
    (by simpa only [strictDoubledTimeNormalizedSignedCovariance,
        states, covariance, zeroLaw, epsilon] using hfinite)

/-- Factored signed-cylinder estimate with the standard product of coefficient
`l1` norms. -/
theorem strictDoubledTimeNormalizedSignedCovariance_abs_le_l1
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    Q'.abs (strictDoubledTimeNormalizedSignedCovariance
        hadmissible hroots leftCoefficient rightCoefficient) ≤
      (coefficientL1
          (strictJointFingerprintSpace roots.length) leftCoefficient *
        coefficientL1
          (strictJointFingerprintSpace roots.length) rightCoefficient) *
        strictDoubledTimeNormalizedCovarianceEpsilon
          roots.length shift := by
  refine Q'.le_trans' _ _ _
    (strictDoubledTimeNormalizedSignedCovariance_abs_le_pairL1
      hadmissible hroots leftCoefficient rightCoefficient) ?_
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (heterogeneousCoefficientPairL1_le_l1_mul_l1
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace roots.length)
      leftCoefficient rightCoefficient)
    (strictDoubledTimeNormalizedCovarianceEpsilon_nonnegative
      roots.length shift)

#print axioms strictDoubledTimeNormalizedCovarianceKernel_abs_le
#print axioms strictDoubledTimeNormalizedCovarianceKernel_eqv_booleanCovariance
#print axioms strictDoubledTimeNormalizedSignedCovariance_eqv_booleanAssembly
#print axioms heterogeneousCoefficientPairL1_le_l1_mul_l1
#print axioms strictDoubledTimeNormalizedSignedCovariance_abs_le_pairL1
#print axioms strictDoubledTimeNormalizedSignedCovariance_abs_le_l1

end YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance
