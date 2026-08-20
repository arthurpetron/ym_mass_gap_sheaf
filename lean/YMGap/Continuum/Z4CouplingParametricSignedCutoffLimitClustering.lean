/-
# Cutoff-removed signed covariance clustering at fixed volume

The arbitrary-cutoff signed estimate is uniform in the representation cutoff.
This module constructs the corresponding Bishop `CReal` at one fixed
admissible ambient volume.  Its approximants use the already derived joint
cutoff schedule, and the Cauchy proof compares two scheduled cutoffs through
their explicit sum.

The resulting limit inherits the common geometric rate `1/16`.  Its
prefactor is still the raw presentation-level coefficient norm.  No
thermodynamic identification with the completed OS moment, and no uniform
completed-space form gap, is asserted here.
-/

import YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
import YMGap.Continuum.Z4CouplingParametricCutoffTail
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.Z4CouplingParametricSignedCutoffLimitClustering

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CouplingParametricCutoffTail
open YMGap.Continuum.Z4CouplingParametricCylinderCofinal
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricTwoBlockProbabilityCovariance
open YMGap.Continuum.Z4CouplingParametricTwoBlockSignedCovariance
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem reassoc_cancel_local (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem abs_sub_triangle_local (a b c : Q') :
    Q'.abs (a - b) ≤ Q'.abs (a - c) + Q'.abs (c - b) := by
  have hdecompose : a - b ≈ (a - c) + (c - b) := by
    exact Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a - c) (c - b))

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

/-! ## 1. Stability of products and Boolean covariance under cutoff removal -/

private theorem probability_product_abs_sub_le
    {a b c d epsilon : Q'}
    (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ (1 : Q'))
    (hd0 : (0 : Q') ≤ d) (hd1 : d ≤ (1 : Q'))
    (hepsilon : (0 : Q') ≤ epsilon)
    (hb : Q'.abs (b - d) ≤ epsilon)
    (ha : Q'.abs (a - c) ≤ epsilon) :
    Q'.abs (a * b - c * d) ≤ epsilon + epsilon := by
  have hdecompose := CReal.mul_sub_decomp a b c d
  have htriangle := Q'.abs_add_le' (a * (b - d)) (d * (a - c))
  have hfirst : Q'.abs (a * (b - d)) ≤ epsilon := by
    refine Q'.le_trans' _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le a (b - d)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hb (Q'.abs_nonneg a)) ?_
    have habsA : Q'.abs a ≤ (1 : Q') := by
      rw [YMGap.Constructive.ExpNeg.abs_of_nonneg ha0]
      exact ha1
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ habsA hepsilon) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv epsilon)
  have hsecond : Q'.abs (d * (a - c)) ≤ epsilon := by
    refine Q'.le_trans' _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le d (a - c)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ ha (Q'.abs_nonneg d)) ?_
    have habsD : Q'.abs d ≤ (1 : Q') := by
      rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hd0]
      exact hd1
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ habsD hepsilon) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv epsilon)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.le_trans' _ _ _ htriangle (Q'.add_le_add hfirst hsecond))

/-- Extending the joint-cutoff schedule changes a two-block Boolean
covariance by at most three copies of the requested dyadic probability
error. -/
theorem couplingParametricKTwoBlockBooleanCovariance_jointCutoff_extension_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {precision n targetCutoff : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool)
    (hcutoff : spinSummedJointCutoff precision n ≤ targetCutoff) :
    Q'.abs
        (couplingParametricKTwoBlockBooleanCovariance hcoupling targetCutoff
            firstRoots secondRoots firstPredicate secondPredicate -
          couplingParametricKTwoBlockBooleanCovariance hcoupling
            (spinSummedJointCutoff precision n)
            firstRoots secondRoots firstPredicate secondPredicate) ≤
      HalfPow.half ^ precision +
        (HalfPow.half ^ precision + HalfPow.half ^ precision) := by
  let jointEvent : List (List Nat) → Bool := fun family =>
    blockCylinderEvent firstRoots firstPredicate family &&
      blockCylinderEvent secondRoots secondPredicate family
  let firstEvent := blockCylinderEvent firstRoots firstPredicate
  let secondEvent := blockCylinderEvent secondRoots secondPredicate
  let jointTarget :=
    couplingParametricKCompatibleSupportEventProbability coupling hcoupling
      targetCutoff n jointEvent
  let jointScheduled :=
    couplingParametricKCompatibleSupportEventProbability coupling hcoupling
      (spinSummedJointCutoff precision n) n jointEvent
  let firstTarget :=
    couplingParametricKCompatibleSupportEventProbability coupling hcoupling
      targetCutoff n firstEvent
  let firstScheduled :=
    couplingParametricKCompatibleSupportEventProbability coupling hcoupling
      (spinSummedJointCutoff precision n) n firstEvent
  let secondTarget :=
    couplingParametricKCompatibleSupportEventProbability coupling hcoupling
      targetCutoff n secondEvent
  let secondScheduled :=
    couplingParametricKCompatibleSupportEventProbability coupling hcoupling
      (spinSummedJointCutoff precision n) n secondEvent
  let epsilon := HalfPow.half ^ precision
  have hepsilon : (0 : Q') ≤ epsilon :=
    Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg precision
  have hjoint : Q'.abs (jointTarget - jointScheduled) ≤ epsilon := by
    dsimp only [jointTarget, jointScheduled, epsilon]
    exact
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle jointEvent hcutoff
  have hfirst : Q'.abs (firstTarget - firstScheduled) ≤ epsilon := by
    dsimp only [firstTarget, firstScheduled, epsilon]
    exact
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle firstEvent hcutoff
  have hsecond : Q'.abs (secondTarget - secondScheduled) ≤ epsilon := by
    dsimp only [secondTarget, secondScheduled, epsilon]
    exact
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle secondEvent hcutoff
  have hproduct :
      Q'.abs
          (firstTarget * secondTarget -
            firstScheduled * secondScheduled) ≤ epsilon + epsilon := by
    exact probability_product_abs_sub_le
      (couplingParametricKCompatibleSupportEventProbability_nonnegative
        hcoupling targetCutoff n firstEvent)
      (couplingParametricKCompatibleSupportEventProbability_le_one
        hcoupling targetCutoff n firstEvent)
      (couplingParametricKCompatibleSupportEventProbability_nonnegative
        hcoupling (spinSummedJointCutoff precision n) n secondEvent)
      (couplingParametricKCompatibleSupportEventProbability_le_one
        hcoupling (spinSummedJointCutoff precision n) n secondEvent)
      hepsilon hsecond hfirst
  have hdecompose :
      (jointTarget + (-(firstTarget * secondTarget))) +
          (-(jointScheduled + (-(firstScheduled * secondScheduled)))) ≈
        (jointTarget + (-jointScheduled)) +
          (-((firstTarget * secondTarget) +
            (-(firstScheduled * secondScheduled)))) := by
    ring_qeqv
  have htriangle := Q'.abs_add_le'
    (jointTarget - jointScheduled)
    (-(firstTarget * secondTarget - firstScheduled * secondScheduled))
  have hproductNeg :
      Q'.abs
          (-(firstTarget * secondTarget -
            firstScheduled * secondScheduled)) ≤ epsilon + epsilon := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_neg' (firstTarget * secondTarget -
          firstScheduled * secondScheduled))) hproduct
  change Q'.abs
      ((jointTarget - firstTarget * secondTarget) -
        (jointScheduled - firstScheduled * secondScheduled)) ≤
    epsilon + (epsilon + epsilon)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.le_trans' _ _ _ htriangle
      (Q'.add_le_add hjoint hproductNeg))

/-! ## 2. The scheduled signed covariance and its pair modulus -/

def couplingParametricStrictSignedCovarianceCutoffSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q')
    (stage : Nat) : Q' :=
  couplingParametricKStrictDoubledTimeBooleanCovarianceAssembly
    hcoupling (spinSummedJointCutoff stage (centralAmbient radius))
    hadmissible hroots leftCoefficient rightCoefficient

theorem couplingParametricStrictSignedCovarianceCutoffSequence_eqv_normalized
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {radius base shift stage : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    couplingParametricStrictSignedCovarianceCutoffSequence
        coupling hcoupling hadmissible hroots
        leftCoefficient rightCoefficient stage ≈
      couplingParametricKStrictDoubledTimeNormalizedSignedCovariance
        hcoupling (spinSummedJointCutoff stage (centralAmbient radius))
        hadmissible hroots leftCoefficient rightCoefficient := by
  exact Q'.eqv_symm
    (couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_eqv_booleanAssembly
      hcoupling (spinSummedJointCutoff stage (centralAmbient radius))
      hadmissible hroots leftCoefficient rightCoefficient)

def couplingParametricStrictSignedCutoffCauchyCoefficient
    {roots : List (List Nat)}
    (leftCoefficient rightCoefficient : List Bool → Q') : Q' :=
  let pairL1 := heterogeneousCoefficientPairL1
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace roots.length)
      leftCoefficient rightCoefficient
  (pairL1 + (pairL1 + pairL1)) +
    (pairL1 + (pairL1 + pairL1))

theorem couplingParametricStrictSignedCutoffCauchyCoefficient_nonnegative
    {roots : List (List Nat)}
    (leftCoefficient rightCoefficient : List Bool → Q') :
    (0 : Q') ≤ couplingParametricStrictSignedCutoffCauchyCoefficient
      (roots := roots) leftCoefficient rightCoefficient := by
  unfold couplingParametricStrictSignedCutoffCauchyCoefficient
  let pairL1 := heterogeneousCoefficientPairL1
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace roots.length)
      leftCoefficient rightCoefficient
  have hpair : (0 : Q') ≤ pairL1 :=
    heterogeneousCoefficientPairL1_nonnegative
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace roots.length)
      leftCoefficient rightCoefficient
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ hpair (Q'.zero_le_add _ _ hpair hpair))
    (Q'.zero_le_add _ _ hpair (Q'.zero_le_add _ _ hpair hpair))

private theorem couplingParametricStrictSignedCovarianceCutoffAssembly_extension_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {precision radius base shift targetCutoff : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q')
    (hcutoff : spinSummedJointCutoff precision (centralAmbient radius) ≤
      targetCutoff) :
    Q'.abs
        (couplingParametricKStrictDoubledTimeBooleanCovarianceAssembly
            hcoupling targetCutoff hadmissible hroots
            leftCoefficient rightCoefficient -
          couplingParametricKStrictDoubledTimeBooleanCovarianceAssembly
            hcoupling
              (spinSummedJointCutoff precision (centralAmbient radius))
            hadmissible hroots leftCoefficient rightCoefficient) ≤
      heterogeneousCoefficientPairL1
          (strictJointFingerprintSpace roots.length)
          (strictJointFingerprintSpace roots.length)
          leftCoefficient rightCoefficient *
        (HalfPow.half ^ precision +
          (HalfPow.half ^ precision + HalfPow.half ^ precision)) := by
  unfold couplingParametricKStrictDoubledTimeBooleanCovarianceAssembly
  exact finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1
    (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace roots.length)
    leftCoefficient rightCoefficient
    (fun leftBits rightBits =>
      couplingParametricKTwoBlockBooleanCovariance hcoupling targetCutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        (exactFingerprintPredicate leftBits)
        (exactFingerprintPredicate rightBits))
    (fun leftBits rightBits =>
      couplingParametricKTwoBlockBooleanCovariance hcoupling
        (spinSummedJointCutoff precision (centralAmbient radius))
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        (exactFingerprintPredicate leftBits)
        (exactFingerprintPredicate rightBits))
    (HalfPow.half ^ precision +
      (HalfPow.half ^ precision + HalfPow.half ^ precision))
    (fun leftBits rightBits hleft hright =>
      couplingParametricKTwoBlockBooleanCovariance_jointCutoff_extension_abs_le
        hcoupling hle
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        (exactFingerprintPredicate leftBits)
        (exactFingerprintPredicate rightBits) hcutoff)

theorem couplingParametricStrictSignedCovarianceCutoffSequence_pair_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {radius base shift earlier later : Nat} (hstage : earlier ≤ later)
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    Q'.abs
        (couplingParametricStrictSignedCovarianceCutoffSequence
            coupling hcoupling hadmissible hroots
            leftCoefficient rightCoefficient later -
          couplingParametricStrictSignedCovarianceCutoffSequence
            coupling hcoupling hadmissible hroots
            leftCoefficient rightCoefficient earlier) ≤
      couplingParametricStrictSignedCutoffCauchyCoefficient
          (roots := roots) leftCoefficient rightCoefficient *
        HalfPow.half ^ earlier := by
  let n := centralAmbient radius
  let earlierCutoff := spinSummedJointCutoff earlier n
  let laterCutoff := spinSummedJointCutoff later n
  let commonCutoff := earlierCutoff + laterCutoff
  let earlierValue :=
    couplingParametricStrictSignedCovarianceCutoffSequence
      coupling hcoupling hadmissible hroots
      leftCoefficient rightCoefficient earlier
  let laterValue :=
    couplingParametricStrictSignedCovarianceCutoffSequence
      coupling hcoupling hadmissible hroots
      leftCoefficient rightCoefficient later
  let commonValue :=
    couplingParametricKStrictDoubledTimeBooleanCovarianceAssembly
      hcoupling commonCutoff hadmissible hroots
      leftCoefficient rightCoefficient
  let pairL1 := heterogeneousCoefficientPairL1
    (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace roots.length)
    leftCoefficient rightCoefficient
  let earlyError := HalfPow.half ^ earlier
  let lateError := HalfPow.half ^ later
  have hearlierCutoff : earlierCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hlaterCutoff : laterCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hearlier : Q'.abs (commonValue - earlierValue) ≤
      pairL1 * (earlyError + (earlyError + earlyError)) := by
    dsimp only [commonValue, earlierValue, pairL1, earlyError,
      couplingParametricStrictSignedCovarianceCutoffSequence,
      earlierCutoff, n]
    exact
      couplingParametricStrictSignedCovarianceCutoffAssembly_extension_abs_le
        hcoupling hle hadmissible hroots
        leftCoefficient rightCoefficient hearlierCutoff
  have hlaterRaw : Q'.abs (commonValue - laterValue) ≤
      pairL1 * (lateError + (lateError + lateError)) := by
    dsimp only [commonValue, laterValue, pairL1, lateError,
      couplingParametricStrictSignedCovarianceCutoffSequence,
      laterCutoff, n]
    exact
      couplingParametricStrictSignedCovarianceCutoffAssembly_extension_abs_le
        hcoupling hle hadmissible hroots
        leftCoefficient rightCoefficient hlaterCutoff
  have hhalf : lateError ≤ earlyError := by
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
    dsimp only [lateError, earlyError]
    rw [hoffset]
    exact ExpNeg.pow_half_antitone earlier offset
  have htriple : lateError + (lateError + lateError) ≤
      earlyError + (earlyError + earlyError) :=
    Q'.add_le_add hhalf (Q'.add_le_add hhalf hhalf)
  have hpairNonnegative : (0 : Q') ≤ pairL1 := by
    dsimp only [pairL1]
    exact heterogeneousCoefficientPairL1_nonnegative
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace roots.length)
      leftCoefficient rightCoefficient
  have hlaterCommon : Q'.abs (laterValue - commonValue) ≤
      pairL1 * (earlyError + (earlyError + earlyError)) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          laterValue commonValue)) ?_
    exact Q'.le_trans' _ _ _ hlaterRaw
      (Q'.mul_le_mul_of_nonneg_left _ _ _ htriple hpairNonnegative)
  have htriangle := abs_sub_triangle_local laterValue earlierValue commonValue
  have hsum :
      pairL1 * (earlyError + (earlyError + earlyError)) +
          pairL1 * (earlyError + (earlyError + earlyError)) ≈
        couplingParametricStrictSignedCutoffCauchyCoefficient
            (roots := roots) leftCoefficient rightCoefficient *
          earlyError := by
    unfold couplingParametricStrictSignedCutoffCauchyCoefficient
    dsimp only [pairL1, earlyError]
    ring_qeqv
  change Q'.abs (laterValue - earlierValue) ≤ _
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _
      (Q'.add_le_add hlaterCommon hearlier)
      (Q'.le_of_eqv hsum))

/-! ## 3. The cutoff-removed constructive real and its geometric bound -/

def couplingParametricStrictSignedCovarianceCutoffLimit
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') : CReal where
  approx := couplingParametricStrictSignedCovarianceCutoffSequence
    coupling hcoupling hadmissible hroots
    leftCoefficient rightCoefficient
  cauchy := by
    intro epsilon hepsilon
    let coefficient := couplingParametricStrictSignedCutoffCauchyCoefficient
      (roots := roots) leftCoefficient rightCoefficient
    let scaledTolerance := epsilon * Q'.invSucc coefficient.num.toNat
    have hcoefficient : (0 : Q') ≤ coefficient :=
      couplingParametricStrictSignedCutoffCauchyCoefficient_nonnegative
        (roots := roots) leftCoefficient rightCoefficient
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
    have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
      ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
        hcoefficient (Q'.le_of_lt hepsilon)
    refine ⟨scaledTolerance.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · have hpair :=
        couplingParametricStrictSignedCovarianceCutoffSequence_pair_abs_le
          hcoupling hle hmn hadmissible hroots
          leftCoefficient rightCoefficient
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hm
      have hhalf : HalfPow.half ^ m ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ m) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricStrictSignedCovarianceCutoffSequence
              coupling hcoupling hadmissible hroots
              leftCoefficient rightCoefficient n -
            couplingParametricStrictSignedCovarianceCutoffSequence
              coupling hcoupling hadmissible hroots
              leftCoefficient rightCoefficient m) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      have htwo := two_sided_add_of_abs_sub_le_local habs
      exact ⟨htwo.2, htwo.1⟩
    · have hpair :=
        couplingParametricStrictSignedCovarianceCutoffSequence_pair_abs_le
          hcoupling hle hnm hadmissible hroots
          leftCoefficient rightCoefficient
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hn
      have hhalf : HalfPow.half ^ n ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ n) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricStrictSignedCovarianceCutoffSequence
              coupling hcoupling hadmissible hroots
              leftCoefficient rightCoefficient m -
            couplingParametricStrictSignedCovarianceCutoffSequence
              coupling hcoupling hadmissible hroots
              leftCoefficient rightCoefficient n) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      exact two_sided_add_of_abs_sub_le_local habs

@[simp] theorem couplingParametricStrictSignedCovarianceCutoffLimit_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {radius base shift stage : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    (couplingParametricStrictSignedCovarianceCutoffLimit
      coupling hcoupling hle hadmissible hroots
      leftCoefficient rightCoefficient).approx stage =
      couplingParametricStrictSignedCovarianceCutoffSequence
        coupling hcoupling hadmissible hroots
        leftCoefficient rightCoefficient stage := rfl

/-- The cutoff-removed signed covariance inherits the same `1/16` geometric
envelope as every finite-cutoff approximant. -/
theorem couplingParametricStrictSignedCovarianceCutoffLimit_abs_le_geometric
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    CReal.abs
        (couplingParametricStrictSignedCovarianceCutoffLimit
          coupling hcoupling hle hadmissible hroots
          leftCoefficient rightCoefficient) ≤
      CReal.ofQ'
        (couplingParametricStrictSignedPositivePrefactor roots.length
            (strictJointFingerprintSpace roots.length)
            (strictJointFingerprintSpace roots.length)
            leftCoefficient rightCoefficient *
          anchorDecoratedDoubledTimeRate ^ shift) := by
  apply CReal.le_ofQ'_of_approx_le
  intro stage
  rw [CReal.abs_approx,
    couplingParametricStrictSignedCovarianceCutoffLimit_approx]
  have heq :=
    couplingParametricStrictSignedCovarianceCutoffSequence_eqv_normalized
      hcoupling hadmissible hroots
      leftCoefficient rightCoefficient (stage := stage)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr heq)) ?_
  exact
    couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_abs_le_geometric
      hcoupling hle
      (spinSummedJointCutoff stage (centralAmbient radius))
      hadmissible hroots leftCoefficient rightCoefficient

#print axioms couplingParametricKTwoBlockBooleanCovariance_jointCutoff_extension_abs_le
#print axioms couplingParametricStrictSignedCovarianceCutoffSequence_pair_abs_le
#print axioms couplingParametricStrictSignedCovarianceCutoffLimit
#print axioms couplingParametricStrictSignedCovarianceCutoffLimit_abs_le_geometric

end YMGap.Continuum.Z4CouplingParametricSignedCutoffLimitClustering
