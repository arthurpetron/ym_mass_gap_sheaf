/-
# Arbitrary-cutoff signed covariance as a centered observable moment

The arbitrary-cutoff cluster estimate is currently stated as a finite sum of
Boolean fingerprint covariances.  This file performs the exact finite algebra
which rewrites that sum as

  `E[F * G] - E[F] * E[G]`

for the two rational cylinder observables.  The identity holds at every
finite volume and representation cutoff.  Its strict doubled-time
specialization therefore inherits the common geometric rate `1/16`.

No cutoff or volume limit is taken here, and the coefficient norm remains a
presentation-level quantity.
-/

import YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering

namespace YMGap.Continuum.Z4CouplingParametricTwoBlockObservableCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricTwoBlockProbabilityCovariance
open YMGap.Continuum.Z4CouplingParametricTwoBlockSignedCovariance
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem listQSum_neg_local {A : Type} (f : A → Q') :
    ∀ xs : List A,
      listQSum (fun item => -(f item)) xs ≈ -(listQSum f xs)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(f head) + -(listQSum f tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _) (listQSum_neg_local f tail)
      · exact Q'.eqv_symm (Q'.neg_add_eqv (f head) (listQSum f tail))

private theorem listQSum_sub_local {A : Type} (f g : A → Q')
    (xs : List A) :
    listQSum (fun item => f item - g item) xs ≈
      listQSum f xs - listQSum g xs := by
  refine Q'.eqv_trans _
    (listQSum f xs + listQSum (fun item => -(g item)) xs) _ ?_ ?_
  · exact listQSum_add f (fun item => -(g item)) xs
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_neg_local g xs)

private theorem finiteHeterogeneousCrossBilinear_sub_local
    {Left Right : Type}
    (leftStates : List Left) (rightStates : List Right)
    (leftCoefficient : Left → Q') (rightCoefficient : Right → Q')
    (first second : Left → Right → Q') :
    finiteHeterogeneousCrossBilinear
        leftStates rightStates leftCoefficient rightCoefficient
        (fun left right => first left right - second left right) ≈
      finiteHeterogeneousCrossBilinear
          leftStates rightStates leftCoefficient rightCoefficient first -
        finiteHeterogeneousCrossBilinear
          leftStates rightStates leftCoefficient rightCoefficient second := by
  unfold finiteHeterogeneousCrossBilinear
  let firstRow : Left → Q' := fun left =>
    listQSum (fun right =>
      (leftCoefficient left * rightCoefficient right) * first left right)
      rightStates
  let secondRow : Left → Q' := fun left =>
    listQSum (fun right =>
      (leftCoefficient left * rightCoefficient right) * second left right)
      rightStates
  refine Q'.eqv_trans _
    (listQSum (fun left => firstRow left - secondRow left) leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum (fun right =>
        (leftCoefficient left * rightCoefficient right) * first left right -
          (leftCoefficient left * rightCoefficient right) * second left right)
        rightStates) _ ?_ ?_
    · apply listQSum_congr
      intro right
      refine Q'.eqv_trans _
        ((leftCoefficient left * rightCoefficient right) * first left right +
          (leftCoefficient left * rightCoefficient right) *
            (-(second left right))) _ ?_ ?_
      · exact Q'.mul_add_eqv
          (leftCoefficient left * rightCoefficient right)
          (first left right) (-(second left right))
      · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_neg_eqv
            (leftCoefficient left * rightCoefficient right)
            (second left right))
    · exact listQSum_sub_local
        (fun right =>
          (leftCoefficient left * rightCoefficient right) * first left right)
        (fun right =>
          (leftCoefficient left * rightCoefficient right) * second left right)
        rightStates
  · exact listQSum_sub_local firstRow secondRow leftStates

/-! ## 1. Finite observable expectations -/

def couplingParametricKBlockObservableExpectation
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat}
    (roots : List (CanonicalAtom n))
    (coefficient : List Bool → Q') : Q' :=
  listQSum (fun bits => coefficient bits *
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff n
        (blockCylinderEvent roots (exactFingerprintPredicate bits)))
    (strictJointFingerprintSpace roots.length)

def couplingParametricKTwoBlockProductExpectation
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstCoefficient secondCoefficient : List Bool → Q') : Q' :=
  finiteHeterogeneousCrossBilinear
    (strictJointFingerprintSpace firstRoots.length)
    (strictJointFingerprintSpace secondRoots.length)
    firstCoefficient secondCoefficient
    (fun firstBits secondBits =>
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff n (fun family =>
          blockCylinderEvent firstRoots
              (exactFingerprintPredicate firstBits) family &&
            blockCylinderEvent secondRoots
              (exactFingerprintPredicate secondBits) family))

def couplingParametricKTwoBlockObservableCovariance
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstCoefficient secondCoefficient : List Bool → Q') : Q' :=
  couplingParametricKTwoBlockProductExpectation hcoupling cutoff
      firstRoots secondRoots firstCoefficient secondCoefficient -
    couplingParametricKBlockObservableExpectation hcoupling cutoff
        firstRoots firstCoefficient *
      couplingParametricKBlockObservableExpectation hcoupling cutoff
        secondRoots secondCoefficient

/-! ## 2. Exact atom-covariance assembly -/

theorem couplingParametricKTwoBlockBooleanAssembly_eqv_observableCovariance
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstCoefficient secondCoefficient : List Bool → Q') :
    finiteHeterogeneousCrossBilinear
        (strictJointFingerprintSpace firstRoots.length)
        (strictJointFingerprintSpace secondRoots.length)
        firstCoefficient secondCoefficient
        (fun firstBits secondBits =>
          couplingParametricKTwoBlockBooleanCovariance hcoupling cutoff
            firstRoots secondRoots
            (exactFingerprintPredicate firstBits)
            (exactFingerprintPredicate secondBits)) ≈
      couplingParametricKTwoBlockObservableCovariance hcoupling cutoff
        firstRoots secondRoots firstCoefficient secondCoefficient := by
  let firstStates := strictJointFingerprintSpace firstRoots.length
  let secondStates := strictJointFingerprintSpace secondRoots.length
  let jointLaw : List Bool → List Bool → Q' := fun firstBits secondBits =>
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff n (fun family =>
        blockCylinderEvent firstRoots
            (exactFingerprintPredicate firstBits) family &&
          blockCylinderEvent secondRoots
            (exactFingerprintPredicate secondBits) family)
  let firstLaw : List Bool → Q' := fun firstBits =>
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff n
      (blockCylinderEvent firstRoots
        (exactFingerprintPredicate firstBits))
  let secondLaw : List Bool → Q' := fun secondBits =>
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff n
      (blockCylinderEvent secondRoots
        (exactFingerprintPredicate secondBits))
  let productLaw : List Bool → List Bool → Q' :=
    fun firstBits secondBits => firstLaw firstBits * secondLaw secondBits
  have hsplit :
      finiteHeterogeneousCrossBilinear
          firstStates secondStates firstCoefficient secondCoefficient
          (fun firstBits secondBits =>
            couplingParametricKTwoBlockBooleanCovariance hcoupling cutoff
              firstRoots secondRoots
              (exactFingerprintPredicate firstBits)
              (exactFingerprintPredicate secondBits)) ≈
        finiteHeterogeneousCrossBilinear
            firstStates secondStates firstCoefficient secondCoefficient
            jointLaw -
          finiteHeterogeneousCrossBilinear
            firstStates secondStates firstCoefficient secondCoefficient
            productLaw := by
    simpa only [firstStates, secondStates, jointLaw, firstLaw, secondLaw,
      productLaw, couplingParametricKTwoBlockBooleanCovariance] using
      (finiteHeterogeneousCrossBilinear_sub_local
        firstStates secondStates firstCoefficient secondCoefficient
        jointLaw productLaw)
  have hproduct :
      finiteHeterogeneousCrossBilinear
          firstStates secondStates firstCoefficient secondCoefficient
          productLaw ≈
        couplingParametricKBlockObservableExpectation hcoupling cutoff
            firstRoots firstCoefficient *
          couplingParametricKBlockObservableExpectation hcoupling cutoff
            secondRoots secondCoefficient := by
    unfold finiteHeterogeneousCrossBilinear productLaw
      couplingParametricKBlockObservableExpectation
    refine Q'.eqv_trans _
      (listQSum (fun firstBits => listQSum (fun secondBits =>
        (firstCoefficient firstBits * firstLaw firstBits) *
          (secondCoefficient secondBits * secondLaw secondBits))
        secondStates) firstStates) _ ?_ ?_
    · apply listQSum_congr
      intro firstBits
      apply listQSum_congr
      intro secondBits
      ring_qeqv
    exact listQSum_product
      (fun firstBits => firstCoefficient firstBits * firstLaw firstBits)
      (fun secondBits => secondCoefficient secondBits * secondLaw secondBits)
      firstStates secondStates
  refine Q'.eqv_trans _ _ _ hsplit ?_
  unfold couplingParametricKTwoBlockObservableCovariance
    couplingParametricKTwoBlockProductExpectation
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _)
    (Q'.neg_eqv_congr _ _ hproduct)

/-! ## 3. Strict doubled-time specialization and geometric rate -/

theorem couplingParametricKStrictDoubledTimeSignedCovariance_eqv_observable
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    couplingParametricKStrictDoubledTimeBooleanCovarianceAssembly
        hcoupling cutoff hadmissible hroots
        leftCoefficient rightCoefficient ≈
      couplingParametricKTwoBlockObservableCovariance hcoupling cutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        leftCoefficient rightCoefficient := by
  unfold couplingParametricKStrictDoubledTimeBooleanCovarianceAssembly
  have hlower := strictJointDoubledTimeLowerRootAtoms_length
    hadmissible hroots
  have hupper := strictJointDoubledTimeUpperRootAtoms_length
    hadmissible hroots
  simpa only [hlower, hupper] using
    (couplingParametricKTwoBlockBooleanAssembly_eqv_observableCovariance
      hcoupling cutoff
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      leftCoefficient rightCoefficient)

/-- The conventional finite-volume connected observable moment inherits the
same presentation prefactor and common `1/16` temporal rate. -/
theorem couplingParametricKStrictDoubledTimeObservableCovariance_abs_le_geometric
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    Q'.abs
        (couplingParametricKTwoBlockObservableCovariance hcoupling cutoff
          (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
          (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
          leftCoefficient rightCoefficient) ≤
      couplingParametricStrictSignedPositivePrefactor roots.length
          (strictJointFingerprintSpace roots.length)
          (strictJointFingerprintSpace roots.length)
          leftCoefficient rightCoefficient *
        anchorDecoratedDoubledTimeRate ^ shift := by
  have hidentity :=
    couplingParametricKStrictDoubledTimeSignedCovariance_eqv_observable
      hcoupling cutoff hadmissible hroots
      leftCoefficient rightCoefficient
  have hnormalized :=
    couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_eqv_booleanAssembly
      hcoupling cutoff hadmissible hroots
      leftCoefficient rightCoefficient
  have hcombined :
      couplingParametricKStrictDoubledTimeNormalizedSignedCovariance
          hcoupling cutoff hadmissible hroots
          leftCoefficient rightCoefficient ≈
        couplingParametricKTwoBlockObservableCovariance hcoupling cutoff
          (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
          (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
          leftCoefficient rightCoefficient :=
    Q'.eqv_trans _ _ _ hnormalized hidentity
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hcombined))) ?_
  exact
    couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_abs_le_geometric
      hcoupling hle cutoff hadmissible hroots
      leftCoefficient rightCoefficient

#print axioms couplingParametricKTwoBlockBooleanAssembly_eqv_observableCovariance
#print axioms couplingParametricKStrictDoubledTimeSignedCovariance_eqv_observable
#print axioms couplingParametricKStrictDoubledTimeObservableCovariance_abs_le_geometric

end YMGap.Continuum.Z4CouplingParametricTwoBlockObservableCovariance
