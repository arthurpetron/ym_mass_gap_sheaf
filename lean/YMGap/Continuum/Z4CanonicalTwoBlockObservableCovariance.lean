/-
# Signed cylinder covariance as an ordinary centered observable moment

The exact Boolean fingerprint atoms form a finite, duplicate-free partition
of every cylinder chart.  This module uses constructive finite pushforward
algebra to prove that the signed sum of atom covariances is exactly

  E[F G] - E[F] E[G]

for the corresponding rational cylinder observables.  Specializing to the
strict doubled-time charts identifies the previously bounded signed
determinant assembly with a conventional centered moment on the literal
finite canonical polymer measure.

No thermodynamic limit or spectral representation is used here.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance
import YMGap.Continuum.FiniteCoefficientZeroExtension

namespace YMGap.Continuum.Z4CanonicalTwoBlockObservableCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockNormalizedCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockProbabilityCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
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

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

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
            (-(second left right))) _
        (Q'.mul_add_eqv
          (leftCoefficient left * rightCoefficient right)
          (first left right) (-(second left right))) ?_
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
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

/-! ## 1. Literal finite observables and their centered moment -/

def blockCylinderObservable
    {n : Nat} (roots : List (CanonicalAtom n))
    (coefficient : List Bool → Q') : TwoBlockPolymerFamily → Q' :=
  fun family => coefficient
    (familyOccurrenceFingerprint (roots.map Subtype.val) family)

def anchorObservableExpectation
    (n : Nat) (observable : TwoBlockPolymerFamily → Q') : Q' :=
  Q'.divPos
    (listQSum
      (fun family =>
        canonicalSurfaceFamilyActivity anchorCoupling n family *
          observable family)
      (canonicalCompatibleAmbientFamilies n))
    (anchorCanonicalPartition n) (anchorCanonicalPartition_pos n)

def anchorBlockObservableExpectation
    {n : Nat} (roots : List (CanonicalAtom n))
    (coefficient : List Bool → Q') : Q' :=
  anchorObservableExpectation n
    (blockCylinderObservable roots coefficient)

def anchorTwoBlockProductExpectation
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstCoefficient secondCoefficient : List Bool → Q') : Q' :=
  anchorObservableExpectation n (fun family =>
    blockCylinderObservable firstRoots firstCoefficient family *
      blockCylinderObservable secondRoots secondCoefficient family)

def anchorTwoBlockObservableCovariance
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstCoefficient secondCoefficient : List Bool → Q') : Q' :=
  anchorTwoBlockProductExpectation firstRoots secondRoots
      firstCoefficient secondCoefficient -
    anchorBlockObservableExpectation firstRoots firstCoefficient *
      anchorBlockObservableExpectation secondRoots secondCoefficient

/-! ## 2. Exact fingerprint-atom pushforward -/

private theorem exactCodeEventNumerator_eqv_fiberWeight
    {Target : Type} [DecidableEq Target]
    (n : Nat) (code : TwoBlockPolymerFamily → Target) (target : Target) :
    anchorEventNumerator n (fun family => decide (code family = target)) ≈
      fiberWeight
        (canonicalCompatibleAmbientFamilies n)
        (canonicalSurfaceFamilyActivity anchorCoupling n)
        code target := by
  unfold anchorEventNumerator fiberWeight
  have hfilter :
      (canonicalCompatibleAmbientFamilies n).filter
          (fun family => decide (code family = target)) =
        (canonicalCompatibleAmbientFamilies n).filter
          (fun family => decide (target = code family)) := by
    apply List.filter_congr
    intro family hfamily
    by_cases h : code family = target
    · simp [h]
    · have hreverse : target ≠ code family := by
        intro hback
        exact h hback.symm
      simp [h, hreverse]
  rw [hfilter]
  exact Q'.eqv_refl _

private theorem exactPairEventNumerator_eqv_fiberWeight
    {Left Right : Type} [DecidableEq Left] [DecidableEq Right]
    (n : Nat)
    (leftCode : TwoBlockPolymerFamily → Left)
    (rightCode : TwoBlockPolymerFamily → Right)
    (left : Left) (right : Right) :
    anchorEventNumerator n (fun family =>
        decide (leftCode family = left) &&
          decide (rightCode family = right)) ≈
      fiberWeight
        (canonicalCompatibleAmbientFamilies n)
        (canonicalSurfaceFamilyActivity anchorCoupling n)
        (fun family => (leftCode family, rightCode family))
        (left, right) := by
  unfold anchorEventNumerator fiberWeight
  have hfilter :
      (canonicalCompatibleAmbientFamilies n).filter (fun family =>
          decide (leftCode family = left) &&
            decide (rightCode family = right)) =
        (canonicalCompatibleAmbientFamilies n).filter (fun family =>
          decide ((left, right) =
            (leftCode family, rightCode family))) := by
    apply List.filter_congr
    intro family hfamily
    by_cases hleft : leftCode family = left <;>
      by_cases hright : rightCode family = right
    · simp [hleft, hright]
    · have hpair : (left, right) ≠
          (leftCode family, rightCode family) := by
        intro hp
        exact hright (congrArg Prod.snd hp).symm
      have hrightReverse : right ≠ rightCode family := by
        intro heq
        exact hright heq.symm
      simp [hleft, hright, hrightReverse]
    · have hpair : (left, right) ≠
          (leftCode family, rightCode family) := by
        intro hp
        exact hleft (congrArg Prod.fst hp).symm
      simp [hleft, hpair]
    · have hpair : (left, right) ≠
          (leftCode family, rightCode family) := by
        intro hp
        exact hleft (congrArg Prod.fst hp).symm
      simp [hleft, hright, hpair]
  rw [hfilter]
  exact Q'.eqv_refl _

private theorem normalizedAtomMoment_eqv_observableExpectation
    {Target : Type} [DecidableEq Target]
    (n : Nat) (code : TwoBlockPolymerFamily → Target)
    (targets : List Target) (hnodup : targets.Nodup)
    (hcoverage : ∀ family,
      family ∈ canonicalCompatibleAmbientFamilies n →
        code family ∈ targets)
    (coefficient : Target → Q') :
    listQSum (fun target =>
        coefficient target *
          anchorEventProbability n
            (fun family => decide (code family = target))) targets ≈
      anchorObservableExpectation n
        (fun family => coefficient (code family)) := by
  let source := canonicalCompatibleAmbientFamilies n
  let weight := canonicalSurfaceFamilyActivity anchorCoupling n
  let z := anchorCanonicalPartition n
  let recip := Q'.recipPos z (anchorCanonicalPartition_pos n)
  have hraw := finiteCoefficientZeroExtension_reindex_mul
    source weight code targets hnodup hcoverage coefficient
  unfold anchorEventProbability anchorObservableExpectation Q'.divPos
  refine Q'.eqv_trans _
    (listQSum (fun target =>
      (fiberWeight source weight code target * coefficient target) * recip)
      targets) _ ?_ ?_
  · apply listQSum_congr
    intro target
    have hevent := exactCodeEventNumerator_eqv_fiberWeight n code target
    refine Q'.eqv_trans _
      ((coefficient target * anchorEventNumerator n
          (fun family => decide (code family = target))) * recip) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact mul_eqv_both_local
      (Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv (coefficient target)
          (anchorEventNumerator n
            (fun family => decide (code family = target))))
        (Q'.mul_eqv_congr_right _ _ _ hevent))
      (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (listQSum
      (fun target => fiberWeight source weight code target * coefficient target)
      targets * recip) _ ?_ ?_
  · exact listQSum_mul_right _ recip targets
  exact Q'.mul_eqv_congr_right _ _ recip hraw

private theorem normalizedJointAtomMoment_eqv_productExpectation
    {Left Right : Type} [DecidableEq Left] [DecidableEq Right]
    (n : Nat)
    (leftCode : TwoBlockPolymerFamily → Left)
    (rightCode : TwoBlockPolymerFamily → Right)
    (leftTargets : List Left) (rightTargets : List Right)
    (hleftNodup : leftTargets.Nodup)
    (hrightNodup : rightTargets.Nodup)
    (hleft : ∀ family, family ∈ canonicalCompatibleAmbientFamilies n →
      leftCode family ∈ leftTargets)
    (hright : ∀ family, family ∈ canonicalCompatibleAmbientFamilies n →
      rightCode family ∈ rightTargets)
    (leftCoefficient : Left → Q') (rightCoefficient : Right → Q') :
    finiteHeterogeneousCrossBilinear
        leftTargets rightTargets leftCoefficient rightCoefficient
        (fun left right =>
          anchorEventProbability n (fun family =>
            decide (leftCode family = left) &&
              decide (rightCode family = right))) ≈
      anchorObservableExpectation n (fun family =>
        leftCoefficient (leftCode family) *
          rightCoefficient (rightCode family)) := by
  let source := canonicalCompatibleAmbientFamilies n
  let weight := canonicalSurfaceFamilyActivity anchorCoupling n
  let pairCode : TwoBlockPolymerFamily → Left × Right := fun family =>
    (leftCode family, rightCode family)
  let targetPairs := cartesian leftTargets rightTargets
  let pairCoefficient : Left × Right → Q' := fun pair =>
    leftCoefficient pair.1 * rightCoefficient pair.2
  let z := anchorCanonicalPartition n
  let recip := Q'.recipPos z (anchorCanonicalPartition_pos n)
  have htargetNodup : targetPairs.Nodup :=
    cartesian_nodup leftTargets rightTargets hleftNodup hrightNodup
  have hpairsCovered : ∀ family, family ∈ source →
      pairCode family ∈ targetPairs := by
    intro family hfamily
    exact (mem_cartesian_iff leftTargets rightTargets (pairCode family)).2
      ⟨hleft family hfamily, hright family hfamily⟩
  have hraw := finiteCoefficientZeroExtension_reindex_mul
    source weight pairCode targetPairs htargetNodup hpairsCovered
    pairCoefficient
  unfold finiteHeterogeneousCrossBilinear anchorEventProbability
    anchorObservableExpectation Q'.divPos
  refine Q'.eqv_trans _
    (listQSum (fun left => listQSum (fun right =>
      (fiberWeight source weight pairCode (left, right) *
        (leftCoefficient left * rightCoefficient right)) * recip)
      rightTargets) leftTargets) _ ?_ ?_
  · apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    have hevent := exactPairEventNumerator_eqv_fiberWeight
      n leftCode rightCode left right
    refine Q'.eqv_trans _
      (((leftCoefficient left * rightCoefficient right) *
          anchorEventNumerator n (fun family =>
            decide (leftCode family = left) &&
              decide (rightCode family = right))) * recip) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact mul_eqv_both_local
      (Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv
          (leftCoefficient left * rightCoefficient right)
          (anchorEventNumerator n (fun family =>
            decide (leftCode family = left) &&
              decide (rightCode family = right))))
        (Q'.mul_eqv_congr_right _ _ _ hevent))
      (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (listQSum (fun left =>
      listQSum (fun right =>
        fiberWeight source weight pairCode (left, right) *
          (leftCoefficient left * rightCoefficient right)) rightTargets * recip)
      leftTargets) _ ?_ ?_
  · apply listQSum_congr
    intro left
    exact listQSum_mul_right _ recip rightTargets
  refine Q'.eqv_trans _
    (listQSum (fun left =>
      listQSum (fun right =>
        fiberWeight source weight pairCode (left, right) *
          (leftCoefficient left * rightCoefficient right)) rightTargets)
      leftTargets * recip) _ ?_ ?_
  · exact listQSum_mul_right _ recip leftTargets
  have hcartesian :
      listQSum (fun pair =>
          fiberWeight source weight pairCode pair * pairCoefficient pair)
          targetPairs ≈
        listQSum (fun left => listQSum (fun right =>
          fiberWeight source weight pairCode (left, right) *
            (leftCoefficient left * rightCoefficient right))
          rightTargets) leftTargets := by
    exact listQSum_cartesian_eq_nested
      (fun pair => fiberWeight source weight pairCode pair *
        pairCoefficient pair) leftTargets rightTargets
  have hnested :
      listQSum (fun left => listQSum (fun right =>
          fiberWeight source weight pairCode (left, right) *
            (leftCoefficient left * rightCoefficient right))
        rightTargets) leftTargets ≈
      listQSum (fun family =>
        weight family * pairCoefficient (pairCode family)) source :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hcartesian) hraw
  exact Q'.mul_eqv_congr_right _ _ recip hnested

/-! ## 3. Atom sums equal the ordinary centered moment -/

def anchorTwoBlockObservableAtomCovarianceAssembly
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstCoefficient secondCoefficient : List Bool → Q') : Q' :=
  finiteHeterogeneousCrossBilinear
    (strictJointFingerprintSpace firstRoots.length)
    (strictJointFingerprintSpace secondRoots.length)
    firstCoefficient secondCoefficient
    (fun firstBits secondBits =>
      anchorTwoBlockBooleanCovariance n firstRoots secondRoots
        (exactFingerprintPredicate firstBits)
        (exactFingerprintPredicate secondBits))

theorem anchorTwoBlockObservableAtomCovarianceAssembly_eqv_covariance
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstCoefficient secondCoefficient : List Bool → Q') :
    anchorTwoBlockObservableAtomCovarianceAssembly
        firstRoots secondRoots firstCoefficient secondCoefficient ≈
      anchorTwoBlockObservableCovariance
        firstRoots secondRoots firstCoefficient secondCoefficient := by
  let firstStates := strictJointFingerprintSpace firstRoots.length
  let secondStates := strictJointFingerprintSpace secondRoots.length
  let firstCode : TwoBlockPolymerFamily → List Bool := fun family =>
    familyOccurrenceFingerprint (firstRoots.map Subtype.val) family
  let secondCode : TwoBlockPolymerFamily → List Bool := fun family =>
    familyOccurrenceFingerprint (secondRoots.map Subtype.val) family
  let jointLaw : List Bool → List Bool → Q' := fun firstBits secondBits =>
    anchorEventProbability n (fun family =>
      decide (firstCode family = firstBits) &&
        decide (secondCode family = secondBits))
  let productLaw : List Bool → List Bool → Q' := fun firstBits secondBits =>
    anchorEventProbability n
        (fun family => decide (firstCode family = firstBits)) *
      anchorEventProbability n
        (fun family => decide (secondCode family = secondBits))
  have hfirstCoverage : ∀ family,
      family ∈ canonicalCompatibleAmbientFamilies n →
        firstCode family ∈ firstStates := by
    intro family hfamily
    apply strictJointFingerprintSpace_complete
    simp only [firstCode, familyOccurrenceFingerprint_length,
      List.length_map]
  have hsecondCoverage : ∀ family,
      family ∈ canonicalCompatibleAmbientFamilies n →
        secondCode family ∈ secondStates := by
    intro family hfamily
    apply strictJointFingerprintSpace_complete
    simp only [secondCode, familyOccurrenceFingerprint_length,
      List.length_map]
  have hjoint :
      finiteHeterogeneousCrossBilinear
          firstStates secondStates firstCoefficient secondCoefficient jointLaw ≈
        anchorTwoBlockProductExpectation firstRoots secondRoots
          firstCoefficient secondCoefficient := by
    simpa only [firstStates, secondStates, firstCode, secondCode,
      jointLaw, anchorTwoBlockProductExpectation,
      blockCylinderObservable] using
      (normalizedJointAtomMoment_eqv_productExpectation n
        firstCode secondCode firstStates secondStates
        (strictJointFingerprintSpace_nodup firstRoots.length)
        (strictJointFingerprintSpace_nodup secondRoots.length)
        hfirstCoverage hsecondCoverage firstCoefficient secondCoefficient)
  have hfirst :
      listQSum (fun firstBits => firstCoefficient firstBits *
          anchorEventProbability n
            (fun family => decide (firstCode family = firstBits)))
          firstStates ≈
        anchorBlockObservableExpectation firstRoots firstCoefficient := by
    simpa only [firstStates, firstCode, anchorBlockObservableExpectation,
      blockCylinderObservable] using
      (normalizedAtomMoment_eqv_observableExpectation n firstCode firstStates
        (strictJointFingerprintSpace_nodup firstRoots.length)
        hfirstCoverage firstCoefficient)
  have hsecond :
      listQSum (fun secondBits => secondCoefficient secondBits *
          anchorEventProbability n
            (fun family => decide (secondCode family = secondBits)))
          secondStates ≈
        anchorBlockObservableExpectation secondRoots secondCoefficient := by
    simpa only [secondStates, secondCode, anchorBlockObservableExpectation,
      blockCylinderObservable] using
      (normalizedAtomMoment_eqv_observableExpectation n secondCode secondStates
        (strictJointFingerprintSpace_nodup secondRoots.length)
        hsecondCoverage secondCoefficient)
  have hproduct :
      finiteHeterogeneousCrossBilinear
          firstStates secondStates firstCoefficient secondCoefficient productLaw ≈
        anchorBlockObservableExpectation firstRoots firstCoefficient *
          anchorBlockObservableExpectation secondRoots secondCoefficient := by
    unfold finiteHeterogeneousCrossBilinear productLaw
    refine Q'.eqv_trans _
      (listQSum (fun firstBits => listQSum (fun secondBits =>
        (firstCoefficient firstBits *
            anchorEventProbability n
              (fun family => decide (firstCode family = firstBits))) *
          (secondCoefficient secondBits *
            anchorEventProbability n
              (fun family => decide (secondCode family = secondBits))))
        secondStates) firstStates) _ ?_ ?_
    · apply listQSum_congr
      intro firstBits
      apply listQSum_congr
      intro secondBits
      ring_qeqv
    refine Q'.eqv_trans _
      (listQSum (fun firstBits => firstCoefficient firstBits *
          anchorEventProbability n
            (fun family => decide (firstCode family = firstBits))) firstStates *
        listQSum (fun secondBits => secondCoefficient secondBits *
          anchorEventProbability n
            (fun family => decide (secondCode family = secondBits))) secondStates)
      _ (listQSum_product _ _ firstStates secondStates) ?_
    exact mul_eqv_both_local hfirst hsecond
  have hsplit :
      anchorTwoBlockObservableAtomCovarianceAssembly
          firstRoots secondRoots firstCoefficient secondCoefficient ≈
        finiteHeterogeneousCrossBilinear
            firstStates secondStates firstCoefficient secondCoefficient jointLaw -
          finiteHeterogeneousCrossBilinear
            firstStates secondStates firstCoefficient secondCoefficient
            productLaw := by
    unfold anchorTwoBlockObservableAtomCovarianceAssembly
      anchorTwoBlockBooleanCovariance exactFingerprintPredicate
      blockCylinderEvent
    simpa only [firstStates, secondStates, firstCode, secondCode,
      jointLaw, productLaw] using
      (finiteHeterogeneousCrossBilinear_sub_local
        firstStates secondStates firstCoefficient secondCoefficient
        jointLaw productLaw)
  refine Q'.eqv_trans _ _ _ hsplit ?_
  unfold anchorTwoBlockObservableCovariance
  exact sub_eqv_both_local hjoint hproduct

/-! ## 4. Strict doubled-time specialization -/

theorem strictDoubledTimeNormalizedSignedCovariance_eqv_observableCovariance
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    strictDoubledTimeNormalizedSignedCovariance
        hadmissible hroots leftCoefficient rightCoefficient ≈
      anchorTwoBlockObservableCovariance
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        leftCoefficient rightCoefficient := by
  refine Q'.eqv_trans _ _ _
    (strictDoubledTimeNormalizedSignedCovariance_eqv_booleanAssembly
      hadmissible hroots leftCoefficient rightCoefficient) ?_
  unfold strictDoubledTimeBooleanCovarianceAssembly
  have hlengthLower := strictJointDoubledTimeLowerRootAtoms_length
    hadmissible hroots
  have hlengthUpper := strictJointDoubledTimeUpperRootAtoms_length
    hadmissible hroots
  simpa only [anchorTwoBlockObservableAtomCovarianceAssembly,
      hlengthLower, hlengthUpper] using
    (anchorTwoBlockObservableAtomCovarianceAssembly_eqv_covariance
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      leftCoefficient rightCoefficient)

/-- Direct conventional centered-moment decay for arbitrary rational
strict-cylinder observables.  The prefactor depends on the two finite
presentations, while the temporal rate is common and independent of the
ambient volume. -/
theorem strictDoubledTimeObservableCovariance_abs_le_l1
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    Q'.abs
        (anchorTwoBlockObservableCovariance
          (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
          (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
          leftCoefficient rightCoefficient) ≤
      (coefficientL1
          (strictJointFingerprintSpace roots.length) leftCoefficient *
        coefficientL1
          (strictJointFingerprintSpace roots.length) rightCoefficient) *
        strictDoubledTimeNormalizedCovarianceEpsilon
          roots.length shift := by
  have hidentity :=
    strictDoubledTimeNormalizedSignedCovariance_eqv_observableCovariance
      hadmissible hroots leftCoefficient rightCoefficient
  have habs := Q'.abs_eqv_congr hidentity
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm habs))
    (strictDoubledTimeNormalizedSignedCovariance_abs_le_l1
      hadmissible hroots leftCoefficient rightCoefficient)

#print axioms anchorTwoBlockObservableAtomCovarianceAssembly_eqv_covariance
#print axioms strictDoubledTimeNormalizedSignedCovariance_eqv_observableCovariance
#print axioms strictDoubledTimeObservableCovariance_abs_le_l1

end YMGap.Continuum.Z4CanonicalTwoBlockObservableCovariance
