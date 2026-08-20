/-
# Normalized two-block covariance determinant

Divide the exact four-cell cross numerator by the square of the genuine
canonical partition function.  The `Z_n^2` background factor cancels, leaving
a volume-uniform temporal decay estimate whose only observable prefactor is
the finite number of lower roots.

This is still an indicator/cylinder estimate.  It is not yet relative to the
reflection seminorm and therefore is not yet an operator contraction.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockCarrierTail
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.Z4CanonicalTwoBlockNormalizedCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockCarrierTail
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

local macro "ring_qeqv_neg" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one]; ac_rfl))

private theorem cross_swap_eqv_neg (a b c d : Q') :
    c * d - b * a ≈ -(a * b - d * c) := by
  change c * d + -(b * a) ≈ -(a * b + -(d * c))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_comm_eqv c d)
      (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv b a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv (d * c) (-(a * b))) ?_
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv (a * b) (-(d * c)))
      (Q'.add_eqv_congr_left (-(a * b)) _ _
        (Q'.neg_neg_eqv (d * c))))

def boolPredicateComplement (predicate : List Bool → Bool) :
    List Bool → Bool :=
  fun bits => !(predicate bits)

def twoBlockFourCellCrossNumerator
    (n : Nat) (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (twoBlockTTFamilyList firstRoots secondRoots
          firstPredicate secondPredicate) *
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (twoBlockFFFamilyList firstRoots secondRoots
          firstPredicate secondPredicate) -
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (twoBlockFTFamilyList firstRoots secondRoots
          firstPredicate secondPredicate) *
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (twoBlockTFFamilyList firstRoots secondRoots
          firstPredicate secondPredicate)

theorem anchorCanonicalPartition_sq_pos (n : Nat) :
    (0 : Q') < anchorCanonicalPartition n * anchorCanonicalPartition n :=
  Q'.mul_pos (anchorCanonicalPartition_pos n)
    (anchorCanonicalPartition_pos n)

def normalizedTwoBlockFourCellCovariance
    (n : Nat) (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  Q'.divPos
    (twoBlockFourCellCrossNumerator n firstRoots secondRoots
      firstPredicate secondPredicate)
    (anchorCanonicalPartition n * anchorCanonicalPartition n)
    (anchorCanonicalPartition_sq_pos n)

theorem twoBlockTT_complement_second
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    twoBlockTTFamilyList firstRoots secondRoots
        firstPredicate (boolPredicateComplement secondPredicate) =
      twoBlockTFFamilyList firstRoots secondRoots
        firstPredicate secondPredicate := by
  unfold twoBlockTTFamilyList twoBlockTFFamilyList
    boolPredicateComplement blockCylinderEvent
  apply List.filter_congr
  intro family _
  rfl

theorem twoBlockFF_complement_second
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    twoBlockFFFamilyList firstRoots secondRoots
        firstPredicate (boolPredicateComplement secondPredicate) =
      twoBlockFTFamilyList firstRoots secondRoots
        firstPredicate secondPredicate := by
  unfold twoBlockFFFamilyList twoBlockFTFamilyList
    boolPredicateComplement blockCylinderEvent
  apply List.filter_congr
  intro family _
  cases hfirst : firstPredicate
      (familyOccurrenceFingerprint
        (List.map Subtype.val firstRoots) family) <;>
    cases hsecond : secondPredicate
      (familyOccurrenceFingerprint
        (List.map Subtype.val secondRoots) family) <;>
    simp_all

theorem twoBlockFT_complement_second
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    twoBlockFTFamilyList firstRoots secondRoots
        firstPredicate (boolPredicateComplement secondPredicate) =
      twoBlockFFFamilyList firstRoots secondRoots
        firstPredicate secondPredicate := by
  unfold twoBlockFTFamilyList twoBlockFFFamilyList
    boolPredicateComplement blockCylinderEvent
  apply List.filter_congr
  intro family _
  rfl

theorem twoBlockTF_complement_second
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    twoBlockTFFamilyList firstRoots secondRoots
        firstPredicate (boolPredicateComplement secondPredicate) =
      twoBlockTTFamilyList firstRoots secondRoots
        firstPredicate secondPredicate := by
  unfold twoBlockTFFamilyList twoBlockTTFamilyList
    boolPredicateComplement blockCylinderEvent
  apply List.filter_congr
  intro family _
  cases hsecond : secondPredicate
      (familyOccurrenceFingerprint
        (List.map Subtype.val secondRoots) family) <;>
    simp_all

theorem twoBlockFourCellCrossNumerator_complement_second
    (n : Nat) (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    twoBlockFourCellCrossNumerator n firstRoots secondRoots
        firstPredicate (boolPredicateComplement secondPredicate) ≈
      -(twoBlockFourCellCrossNumerator n firstRoots secondRoots
        firstPredicate secondPredicate) := by
  unfold twoBlockFourCellCrossNumerator
  rw [twoBlockTT_complement_second,
    twoBlockFF_complement_second,
    twoBlockFT_complement_second,
    twoBlockTF_complement_second]
  exact cross_swap_eqv_neg _ _ _ _

theorem normalizedTwoBlockFourCellCovariance_complement_second
    (n : Nat) (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    normalizedTwoBlockFourCellCovariance n firstRoots secondRoots
        firstPredicate (boolPredicateComplement secondPredicate) ≈
      -(normalizedTwoBlockFourCellCovariance n firstRoots secondRoots
        firstPredicate secondPredicate) := by
  unfold normalizedTwoBlockFourCellCovariance Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (twoBlockFourCellCrossNumerator_complement_second
        n firstRoots secondRoots firstPredicate secondPredicate)) ?_
  exact Q'.neg_mul_eqv _ _

def normalizedTwoBlockCovarianceMagnitude
    (n : Nat) (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  Q'.abs (normalizedTwoBlockFourCellCovariance n
    firstRoots secondRoots firstPredicate secondPredicate)

/-- After normalization the two background partition functions cancel. -/
theorem strictDoubledTimeNormalizedFourCellCovariance_le
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    normalizedTwoBlockFourCellCovariance
        (centralAmbient radius)
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate ≤
      Q'.ofNat
          (strictJointDoubledTimeLowerRootAtoms
            hadmissible hroots).length *
        (anchorEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2) := by
  let n := centralAmbient radius
  let rootCount := Q'.ofNat
    (strictJointDoubledTimeLowerRootAtoms hadmissible hroots).length
  let tail := anchorEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2
  let partitionSq := anchorCanonicalPartition n * anchorCanonicalPartition n
  have hraw := strictDoubledTimeFourCellCrossDifference_le_tail
    hadmissible hroots firstPredicate secondPredicate
  have hreorder :
      (rootCount * partitionSq) * tail ≈
        (rootCount * tail) * partitionSq := by
    unfold rootCount tail partitionSq n
    ring_qeqv
  unfold normalizedTwoBlockFourCellCovariance
    twoBlockFourCellCrossNumerator
  apply Q'.divPos_le_of_le_mul _ _
    (anchorCanonicalPartition_sq_pos n)
  exact Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hreorder)

theorem strictDoubledTimeNormalizedFourCellCovariance_neg_le
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    -(normalizedTwoBlockFourCellCovariance
        (centralAmbient radius)
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate) ≤
      Q'.ofNat
          (strictJointDoubledTimeLowerRootAtoms
            hadmissible hroots).length *
        (anchorEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2) := by
  let lowerRoots :=
    strictJointDoubledTimeLowerRootAtoms hadmissible hroots
  let upperRoots :=
    strictJointDoubledTimeUpperRootAtoms hadmissible hroots
  have hcomplement :=
    strictDoubledTimeNormalizedFourCellCovariance_le
      hadmissible hroots firstPredicate
        (boolPredicateComplement secondPredicate)
  have heq := normalizedTwoBlockFourCellCovariance_complement_second
    (centralAmbient radius) lowerRoots upperRoots
    firstPredicate secondPredicate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm heq)) hcomplement

/-- Absolute normalized indicator covariance has uniform exponential temporal
decay.  The root-count prefactor still depends on the chosen cylinder chart. -/
theorem strictDoubledTimeNormalizedCovarianceMagnitude_le
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    normalizedTwoBlockCovarianceMagnitude
        (centralAmbient radius)
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate ≤
      Q'.ofNat
          (strictJointDoubledTimeLowerRootAtoms
            hadmissible hroots).length *
        (anchorEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2) := by
  unfold normalizedTwoBlockCovarianceMagnitude
  by_cases hnonnegative : (0 : Q') ≤
      normalizedTwoBlockFourCellCovariance
        (centralAmbient radius)
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate
  · rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hnonnegative]
    exact strictDoubledTimeNormalizedFourCellCovariance_le
      hadmissible hroots firstPredicate secondPredicate
  · unfold Q'.abs
    rw [if_neg hnonnegative]
    exact strictDoubledTimeNormalizedFourCellCovariance_neg_le
      hadmissible hroots firstPredicate secondPredicate

/-- Root-count form of the same absolute indicator estimate. -/
theorem strictDoubledTimeNormalizedCovarianceMagnitude_le_rootCount
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    normalizedTwoBlockCovarianceMagnitude
        (centralAmbient radius)
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate ≤
      Q'.ofNat roots.length *
        (anchorEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2) := by
  simpa only [strictJointDoubledTimeLowerRootAtoms_length] using
    (strictDoubledTimeNormalizedCovarianceMagnitude_le
      hadmissible hroots firstPredicate secondPredicate)

#print axioms anchorCanonicalPartition_sq_pos
#print axioms normalizedTwoBlockFourCellCovariance_complement_second
#print axioms strictDoubledTimeNormalizedFourCellCovariance_le
#print axioms strictDoubledTimeNormalizedCovarianceMagnitude_le
#print axioms strictDoubledTimeNormalizedCovarianceMagnitude_le_rootCount

end YMGap.Continuum.Z4CanonicalTwoBlockNormalizedCovariance
