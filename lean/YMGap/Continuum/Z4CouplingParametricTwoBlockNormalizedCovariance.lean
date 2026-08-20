/-
# Uniform normalized arbitrary-cutoff two-block covariance

Divide the all-cutoff four-cell carrier tail by the square of the same
strictly positive spin-summed support-gas partition.  The partition factors
cancel exactly, leaving a volume- and cutoff-uniform temporal bound.  Applying
the same estimate to the complement of the second Boolean event gives the
opposite sign and hence an absolute covariance estimate.
-/

import YMGap.Continuum.Z4CouplingParametricTwoBlockCarrierTail
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.Z4CouplingParametricTwoBlockNormalizedCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockNormalizedCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CouplingParametricTwoBlockCarrierTail
open YMGap.Continuum.Z4CouplingParametricTwoBlockProbabilityCovariance
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

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

theorem couplingParametricKTwoBlockFourCellCrossNumerator_complement_second
    (coupling : Q') (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKTwoBlockFourCellCrossNumerator coupling cutoff
        firstRoots secondRoots firstPredicate
        (boolPredicateComplement secondPredicate) ≈
      -(couplingParametricKTwoBlockFourCellCrossNumerator coupling cutoff
        firstRoots secondRoots firstPredicate secondPredicate) := by
  unfold couplingParametricKTwoBlockFourCellCrossNumerator
    couplingParametricKTwoBlockTTWeight
    couplingParametricKTwoBlockFFWeight
    couplingParametricKTwoBlockFTWeight
    couplingParametricKTwoBlockTFWeight
  rw [twoBlockTT_complement_second,
    twoBlockFF_complement_second,
    twoBlockFT_complement_second,
    twoBlockTF_complement_second]
  exact cross_swap_eqv_neg _ _ _ _

theorem couplingParametricKNormalizedTwoBlockFourCellCovariance_complement_second
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKNormalizedTwoBlockFourCellCovariance hcoupling cutoff
        firstRoots secondRoots firstPredicate
        (boolPredicateComplement secondPredicate) ≈
      -(couplingParametricKNormalizedTwoBlockFourCellCovariance
        hcoupling cutoff firstRoots secondRoots
        firstPredicate secondPredicate) := by
  unfold couplingParametricKNormalizedTwoBlockFourCellCovariance Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (couplingParametricKTwoBlockFourCellCrossNumerator_complement_second
        coupling cutoff firstRoots secondRoots
        firstPredicate secondPredicate)) ?_
  exact Q'.neg_mul_eqv _ _

def couplingParametricKNormalizedTwoBlockCovarianceMagnitude
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  Q'.abs (couplingParametricKNormalizedTwoBlockFourCellCovariance
    hcoupling cutoff firstRoots secondRoots
    firstPredicate secondPredicate)

theorem couplingParametricKStrictDoubledTimeNormalizedFourCellCovariance_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKNormalizedTwoBlockFourCellCovariance
        hcoupling cutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate ≤
      Q'.ofNat
          (strictJointDoubledTimeLowerRootAtoms
            hadmissible hroots).length *
        (anchorDecoratedEffectiveRatio ^ (shift + shift + 6) *
          Q'.ofNat 2) := by
  let n := centralAmbient radius
  let rootCount := Q'.ofNat
    (strictJointDoubledTimeLowerRootAtoms hadmissible hroots).length
  let tail := anchorDecoratedEffectiveRatio ^ (shift + shift + 6) *
    Q'.ofNat 2
  let partitionSq :=
    couplingParametricKCompatibleSupportGasPartition coupling cutoff n *
      couplingParametricKCompatibleSupportGasPartition coupling cutoff n
  have hraw :=
    couplingSpinSummedStrictDoubledTimeFourCellCrossDifference_le_tail
      hcoupling hle cutoff hadmissible hroots
      firstPredicate secondPredicate
  have hreorder :
      (rootCount * partitionSq) * tail ≈
        (rootCount * tail) * partitionSq := by
    unfold rootCount tail partitionSq n
    ring_qeqv
  unfold couplingParametricKNormalizedTwoBlockFourCellCovariance
  apply Q'.divPos_le_of_le_mul _ _
    (Q'.mul_pos
      (couplingParametricKCompatibleSupportGasPartition_pos
        hcoupling cutoff n)
      (couplingParametricKCompatibleSupportGasPartition_pos
        hcoupling cutoff n))
  exact Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hreorder)

theorem couplingParametricKStrictDoubledTimeNormalizedFourCellCovariance_neg_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    -(couplingParametricKNormalizedTwoBlockFourCellCovariance
        hcoupling cutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate) ≤
      Q'.ofNat
          (strictJointDoubledTimeLowerRootAtoms
            hadmissible hroots).length *
        (anchorDecoratedEffectiveRatio ^ (shift + shift + 6) *
          Q'.ofNat 2) := by
  let lowerRoots :=
    strictJointDoubledTimeLowerRootAtoms hadmissible hroots
  let upperRoots :=
    strictJointDoubledTimeUpperRootAtoms hadmissible hroots
  have hcomplement :=
    couplingParametricKStrictDoubledTimeNormalizedFourCellCovariance_le
      hcoupling hle cutoff hadmissible hroots firstPredicate
        (boolPredicateComplement secondPredicate)
  have heq :=
    couplingParametricKNormalizedTwoBlockFourCellCovariance_complement_second
      hcoupling cutoff lowerRoots upperRoots
      firstPredicate secondPredicate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm heq)) hcomplement

theorem couplingParametricKStrictDoubledTimeNormalizedCovarianceMagnitude_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKNormalizedTwoBlockCovarianceMagnitude
        hcoupling cutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate ≤
      Q'.ofNat
          (strictJointDoubledTimeLowerRootAtoms
            hadmissible hroots).length *
        (anchorDecoratedEffectiveRatio ^ (shift + shift + 6) *
          Q'.ofNat 2) := by
  unfold couplingParametricKNormalizedTwoBlockCovarianceMagnitude
  by_cases hnonnegative : (0 : Q') ≤
      couplingParametricKNormalizedTwoBlockFourCellCovariance
        hcoupling cutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate
  · rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hnonnegative]
    exact couplingParametricKStrictDoubledTimeNormalizedFourCellCovariance_le
      hcoupling hle cutoff hadmissible hroots
      firstPredicate secondPredicate
  · unfold Q'.abs
    rw [if_neg hnonnegative]
    exact
      couplingParametricKStrictDoubledTimeNormalizedFourCellCovariance_neg_le
        hcoupling hle cutoff hadmissible hroots
        firstPredicate secondPredicate

/-- Root-count form of the uniform absolute Boolean covariance estimate. -/
theorem couplingParametricKStrictDoubledTimeNormalizedCovarianceMagnitude_le_rootCount
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKNormalizedTwoBlockCovarianceMagnitude
        hcoupling cutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate ≤
      Q'.ofNat roots.length *
        (anchorDecoratedEffectiveRatio ^ (shift + shift + 6) *
          Q'.ofNat 2) := by
  simpa only [strictJointDoubledTimeLowerRootAtoms_length] using
    (couplingParametricKStrictDoubledTimeNormalizedCovarianceMagnitude_le
      hcoupling hle cutoff hadmissible hroots
      firstPredicate secondPredicate)

/-- The ordinary physical Boolean covariance from the spin-summed event law
has the same absolute temporal bound. -/
theorem couplingParametricKStrictDoubledTimeBooleanCovariance_abs_le_rootCount
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    Q'.abs (couplingParametricKTwoBlockBooleanCovariance hcoupling cutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate) ≤
      Q'.ofNat roots.length *
        (anchorDecoratedEffectiveRatio ^ (shift + shift + 6) *
          Q'.ofNat 2) := by
  have heq :=
    couplingParametricKTwoBlockBooleanCovariance_eqv_normalizedFourCell
      hcoupling cutoff
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      firstPredicate secondPredicate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr heq))
    (couplingParametricKStrictDoubledTimeNormalizedCovarianceMagnitude_le_rootCount
      hcoupling hle cutoff hadmissible hroots
      firstPredicate secondPredicate)

#print axioms couplingParametricKNormalizedTwoBlockFourCellCovariance_complement_second
#print axioms couplingParametricKStrictDoubledTimeNormalizedFourCellCovariance_le
#print axioms couplingParametricKStrictDoubledTimeNormalizedCovarianceMagnitude_le_rootCount
#print axioms couplingParametricKStrictDoubledTimeBooleanCovariance_abs_le_rootCount

end YMGap.Continuum.Z4CouplingParametricTwoBlockNormalizedCovariance
