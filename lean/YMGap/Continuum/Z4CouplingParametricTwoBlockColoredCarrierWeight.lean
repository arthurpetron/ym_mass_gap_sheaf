/-
# Arbitrary-cutoff weight of the two-block colored carrier

For a connected two-replica source pair, filter each replica into its
loop-erased disagreement-path family and its compatible background family.
The exact spin-summed support-family activity factors across this partition.
Below the anchor coupling, the path product is bounded by one decorated-face
envelope factor for every face in the colored carrier support; the two
background activities remain exact.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockColoredCarrierGeometry
import YMGap.Continuum.Z4CouplingParametricTwoBlockSwitchSummation

namespace YMGap.Continuum.Z4CouplingParametricTwoBlockColoredCarrierWeight

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalTwoBlockColoredCarrierGeometry
open YMGap.Continuum.Z4CanonicalTwoBlockColoredPathCarrier
open YMGap.Continuum.Z4CouplingParametricCylinderWeights
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CouplingParametricTwoBlockSwitchSummation
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

def couplingSpinSummedTwoBlockConnectedPathPairWeight
    (coupling : Q') (cutoff : Nat)
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff n
      (twoBlockConnectedPathLeftFamily entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff n
      (twoBlockConnectedPathRightFamily entry)

def couplingSpinSummedTwoBlockConnectedBackgroundPairWeight
    (coupling : Q') (cutoff : Nat)
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff n
      (twoBlockConnectedBackgroundLeftFamily entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff n
      (twoBlockConnectedBackgroundRightFamily entry)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem couplingSpinSummedTwoBlockConnectedSourcePairWeight_factor
    (coupling : Q') (cutoff : Nat)
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    couplingSpinSummedTwoBlockSourcePairWeight
        coupling cutoff entry.val ≈
      couplingSpinSummedTwoBlockConnectedPathPairWeight
          coupling cutoff entry *
        couplingSpinSummedTwoBlockConnectedBackgroundPairWeight
          coupling cutoff entry := by
  have hleft := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff n entry.val.1.val (twoBlockConnectedPathTest entry)
  have hright := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff n entry.val.2.val (twoBlockConnectedPathTest entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both hleft hright) ?_
  unfold couplingSpinSummedTwoBlockConnectedPathPairWeight
    couplingSpinSummedTwoBlockConnectedBackgroundPairWeight
    twoBlockConnectedPathLeftFamily
    twoBlockConnectedBackgroundLeftFamily
    twoBlockConnectedPathRightFamily
    twoBlockConnectedBackgroundRightFamily
  ring_qeqv

theorem couplingSpinSummedTwoBlockConnectedPathPairWeight_le_supportPow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    couplingSpinSummedTwoBlockConnectedPathPairWeight
        coupling cutoff entry ≤
      anchorDecoratedFaceEnvelope ^
        (twoBlockConnectedColoredSupport entry).length := by
  have hleft := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff n (twoBlockConnectedPathLeftFamily entry)
  have hright := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff n (twoBlockConnectedPathRightFamily entry)
  have hright0 := couplingParametricKSupportFamilyActivity_nonnegative
    hcoupling cutoff n (twoBlockConnectedPathRightFamily entry)
  have hleftPow0 : (0 : Q') ≤ anchorDecoratedFaceEnvelope ^
      familyFaceCount (twoBlockConnectedPathLeftFamily entry) :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  have htotal :
      couplingSpinSummedTwoBlockConnectedPathPairWeight
          coupling cutoff entry ≤
        anchorDecoratedFaceEnvelope ^
          (familyFaceCount (twoBlockConnectedPathLeftFamily entry) +
            familyFaceCount (twoBlockConnectedPathRightFamily entry)) := by
    unfold couplingSpinSummedTwoBlockConnectedPathPairWeight
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ hsecond
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.pow_add_eqv anchorDecoratedFaceEnvelope _ _))))
  exact Q'.le_trans' _ _ _ htotal
    (pow_base_antitone (r := anchorDecoratedFaceEnvelope)
      anchorDecoratedFaceEnvelope_nonnegative (by decide)
      (twoBlockConnectedColoredSupport_length_le_pathFaceCount entry))

theorem couplingSpinSummedTwoBlockConnectedBackgroundPairWeight_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat)
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    (0 : Q') ≤
      couplingSpinSummedTwoBlockConnectedBackgroundPairWeight
        coupling cutoff entry := by
  unfold couplingSpinSummedTwoBlockConnectedBackgroundPairWeight
  exact Q'.mul_nonneg _ _
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n _)
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n _)

theorem couplingSpinSummedTwoBlockConnectedSourcePairWeight_le_support_background
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff entry.val ≤
      anchorDecoratedFaceEnvelope ^
          (twoBlockConnectedColoredSupport entry).length *
        couplingSpinSummedTwoBlockConnectedBackgroundPairWeight
          coupling cutoff entry := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingSpinSummedTwoBlockConnectedSourcePairWeight_factor
        coupling cutoff entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (couplingSpinSummedTwoBlockConnectedPathPairWeight_le_supportPow
        hcoupling hle cutoff entry)
      (couplingSpinSummedTwoBlockConnectedBackgroundPairWeight_nonnegative
        hcoupling cutoff entry))

#print axioms couplingSpinSummedTwoBlockConnectedSourcePairWeight_factor
#print axioms couplingSpinSummedTwoBlockConnectedPathPairWeight_le_supportPow
#print axioms couplingSpinSummedTwoBlockConnectedSourcePairWeight_le_support_background

end YMGap.Continuum.Z4CouplingParametricTwoBlockColoredCarrierWeight
