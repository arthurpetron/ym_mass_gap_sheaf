/-
# Arbitrary-cutoff two-block switch summation

The recoverable two-replica switch is independent of the representation
cutoff.  This file equips that switch with the exact coupling-parametric
spin-summed support-family activity.  The separated `TT x FF` pairs inject
weight-preservingly into `FT x TF`, so the four-cell cross difference is
bounded by the literal connected-pair residue at every finite cutoff.

No carrier tail or clustering estimate is asserted here.
-/

import YMGap.Continuum.Z4CouplingParametricTwoBlockProbabilityCovariance
import YMGap.Continuum.Z4CouplingParametricCylinderWeights

namespace YMGap.Continuum.Z4CouplingParametricTwoBlockSwitchSummation

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CouplingParametricCylinderWeights
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CouplingParametricTwoBlockProbabilityCovariance

local infix:50 " ≈ " => Q'.eqv

def couplingSpinSummedTwoBlockSourcePairWeight
    (coupling : Q') (cutoff : Nat)
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) : Q' :=
  couplingParametricKSupportFamilyActivity
      coupling cutoff n pair.1.val *
    couplingParametricKSupportFamilyActivity
      coupling cutoff n pair.2.val

def couplingSpinSummedTwoBlockRawPairWeight
    (coupling : Q') (cutoff n : Nat)
    (pair : TwoBlockRawFamilyPair) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff n pair.1 *
    couplingParametricKSupportFamilyActivity coupling cutoff n pair.2

theorem couplingSpinSummedSeparatedTwoBlockSwitchEncode_weight
    (coupling : Q') (cutoff : Nat)
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) :
    couplingSpinSummedTwoBlockRawPairWeight coupling cutoff n
        (separatedTwoBlockSwitchEncode pair) ≈
      couplingSpinSummedTwoBlockSourcePairWeight
        coupling cutoff pair := by
  exact
    recoverableMarkedSwitchedFamilies_couplingSpinSummed_weight_preserved
      coupling cutoff
      (twoBlockSourceLeftCompatible pair)
      (twoBlockSourceRightCompatible pair) firstRoots

theorem couplingSpinSummedSeparatedTwoBlockPairSum_le_target
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
        (separatedTwoBlockSourcePairs
          (firstRoots := firstRoots) (secondRoots := secondRoots)
          (firstPredicate := firstPredicate)
          (secondPredicate := secondPredicate)) ≤
      listQSum
        (couplingSpinSummedTwoBlockRawPairWeight coupling cutoff n)
        (twoBlockTargetPairList firstRoots secondRoots
          firstPredicate secondPredicate) := by
  apply listQSum_le_of_injective
    (separatedTwoBlockSourcePairs
      (firstRoots := firstRoots) (secondRoots := secondRoots)
      (firstPredicate := firstPredicate)
      (secondPredicate := secondPredicate))
    (twoBlockTargetPairList firstRoots secondRoots
      firstPredicate secondPredicate)
    (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
    (couplingSpinSummedTwoBlockRawPairWeight coupling cutoff n)
    separatedTwoBlockSwitchEncode
    (separatedTwoBlockSourcePairs_nodup
      firstRoots secondRoots firstPredicate secondPredicate)
  · exact separatedTwoBlockSwitchEncode_mem_target
  · intro first hfirst second hsecond heq
    exact separatedTwoBlockSwitchEncode_injective
      first second hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (couplingSpinSummedSeparatedTwoBlockSwitchEncode_weight
          coupling cutoff pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff n pair.1)
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff n pair.2)

theorem couplingSpinSummedTwoBlockSourcePairList_sum_eqv_product
    (coupling : Q') (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
        (twoBlockSourcePairList firstRoots secondRoots
          firstPredicate secondPredicate) ≈
      couplingParametricKTwoBlockTTWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate *
        couplingParametricKTwoBlockFFWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate := by
  have hproduct := listQSum_cartesian_product
    (fun entry : TwoBlockTTEntry firstRoots secondRoots
        firstPredicate secondPredicate =>
      couplingParametricKSupportFamilyActivity
        coupling cutoff n entry.val)
    (fun entry : TwoBlockFFEntry firstRoots secondRoots
        firstPredicate secondPredicate =>
      couplingParametricKSupportFamilyActivity
        coupling cutoff n entry.val)
    (twoBlockTTEntries firstRoots secondRoots
      firstPredicate secondPredicate)
    (twoBlockFFEntries firstRoots secondRoots
      firstPredicate secondPredicate)
  unfold twoBlockSourcePairList at hproduct ⊢
  refine Q'.eqv_trans _ _ _ hproduct ?_
  unfold twoBlockTTEntries twoBlockFFEntries
    couplingParametricKTwoBlockTTWeight
    couplingParametricKTwoBlockFFWeight
  rw [listQSum_attach, listQSum_attach]
  exact Q'.eqv_refl _

theorem couplingSpinSummedTwoBlockTargetPairList_sum_eqv_product
    (coupling : Q') (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedTwoBlockRawPairWeight coupling cutoff n)
        (twoBlockTargetPairList firstRoots secondRoots
          firstPredicate secondPredicate) ≈
      couplingParametricKTwoBlockFTWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate *
        couplingParametricKTwoBlockTFWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate := by
  unfold couplingSpinSummedTwoBlockRawPairWeight
    twoBlockTargetPairList
    couplingParametricKTwoBlockFTWeight
    couplingParametricKTwoBlockTFWeight
  exact listQSum_cartesian_product
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (twoBlockFTFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)
    (twoBlockTFFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

theorem couplingSpinSummedTwoBlockSourcePairList_partition
    (coupling : Q') (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
        (twoBlockSourcePairList firstRoots secondRoots
          firstPredicate secondPredicate) ≈
      listQSum
          (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
          (separatedTwoBlockSourcePairs
            (firstRoots := firstRoots) (secondRoots := secondRoots)
            (firstPredicate := firstPredicate)
            (secondPredicate := secondPredicate)) +
        listQSum
          (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
          (connectedTwoBlockSourcePairs
            (firstRoots := firstRoots) (secondRoots := secondRoots)
            (firstPredicate := firstPredicate)
            (secondPredicate := secondPredicate)) :=
  listQSum_filter_partition
    (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
    twoBlockSourceSeparatedB
    (twoBlockSourcePairList firstRoots secondRoots
      firstPredicate secondPredicate)

def couplingSpinSummedTwoBlockConnectedResidue
    (coupling : Q') (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  listQSum
    (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
    (connectedTwoBlockSourcePairs
      (firstRoots := firstRoots) (secondRoots := secondRoots)
      (firstPredicate := firstPredicate)
      (secondPredicate := secondPredicate))

/-- At every cutoff, the positive four-cell determinant is bounded by the
literal connected two-replica residue for the same spin-summed law. -/
theorem couplingSpinSummedTwoBlockFourCellCrossDifference_le_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKTwoBlockFourCellCrossNumerator coupling cutoff
        firstRoots secondRoots firstPredicate secondPredicate ≤
      couplingSpinSummedTwoBlockConnectedResidue coupling cutoff
        firstRoots secondRoots firstPredicate secondPredicate := by
  have hsource :=
    couplingSpinSummedTwoBlockSourcePairList_sum_eqv_product
      coupling cutoff firstRoots secondRoots
      firstPredicate secondPredicate
  have htarget :=
    couplingSpinSummedTwoBlockTargetPairList_sum_eqv_product
      coupling cutoff firstRoots secondRoots
      firstPredicate secondPredicate
  have hpartition :=
    couplingSpinSummedTwoBlockSourcePairList_partition
      coupling cutoff firstRoots secondRoots
      firstPredicate secondPredicate
  have hinjection :=
    couplingSpinSummedSeparatedTwoBlockPairSum_le_target
      hcoupling cutoff firstRoots secondRoots
      firstPredicate secondPredicate
  have hsourceLe :
      listQSum
          (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
          (twoBlockSourcePairList firstRoots secondRoots
            firstPredicate secondPredicate) ≤
        listQSum
            (couplingSpinSummedTwoBlockRawPairWeight coupling cutoff n)
            (twoBlockTargetPairList firstRoots secondRoots
              firstPredicate secondPredicate) +
          couplingSpinSummedTwoBlockConnectedResidue coupling cutoff
            firstRoots secondRoots firstPredicate secondPredicate :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hpartition)
      (Q'.add_le_add hinjection (Q'.le_refl' _))
  have hcells :
      couplingParametricKTwoBlockTTWeight coupling cutoff
            firstRoots secondRoots firstPredicate secondPredicate *
          couplingParametricKTwoBlockFFWeight coupling cutoff
            firstRoots secondRoots firstPredicate secondPredicate ≤
        couplingParametricKTwoBlockFTWeight coupling cutoff
              firstRoots secondRoots firstPredicate secondPredicate *
            couplingParametricKTwoBlockTFWeight coupling cutoff
              firstRoots secondRoots firstPredicate secondPredicate +
          couplingSpinSummedTwoBlockConnectedResidue coupling cutoff
            firstRoots secondRoots firstPredicate secondPredicate :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hsource))
      (Q'.le_trans' _ _ _ hsourceLe
        (Q'.le_of_eqv
          (Q'.add_eqv_congr' htarget (Q'.eqv_refl _))))
  unfold couplingParametricKTwoBlockFourCellCrossNumerator
  exact Q'.sub_le_of_le_add hcells

#print axioms couplingSpinSummedSeparatedTwoBlockSwitchEncode_weight
#print axioms couplingSpinSummedSeparatedTwoBlockPairSum_le_target
#print axioms couplingSpinSummedTwoBlockSourcePairList_sum_eqv_product
#print axioms couplingSpinSummedTwoBlockSourcePairList_partition
#print axioms couplingSpinSummedTwoBlockFourCellCrossDifference_le_connected

end YMGap.Continuum.Z4CouplingParametricTwoBlockSwitchSummation
