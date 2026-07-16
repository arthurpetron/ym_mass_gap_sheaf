/-
# Finite cylinder switching with arbitrary-cutoff spin-summed activities

The canonical marked-root switch and all four-cell family lists are independent
of the activity.  This module repeats only the finite weighted-summation layer,
using the exact spin-summed connected-support activity at an arbitrary physical
representation cutoff.
-/

import YMGap.Continuum.Z4SpinSummedMarkedRootSwitch
import YMGap.Continuum.Z4CanonicalCylinderSwitchSummation

namespace YMGap.Continuum.Z4SpinSummedCylinderSwitchSummation

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedMarkedRootSwitch
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper

local infix:50 " ≈ " => Q'.eqv

def spinSummedCylinderSourcePairWeight
    (cutoff : Nat) {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool}
    (pair : CylinderSourcePair small n roots predicate) : Q' :=
  parametricKSupportFamilyActivity cutoff n pair.1.val *
    parametricKSupportFamilyActivity cutoff n pair.2.val

def spinSummedCylinderRawPairWeight
    (cutoff n : Nat) (pair : RawFamilyPair) : Q' :=
  parametricKSupportFamilyActivity cutoff n pair.1 *
    parametricKSupportFamilyActivity cutoff n pair.2

theorem spinSummedSeparatedCylinderSwitchEncode_weight
    (cutoff : Nat) {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n)
    (pair : CylinderSourcePair small n roots predicate) :
    spinSummedCylinderRawPairWeight cutoff n
        (separatedCylinderSwitchEncode hsmall pair) ≈
      spinSummedCylinderSourcePairWeight cutoff pair := by
  exact recoverableMarkedSwitchedFamilies_spinSummed_weight_preserved
    cutoff (cylinderSourceLeftCompatible pair)
    (cylinderSourceRightCompatible hsmall pair) roots

theorem spinSummedSeparatedCylinderPairSum_le_targetPairSum
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum (spinSummedCylinderSourcePairWeight cutoff)
        (separatedCylinderSourcePairs
          (roots := roots) (predicate := predicate) hsmall) ≤
      listQSum (spinSummedCylinderRawPairWeight cutoff n)
        (cylinderTargetPairList small n roots predicate) := by
  apply listQSum_le_of_injective
    (separatedCylinderSourcePairs
      (roots := roots) (predicate := predicate) hsmall)
    (cylinderTargetPairList small n roots predicate)
    (spinSummedCylinderSourcePairWeight cutoff)
    (spinSummedCylinderRawPairWeight cutoff n)
    (separatedCylinderSwitchEncode hsmall)
    (separatedCylinderSourcePairs_nodup hsmall roots predicate)
  · exact separatedCylinderSwitchEncode_mem_target hsmall
  · intro first hfirst second hsecond heq
    exact separatedCylinderSwitchEncode_injective hsmall first second
      hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (spinSummedSeparatedCylinderSwitchEncode_weight
          cutoff hsmall pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (parametricKSupportFamilyActivity_nonnegative cutoff n pair.1)
      (parametricKSupportFamilyActivity_nonnegative cutoff n pair.2)

theorem spinSummedCylinderSourcePairList_sum_eqv_cellProduct
    (cutoff : Nat) {small n : Nat} (_hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum (spinSummedCylinderSourcePairWeight cutoff)
        (cylinderSourcePairList small n roots predicate) ≈
      listQSum (parametricKSupportFamilyActivity cutoff n)
          (boundaryCylinderEventFamilyList small n roots predicate) *
        listQSum (parametricKSupportFamilyActivity cutoff n)
          (embeddedCylinderComplementFamilyList small n roots predicate) := by
  have hproduct := listQSum_cartesian_product
    (fun entry : BoundaryCylinderEventEntry small n roots predicate =>
      parametricKSupportFamilyActivity cutoff n entry.val)
    (fun entry : EmbeddedCylinderComplementEntry small n roots predicate =>
      parametricKSupportFamilyActivity cutoff n entry.val)
    (boundaryCylinderEventEntries small n roots predicate)
    (embeddedCylinderComplementEntries small n roots predicate)
  unfold cylinderSourcePairList at hproduct ⊢
  refine Q'.eqv_trans _ _ _ hproduct ?_
  unfold boundaryCylinderEventEntries embeddedCylinderComplementEntries
  rw [listQSum_attach, listQSum_attach]
  exact Q'.eqv_refl _

theorem spinSummedCylinderTargetPairList_sum_eqv_cellProduct
    (cutoff small n : Nat) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) :
    listQSum (spinSummedCylinderRawPairWeight cutoff n)
        (cylinderTargetPairList small n roots predicate) ≈
      listQSum (parametricKSupportFamilyActivity cutoff n)
          (boundaryCylinderComplementFamilyList small n roots predicate) *
        listQSum (parametricKSupportFamilyActivity cutoff n)
          (embeddedCylinderEventFamilyList small n roots predicate) := by
  exact listQSum_cartesian_product
    (parametricKSupportFamilyActivity cutoff n)
    (parametricKSupportFamilyActivity cutoff n)
    (boundaryCylinderComplementFamilyList small n roots predicate)
    (embeddedCylinderEventFamilyList small n roots predicate)

theorem spinSummedCylinderSourcePairList_partition
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum (spinSummedCylinderSourcePairWeight cutoff)
        (cylinderSourcePairList small n roots predicate) ≈
      listQSum (spinSummedCylinderSourcePairWeight cutoff)
          (separatedCylinderSourcePairs
            (roots := roots) (predicate := predicate) hsmall) +
        listQSum (spinSummedCylinderSourcePairWeight cutoff)
          (connectedCylinderSourcePairs
            (roots := roots) (predicate := predicate) hsmall) := by
  exact listQSum_filter_partition
    (spinSummedCylinderSourcePairWeight cutoff)
    (cylinderSourceSeparatedB hsmall)
    (cylinderSourcePairList small n roots predicate)

theorem spinSummedBoundaryCylinderEvent_embeddedComplement_le_opposite_add_connected
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum (parametricKSupportFamilyActivity cutoff n)
          (boundaryCylinderEventFamilyList small n roots predicate) *
        listQSum (parametricKSupportFamilyActivity cutoff n)
          (embeddedCylinderComplementFamilyList small n roots predicate) ≤
      listQSum (parametricKSupportFamilyActivity cutoff n)
            (boundaryCylinderComplementFamilyList small n roots predicate) *
          listQSum (parametricKSupportFamilyActivity cutoff n)
            (embeddedCylinderEventFamilyList small n roots predicate) +
        listQSum (spinSummedCylinderSourcePairWeight cutoff)
          (connectedCylinderSourcePairs
            (roots := roots) (predicate := predicate) hsmall) := by
  have hsource := spinSummedCylinderSourcePairList_sum_eqv_cellProduct
    cutoff hsmall roots predicate
  have htarget := spinSummedCylinderTargetPairList_sum_eqv_cellProduct
    cutoff small n roots predicate
  have hpartition := spinSummedCylinderSourcePairList_partition
    cutoff hsmall roots predicate
  have hinjection := spinSummedSeparatedCylinderPairSum_le_targetPairSum
    cutoff hsmall roots predicate
  have hsepAdd :
      listQSum (spinSummedCylinderSourcePairWeight cutoff)
            (separatedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) +
          listQSum (spinSummedCylinderSourcePairWeight cutoff)
            (connectedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) ≤
        listQSum (spinSummedCylinderRawPairWeight cutoff n)
              (cylinderTargetPairList small n roots predicate) +
          listQSum (spinSummedCylinderSourcePairWeight cutoff)
            (connectedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) :=
    Q'.add_le_add hinjection (Q'.le_refl' _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hsepAdd
        (Q'.add_le_add (Q'.le_of_eqv htarget) (Q'.le_refl' _))))

end YMGap.Continuum.Z4SpinSummedCylinderSwitchSummation

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedCylinderSwitchSummation.spinSummedSeparatedCylinderSwitchEncode_weight
#print axioms YMGap.Continuum.Z4SpinSummedCylinderSwitchSummation.spinSummedSeparatedCylinderPairSum_le_targetPairSum
#print axioms YMGap.Continuum.Z4SpinSummedCylinderSwitchSummation.spinSummedBoundaryCylinderEvent_embeddedComplement_le_opposite_add_connected
