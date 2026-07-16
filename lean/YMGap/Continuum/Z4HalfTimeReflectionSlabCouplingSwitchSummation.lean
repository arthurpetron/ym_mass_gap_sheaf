/-
# Arbitrary-cutoff four-cell summation for the corrected reflection slab

The corrected-slab switch is geometric and does not depend on the character
cutoff.  This file replaces the cutoff-one canonical activity in its four-cell
sum by the exact coupling-parametric spin-summed support-family activity.
Marked-component switching still preserves the two-replica product exactly,
so the separated cell injects into the opposite cell at every finite cutoff.

Only the connected source residue remains.  No cutoff-one law is identified
with the arbitrary-cutoff law here: the weights in every statement below are
literally `couplingParametricKSupportFamilyActivity coupling cutoff`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
import YMGap.Continuum.Z4CouplingParametricCylinderWeights

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingSwitchSummation

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CouplingParametricCylinderWeights
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation

local infix:50 " ≈ " => Q'.eqv

def couplingSpinSummedSlabCylinderSourcePairWeight
    (coupling : Q') (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff
      (extent + 1) pair.1.val *
    couplingParametricKSupportFamilyActivity coupling cutoff
      (extent + 1) pair.2.val

def couplingSpinSummedSlabCylinderRawPairWeight
    (coupling : Q') (cutoff extent : Nat)
    (pair : RawFamilyPair) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff
      (extent + 1) pair.1 *
    couplingParametricKSupportFamilyActivity coupling cutoff
      (extent + 1) pair.2

theorem couplingSpinSummedSlabSeparatedSwitchEncode_weight
    (coupling : Q') (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) :
    couplingSpinSummedSlabCylinderRawPairWeight
        coupling cutoff extent (slabSeparatedCylinderSwitchEncode pair) ≈
      couplingSpinSummedSlabCylinderSourcePairWeight
        coupling cutoff pair := by
  exact
    recoverableMarkedSwitchedFamilies_couplingSpinSummed_weight_preserved
      coupling cutoff
      (slabCylinderSourceLeftCompatible pair)
      (slabCylinderSourceRightCompatible pair) roots

theorem couplingSpinSummedSeparatedSlabCylinderPairSum_le_target
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedSlabCylinderSourcePairWeight coupling cutoff)
        (separatedSlabCylinderSourcePairs
          (extent := extent) (roots := roots)
          (predicate := predicate)) ≤
      listQSum
        (couplingSpinSummedSlabCylinderRawPairWeight
          coupling cutoff extent)
        (slabCylinderTargetPairList extent roots predicate) := by
  apply listQSum_le_of_injective
    (separatedSlabCylinderSourcePairs
      (extent := extent) (roots := roots)
      (predicate := predicate))
    (slabCylinderTargetPairList extent roots predicate)
    (couplingSpinSummedSlabCylinderSourcePairWeight coupling cutoff)
    (couplingSpinSummedSlabCylinderRawPairWeight
      coupling cutoff extent)
    slabSeparatedCylinderSwitchEncode
    (separatedSlabCylinderSourcePairs_nodup extent roots predicate)
  · exact slabSeparatedCylinderSwitchEncode_mem_target
  · intro first hfirst second hsecond heq
    exact slabSeparatedCylinderSwitchEncode_injective
      first second hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (couplingSpinSummedSlabSeparatedSwitchEncode_weight
          coupling cutoff pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (extent + 1) pair.1)
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (extent + 1) pair.2)

theorem couplingSpinSummedSlabCylinderSourcePairList_sum_eqv_product
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedSlabCylinderSourcePairWeight coupling cutoff)
        (slabCylinderSourcePairList extent roots predicate) ≈
      listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (extent + 1))
          (slabBoundaryCylinderEventFamilyList extent roots predicate) *
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (extent + 1))
          (slabSupportedCylinderComplementFamilyList
            extent roots predicate) := by
  have hproduct := listQSum_cartesian_product
    (fun entry : SlabBoundaryCylinderEventEntry extent roots predicate =>
      couplingParametricKSupportFamilyActivity
        coupling cutoff (extent + 1) entry.val)
    (fun entry : SlabSupportedCylinderComplementEntry
        extent roots predicate =>
      couplingParametricKSupportFamilyActivity
        coupling cutoff (extent + 1) entry.val)
    (slabBoundaryCylinderEventEntries extent roots predicate)
    (slabSupportedCylinderComplementEntries extent roots predicate)
  unfold slabCylinderSourcePairList at hproduct ⊢
  refine Q'.eqv_trans _ _ _ hproduct ?_
  unfold slabBoundaryCylinderEventEntries
    slabSupportedCylinderComplementEntries
  rw [listQSum_attach, listQSum_attach]
  exact Q'.eqv_refl _

theorem couplingSpinSummedSlabCylinderTargetPairList_sum_eqv_product
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedSlabCylinderRawPairWeight
          coupling cutoff extent)
        (slabCylinderTargetPairList extent roots predicate) ≈
      listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (extent + 1))
          (slabBoundaryCylinderComplementFamilyList
            extent roots predicate) *
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (extent + 1))
          (slabSupportedCylinderEventFamilyList
            extent roots predicate) := by
  exact listQSum_cartesian_product
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (slabBoundaryCylinderComplementFamilyList
      extent roots predicate)
    (slabSupportedCylinderEventFamilyList
      extent roots predicate)

theorem couplingSpinSummedSlabCylinderSourcePairList_partition
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedSlabCylinderSourcePairWeight coupling cutoff)
        (slabCylinderSourcePairList extent roots predicate) ≈
      listQSum
          (couplingSpinSummedSlabCylinderSourcePairWeight coupling cutoff)
          (separatedSlabCylinderSourcePairs
            (extent := extent) (roots := roots)
            (predicate := predicate)) +
        listQSum
          (couplingSpinSummedSlabCylinderSourcePairWeight coupling cutoff)
          (connectedSlabCylinderSourcePairs
            (extent := extent) (roots := roots)
            (predicate := predicate)) := by
  exact listQSum_filter_partition
    (couplingSpinSummedSlabCylinderSourcePairWeight coupling cutoff)
    slabCylinderSourceSeparatedB
    (slabCylinderSourcePairList extent roots predicate)

def couplingSpinSummedSlabConnectedCylinderResidue
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  listQSum
    (couplingSpinSummedSlabCylinderSourcePairWeight coupling cutoff)
    (connectedSlabCylinderSourcePairs
      (extent := extent) (roots := roots) (predicate := predicate))

/-- The arbitrary-cutoff four-cell cancellation.  The only residual is the
literal connected-pair sum with the exact spin-summed family activity. -/
theorem couplingSpinSummedSlabBoundaryEvent_supportedComplement_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (extent + 1))
          (slabBoundaryCylinderEventFamilyList extent roots predicate) *
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (extent + 1))
          (slabSupportedCylinderComplementFamilyList
            extent roots predicate) ≤
      listQSum
            (couplingParametricKSupportFamilyActivity
              coupling cutoff (extent + 1))
            (slabBoundaryCylinderComplementFamilyList
              extent roots predicate) *
          listQSum
            (couplingParametricKSupportFamilyActivity
              coupling cutoff (extent + 1))
            (slabSupportedCylinderEventFamilyList
              extent roots predicate) +
        couplingSpinSummedSlabConnectedCylinderResidue
          coupling cutoff extent roots predicate := by
  have hsource :=
    couplingSpinSummedSlabCylinderSourcePairList_sum_eqv_product
      coupling cutoff extent roots predicate
  have htarget :=
    couplingSpinSummedSlabCylinderTargetPairList_sum_eqv_product
      coupling cutoff extent roots predicate
  have hpartition :=
    couplingSpinSummedSlabCylinderSourcePairList_partition
      coupling cutoff extent roots predicate
  have hinjection :=
    couplingSpinSummedSeparatedSlabCylinderPairSum_le_target
      hcoupling cutoff extent roots predicate
  have hsepAdd := Q'.add_le_add hinjection (Q'.le_refl'
    (couplingSpinSummedSlabConnectedCylinderResidue
      coupling cutoff extent roots predicate))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hsepAdd
        (Q'.add_le_add (Q'.le_of_eqv htarget) (Q'.le_refl' _))))

#print axioms couplingSpinSummedSlabSeparatedSwitchEncode_weight
#print axioms couplingSpinSummedSeparatedSlabCylinderPairSum_le_target
#print axioms couplingSpinSummedSlabCylinderSourcePairList_sum_eqv_product
#print axioms couplingSpinSummedSlabCylinderSourcePairList_partition
#print axioms couplingSpinSummedSlabBoundaryEvent_supportedComplement_le

end YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingSwitchSummation
