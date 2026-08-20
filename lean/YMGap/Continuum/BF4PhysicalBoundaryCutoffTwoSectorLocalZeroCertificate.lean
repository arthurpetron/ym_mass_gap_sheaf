/-
# Local zero certificates for cutoff-two sector pairs

The 65-state physical block has many zero entries.  This module gives those
zeros a local meaning: the two state-dependent lower-link factor families
already have disjoint support at one fixed-interface face.  A Boolean check
searches the 24 fixed faces; the generic local-zero theorem then annihilates
the complete genuine 140-factor partition sum.

This remains a finite cutoff-two, half-extent-zero result.  It does not assert
the classification of every matrix entry until a separate finite index check
is supplied.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel
import YMGap.Continuum.FiniteScopedFactorLocalZeroCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorLocalZeroCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The 96 state-dependent factors for one ordered sector pair. -/
def cutoffTwoSectorPairSourceFactors
    (left right : EdgeLabelling) : List ScopedQFactor :=
  cutoffTwoSourceLinkFactors left ++ cutoffTwoSourceLinkFactors right

/-- Search the 24 interface coordinates for a locally empty source bucket. -/
def cutoffTwoSectorPairLocalZeroCheck
    (left right : EdgeLabelling) : Bool :=
  factorLocalZeroCheck 2 (centralFixedFaceIds 0)
    (cutoffTwoSectorPairSourceFactors left right)

/-- Check a proposed fixed-face witness directly, without searching all 24
coordinates. -/
def cutoffTwoSectorPairLocalZeroAtCheck
    (left right : EdgeLabelling) (coordinate : Nat) : Bool :=
  factorBucketZeroCheck 2 coordinate
    (cutoffTwoSectorPairSourceFactors left right)

theorem cutoffTwoSectorPairPartitionSum_eqv_zero_of_local_at_check
    (left right : EdgeLabelling) (coordinate : Nat)
    (hcoordinate : coordinate ∈ centralFixedFaceIds 0)
    (hcheck :
      cutoffTwoSectorPairLocalZeroAtCheck left right coordinate = true) :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
      (cutoffTwoSectorPairInterfaceFactors left right) ≈ 0 := by
  have hzero :=
    scopedFactorPartitionSum_append_eqv_zero_of_bucket_check
      2 (centralFixedFaceIds 0)
      (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors)
      (cutoffTwoSectorPairSourceFactors left right)
      coordinate hcoordinate hcheck
  simpa only [cutoffTwoSectorPairInterfaceFactors,
    cutoffTwoSectorPairSourceFactors,
    cutoffTwoSectorPairLocalZeroAtCheck,
    List.append_assoc] using hzero

/-- A checked source conflict annihilates the complete genuine 140-factor
interface partition sum. -/
theorem cutoffTwoSectorPairPartitionSum_eqv_zero_of_local_check
    (left right : EdgeLabelling)
    (hcheck : cutoffTwoSectorPairLocalZeroCheck left right = true) :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
      (cutoffTwoSectorPairInterfaceFactors left right) ≈ 0 := by
  have hzero :=
    scopedFactorPartitionSum_append_eqv_zero_of_local_check
      2 (centralFixedFaceIds 0)
      (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors)
      (cutoffTwoSectorPairSourceFactors left right) hcheck
  simpa only [cutoffTwoSectorPairInterfaceFactors,
    cutoffTwoSectorPairSourceFactors, List.append_assoc] using hzero

/-- The verified computed interface value is zero whenever the local check
succeeds. -/
theorem cutoffTwoSectorPairComputedInterface_eqv_zero_of_local_check
    (left right : EdgeLabelling)
    (hcheck : cutoffTwoSectorPairLocalZeroCheck left right = true) :
    cutoffTwoSectorPairComputedInterface left right ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (cutoffTwoSectorPairPartitionSum_eqv_computed left right))
    (cutoffTwoSectorPairPartitionSum_eqv_zero_of_local_check
      left right hcheck)

/-- The genuine physical reflected-kernel entry is zero whenever the local
source incompatibility check succeeds. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_zero_of_local_check
    (left right : EdgeLabelling)
    (hleft : left ∈ cutoffTwoCubeSectorStates)
    (hright : right ∈ cutoffTwoCubeSectorStates)
    (hcheck : cutoffTwoSectorPairLocalZeroCheck left right = true) :
    centralPhysicalReflectedKernel
      BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
      2 0 left right ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      left right hleft hright)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (cutoffTwoLowerFaceScalar left * cutoffTwoLowerFaceScalar right)
        _ _
        (cutoffTwoSectorPairPartitionSum_eqv_zero_of_local_check
          left right hcheck))
      (Q'.mul_zero_eqv _))

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_zero_of_local_at_check
    (left right : EdgeLabelling) (coordinate : Nat)
    (hleft : left ∈ cutoffTwoCubeSectorStates)
    (hright : right ∈ cutoffTwoCubeSectorStates)
    (hcoordinate : coordinate ∈ centralFixedFaceIds 0)
    (hcheck :
      cutoffTwoSectorPairLocalZeroAtCheck left right coordinate = true) :
    centralPhysicalReflectedKernel
      BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
      2 0 left right ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      left right hleft hright)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (cutoffTwoLowerFaceScalar left * cutoffTwoLowerFaceScalar right)
        _ _
        (cutoffTwoSectorPairPartitionSum_eqv_zero_of_local_at_check
          left right coordinate hcoordinate hcheck))
      (Q'.mul_zero_eqv _))

private theorem getD_mem_of_lt {A : Type} (fallback : A) :
    ∀ (items : List A) (index : Nat), index < items.length →
      items.getD index fallback ∈ items
  | [], _, hindex => by simp at hindex
  | head :: tail, 0, _ => by simp
  | head :: tail, index + 1, hindex => by
      simp only [List.getD_cons_succ, List.mem_cons]
      exact Or.inr
        (getD_mem_of_lt fallback tail index (by simpa using hindex))

/-- Total lookup into the exact sector order, used by finite classification
certificates. -/
def cutoffTwoSectorLocalZeroStateAt (index : Nat) : EdgeLabelling :=
  cutoffTwoCubeSectorStates.getD index zeroEdgeLabelling

theorem cutoffTwoSectorLocalZeroStateAt_mem
    {index : Nat} (hindex : index < 65) :
    cutoffTwoSectorLocalZeroStateAt index ∈
      cutoffTwoCubeSectorStates := by
  apply getD_mem_of_lt zeroEdgeLabelling cutoffTwoCubeSectorStates index
  simpa only [cutoffTwoCubeSectorStates_length] using hindex

def cutoffTwoSectorIndexPairLocalZeroCheck
    (row column : Nat) : Bool :=
  cutoffTwoSectorPairLocalZeroCheck
    (cutoffTwoSectorLocalZeroStateAt row)
    (cutoffTwoSectorLocalZeroStateAt column)

def cutoffTwoSectorIndexPairLocalZeroAtCheck
    (row column coordinate : Nat) : Bool :=
  cutoffTwoSectorPairLocalZeroAtCheck
    (cutoffTwoSectorLocalZeroStateAt row)
    (cutoffTwoSectorLocalZeroStateAt column)
    coordinate

/-- Small regression witness: distinct binary masks 0 and 1 are already
incompatible at a single interface coordinate. -/
theorem cutoffTwoSectorIndexPairLocalZeroCheck_one_two :
    cutoffTwoSectorIndexPairLocalZeroCheck 1 2 = true := by
  decide

theorem cutoffTwoSectorIndexPairLocalZeroAtCheck_one_two :
    cutoffTwoSectorIndexPairLocalZeroAtCheck 1 2 40 = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate.cutoffTwoSectorPairPartitionSum_eqv_zero_of_local_check
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate.centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_zero_of_local_check
