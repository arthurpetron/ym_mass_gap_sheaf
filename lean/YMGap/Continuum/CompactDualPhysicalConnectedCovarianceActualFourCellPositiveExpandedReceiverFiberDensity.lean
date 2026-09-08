/-
# Aggregate supported covariance-path densities on receiver fibers

The supported covariance paths already have exact densities relative to their
oriented coarse receiver-pair weights.  Several distinct paths can share the
same receiver pair, so a receiver-column argument must retain that
multiplicity rather than select one representative.

This module pushes the path densities to the complete duplicate-free receiver
source and target carriers by exact finite fiber summation.  It proves that
the two receiver-weighted path-cell masses, their cross, and the connected
raw-cross defect are unchanged.  The resulting coefficients are literally the
total density load on each receiver pair and vanish off the path image.

This is the exact congestion-aware carrier interface.  It does not bound the
fiber densities, compare them across a successful receiver column, or prove an
`O(a)` estimate, continuum measure, OS/GNS reconstruction, or physical mass
gap.

Constructive contract: finite exact rational fiber sums only; no choice,
`Classical`, `native_decide`, `sorry`, noncomputable declaration, or new
axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverDensity
import YMGap.Continuum.FiniteCoefficientZeroExtension

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverOrientation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

local instance receiverFiberPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

/-! ## 1. Source receiver-fiber density -/

/-- Total supported-path density whose oriented endpoint is this source-cell
receiver pair.  Repeated paths are summed rather than erased. -/
def positiveExpandedFourCellSourceReceiverFiberDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) : Q' :=
  finiteCoefficientZeroExtension
    (positiveExpandedFourCellSourceSupportedPaths S root target)
    (positiveExpandedFourCellSourceReceiverDensity
      S hfineCutoff hcoarseCoupling)
    (fun supported => supported.receiverPair)
    receiver

/-- Summing the fiber density against the complete receiver source carrier
recovers the complete supported source-path mass. -/
theorem positiveExpandedFourCellSourceReceiverFiberMass_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (fun receiver =>
          positiveExpandedFourCellSourceReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellSourcePairs S.coarse root target) ≈
      listQSum
        (positiveExpandedFourCellSourceReceiverContribution
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellSourceSupportedPaths S root target) := by
  simpa only [positiveExpandedFourCellSourceReceiverFiberDensity,
      positiveExpandedFourCellSourceReceiverContribution,
      positiveExpandedFourCellSourceReceiverWeight] using
    (finiteCoefficientZeroExtension_reindex_mul
      (positiveExpandedFourCellSourceSupportedPaths S root target)
      (positiveExpandedFourCellSourceReceiverDensity
        S hfineCutoff hcoarseCoupling)
      (fun supported => supported.receiverPair)
      (slabObservableFourCellSourcePairs S.coarse root target)
      (slabObservableFourCellSourcePairs_nodup S.coarse root target)
      (fun supported _ => supported.receiverPair_mem_fourCellSource)
      (slabObservableTwoReplicaPairWeight S.coarse))

theorem positiveExpandedFourCellSourceReceiverFiberDensity_eqv_zero_of_not_image
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (houtside : ∀ supported,
      supported ∈ positiveExpandedFourCellSourceSupportedPaths S root target →
      receiver ≠ supported.receiverPair) :
    positiveExpandedFourCellSourceReceiverFiberDensity
        S hfineCutoff hcoarseCoupling root target receiver ≈ 0 :=
  finiteCoefficientZeroExtension_eqv_zero_of_not_image
    (positiveExpandedFourCellSourceSupportedPaths S root target)
    (positiveExpandedFourCellSourceReceiverDensity
      S hfineCutoff hcoarseCoupling)
    (fun supported => supported.receiverPair)
    receiver houtside

/-! ## 2. Target receiver-fiber density -/

/-- Total supported-path density whose replica-oriented endpoint is this
target-cell receiver pair. -/
def positiveExpandedFourCellTargetReceiverFiberDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) : Q' :=
  finiteCoefficientZeroExtension
    (positiveExpandedFourCellTargetSupportedPaths S root target)
    (positiveExpandedFourCellTargetReceiverDensity
      S hfineCutoff hcoarseCoupling)
    (fun supported => supported.receiverPair)
    receiver

/-- Summing the fiber density against the complete receiver target carrier
recovers the complete supported opposite-cell path mass. -/
theorem positiveExpandedFourCellTargetReceiverFiberMass_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (fun receiver =>
          positiveExpandedFourCellTargetReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellTargetPairs S.coarse root target) ≈
      listQSum
        (positiveExpandedFourCellTargetReceiverContribution
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellTargetSupportedPaths S root target) := by
  simpa only [positiveExpandedFourCellTargetReceiverFiberDensity,
      positiveExpandedFourCellTargetReceiverContribution,
      positiveExpandedFourCellTargetReceiverWeight] using
    (finiteCoefficientZeroExtension_reindex_mul
      (positiveExpandedFourCellTargetSupportedPaths S root target)
      (positiveExpandedFourCellTargetReceiverDensity
        S hfineCutoff hcoarseCoupling)
      (fun supported => supported.receiverPair)
      (slabObservableFourCellTargetPairs S.coarse root target)
      (slabObservableFourCellTargetPairs_nodup S.coarse root target)
      (fun supported _ => supported.receiverPair_mem_fourCellTarget)
      (slabObservableTwoReplicaPairWeight S.coarse))

theorem positiveExpandedFourCellTargetReceiverFiberDensity_eqv_zero_of_not_image
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (houtside : ∀ supported,
      supported ∈ positiveExpandedFourCellTargetSupportedPaths S root target →
      receiver ≠ supported.receiverPair) :
    positiveExpandedFourCellTargetReceiverFiberDensity
        S hfineCutoff hcoarseCoupling root target receiver ≈ 0 :=
  finiteCoefficientZeroExtension_eqv_zero_of_not_image
    (positiveExpandedFourCellTargetSupportedPaths S root target)
    (positiveExpandedFourCellTargetReceiverDensity
      S hfineCutoff hcoarseCoupling)
    (fun supported => supported.receiverPair)
    receiver houtside

/-! ## 3. Congestion-aware receiver cross -/

def actualPositiveExpandedReceiverFiberWeightedFaceRawFourCellPathCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
      (fun receiver =>
        positiveExpandedFourCellSourceReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver *
          slabObservableTwoReplicaPairWeight S.coarse receiver)
      (slabObservableFourCellSourcePairs S.coarse root target) -
    listQSum
      (fun receiver =>
        positiveExpandedFourCellTargetReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver *
          slabObservableTwoReplicaPairWeight S.coarse receiver)
      (slabObservableFourCellTargetPairs S.coarse root target)

theorem actualPositiveExpandedReceiverWeightedFaceRawFourCellPathCross_eqv_fiberWeighted
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedReceiverWeightedFaceRawFourCellPathCross
        S hfineCutoff hcoarseCoupling root target ≈
      actualPositiveExpandedReceiverFiberWeightedFaceRawFourCellPathCross
        S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedReceiverWeightedFaceRawFourCellPathCross
    actualPositiveExpandedReceiverFiberWeightedFaceRawFourCellPathCross
  exact sub_eqv_both_local
    (Q'.eqv_symm
      (positiveExpandedFourCellSourceReceiverFiberMass_eqv
        S hfineCutoff hcoarseCoupling root target))
    (Q'.eqv_symm
      (positiveExpandedFourCellTargetReceiverFiberMass_eqv
        S hfineCutoff hcoarseCoupling root target))

def physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  (physicalFaceRawFourCellCross
      S.coarse M.coarseRoot M.coarseTarget *
      S.coarse.physicalPartition) *
      rawCovarianceDenominator S.fine.physicalPartition -
    (actualPositiveExpandedReceiverFiberWeightedFaceRawFourCellPathCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget *
      S.fine.physicalPartition) *
      rawCovarianceDenominator S.coarse.physicalPartition

theorem physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect_eqv_fiberWeighted
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect
        S hfineCutoff hcoarseCoupling M := by
  unfold physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect
    physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect
  exact sub_eqv_both_local (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _
      (rawCovarianceDenominator S.coarse.physicalPartition)
      (Q'.mul_eqv_congr_right _ _ S.fine.physicalPartition
        (actualPositiveExpandedReceiverWeightedFaceRawFourCellPathCross_eqv_fiberWeighted
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget)))

theorem physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedReceiverFiberWeighted
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceRawCrossDefect S hfineCutoff
        hcoarseCoupling M ≈
      physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect
        S hfineCutoff hcoarseCoupling M :=
  Q'.eqv_trans _ _ _
    (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedReceiverWeighted
      S hfineCutoff hcoarseCoupling M)
    (physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect_eqv_fiberWeighted
      S hfineCutoff hcoarseCoupling M)

/-- A relative bound on the congestion-aware receiver-fiber cross is enough
for the exact connected pushed-law remainder estimate. -/
theorem centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedReceiverFiberWeightedRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross :
      Q'.abs
          (physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect
            S hfineCutoff hcoarseCoupling M) ≤
        budget * connectedCovarianceRawCrossDenominator S) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      budget := by
  apply centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedReceiverWeightedRawCross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect_eqv_fiberWeighted
          S hfineCutoff hcoarseCoupling M)))
    hcross

#print axioms positiveExpandedFourCellSourceReceiverFiberDensity
#print axioms positiveExpandedFourCellSourceReceiverFiberMass_eqv
#print axioms positiveExpandedFourCellSourceReceiverFiberDensity_eqv_zero_of_not_image
#print axioms positiveExpandedFourCellTargetReceiverFiberDensity
#print axioms positiveExpandedFourCellTargetReceiverFiberMass_eqv
#print axioms positiveExpandedFourCellTargetReceiverFiberDensity_eqv_zero_of_not_image
#print axioms actualPositiveExpandedReceiverFiberWeightedFaceRawFourCellPathCross
#print axioms actualPositiveExpandedReceiverWeightedFaceRawFourCellPathCross_eqv_fiberWeighted
#print axioms physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect
#print axioms physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect_eqv_fiberWeighted
#print axioms physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedReceiverFiberWeighted
#print axioms centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedReceiverFiberWeightedRawCross

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
