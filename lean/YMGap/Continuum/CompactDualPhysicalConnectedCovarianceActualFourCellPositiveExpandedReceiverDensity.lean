/-
# Receiver-density form of the supported covariance path cross

After zero-raw paths are deleted, every accepted-fiber path has an oriented
coarse endpoint in the established same-datum receiver source or target cell.
The remaining mismatch is measure-theoretic rather than set-theoretic: the
cross-scale path contribution is not definitionally the coarse receiver
weight.

At positive coarse coupling every attached receiver weight is strictly
positive.  This module therefore defines the exact constructive density of
each supported path relative to its oriented receiver pair.  The defining
division identity rewrites both complete supported cell masses, their
determinant, and the connected raw-cross defect as sums of

  receiver density * receiver pair weight.

This is the exact interface needed for a successful-column comparison.  No
bound, invariance, or congestion estimate for the densities is asserted, and
the module proves no `O(a)` estimate, continuum measure, OS/GNS
reconstruction, or physical mass gap.

Constructive contract: positive-denominator rational division and exact
finite sums only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverDensity

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverOrientation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

/-! ## 1. Source-cell receiver density -/

def positiveExpandedFourCellSourceReceiverWeight
    {S : SlabScalePair} {root target : Nat}
    (supported : PositiveExpandedFourCellSourceSupportedPath
      S root target) : Q' :=
  slabObservableTwoReplicaPairWeight S.coarse supported.receiverPair

theorem positiveExpandedFourCellSourceReceiverWeight_pos
    {S : SlabScalePair} {root target : Nat}
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (supported : PositiveExpandedFourCellSourceSupportedPath
      S root target) :
    (0 : Q') <
      positiveExpandedFourCellSourceReceiverWeight supported :=
  slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
    S.coarse hcoarseCoupling supported.receiverPair

/-- Exact cross-scale path density with respect to the oriented coarse
receiver source-pair weight. -/
def positiveExpandedFourCellSourceReceiverDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellSourceSupportedPath
      S root target) : Q' :=
  Q'.divPos
    (positiveExpandedFourCellSourceSupportedPathRawMass
      S hfineCutoff hcoarseCoupling supported)
    (positiveExpandedFourCellSourceReceiverWeight supported)
    (positiveExpandedFourCellSourceReceiverWeight_pos
      hcoarseCoupling supported)

def positiveExpandedFourCellSourceReceiverContribution
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellSourceSupportedPath
      S root target) : Q' :=
  positiveExpandedFourCellSourceReceiverDensity
      S hfineCutoff hcoarseCoupling supported *
    positiveExpandedFourCellSourceReceiverWeight supported

/-- One supported source-cell path is exactly its receiver density times its
oriented receiver-pair weight. -/
theorem positiveExpandedFourCellSourcePathRawMass_eqv_receiverContribution
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellSourceSupportedPath
      S root target) :
    positiveExpandedFourCellSourceSupportedPathRawMass
        S hfineCutoff hcoarseCoupling supported ≈
      positiveExpandedFourCellSourceReceiverContribution
        S hfineCutoff hcoarseCoupling supported := by
  unfold positiveExpandedFourCellSourceReceiverContribution
    positiveExpandedFourCellSourceReceiverDensity
  exact Q'.eqv_symm
    (Q'.divPos_mul_eqv _ _
      (positiveExpandedFourCellSourceReceiverWeight_pos
        hcoarseCoupling supported))

theorem positiveExpandedFourCellSourceSupportedMass_eqv_receiverWeighted
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (positiveExpandedFourCellSourceSupportedPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellSourceSupportedPaths S root target) ≈
      listQSum
        (positiveExpandedFourCellSourceReceiverContribution
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellSourceSupportedPaths S root target) := by
  apply listQSum_congr
  intro supported
  exact
    positiveExpandedFourCellSourcePathRawMass_eqv_receiverContribution
      S hfineCutoff hcoarseCoupling supported

/-! ## 2. Opposite-cell receiver density after replica orientation -/

def positiveExpandedFourCellTargetReceiverWeight
    {S : SlabScalePair} {root target : Nat}
    (supported : PositiveExpandedFourCellTargetSupportedPath
      S root target) : Q' :=
  slabObservableTwoReplicaPairWeight S.coarse supported.receiverPair

theorem positiveExpandedFourCellTargetReceiverWeight_pos
    {S : SlabScalePair} {root target : Nat}
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (supported : PositiveExpandedFourCellTargetSupportedPath
      S root target) :
    (0 : Q') <
      positiveExpandedFourCellTargetReceiverWeight supported :=
  slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
    S.coarse hcoarseCoupling supported.receiverPair

/-- Exact cross-scale path density with respect to the replica-swapped coarse
receiver target-pair weight. -/
def positiveExpandedFourCellTargetReceiverDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellTargetSupportedPath
      S root target) : Q' :=
  Q'.divPos
    (positiveExpandedFourCellTargetSupportedPathRawMass
      S hfineCutoff hcoarseCoupling supported)
    (positiveExpandedFourCellTargetReceiverWeight supported)
    (positiveExpandedFourCellTargetReceiverWeight_pos
      hcoarseCoupling supported)

def positiveExpandedFourCellTargetReceiverContribution
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellTargetSupportedPath
      S root target) : Q' :=
  positiveExpandedFourCellTargetReceiverDensity
      S hfineCutoff hcoarseCoupling supported *
    positiveExpandedFourCellTargetReceiverWeight supported

/-- One supported opposite-cell path is exactly its receiver density times
its replica-oriented receiver-pair weight. -/
theorem positiveExpandedFourCellTargetPathRawMass_eqv_receiverContribution
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellTargetSupportedPath
      S root target) :
    positiveExpandedFourCellTargetSupportedPathRawMass
        S hfineCutoff hcoarseCoupling supported ≈
      positiveExpandedFourCellTargetReceiverContribution
        S hfineCutoff hcoarseCoupling supported := by
  unfold positiveExpandedFourCellTargetReceiverContribution
    positiveExpandedFourCellTargetReceiverDensity
  exact Q'.eqv_symm
    (Q'.divPos_mul_eqv _ _
      (positiveExpandedFourCellTargetReceiverWeight_pos
        hcoarseCoupling supported))

theorem positiveExpandedFourCellTargetSupportedMass_eqv_receiverWeighted
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (positiveExpandedFourCellTargetSupportedPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellTargetSupportedPaths S root target) ≈
      listQSum
        (positiveExpandedFourCellTargetReceiverContribution
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellTargetSupportedPaths S root target) := by
  apply listQSum_congr
  intro supported
  exact
    positiveExpandedFourCellTargetPathRawMass_eqv_receiverContribution
      S hfineCutoff hcoarseCoupling supported

/-! ## 3. Receiver-weighted covariance cross -/

def actualPositiveExpandedReceiverWeightedFaceRawFourCellPathCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
      (positiveExpandedFourCellSourceReceiverContribution
        S hfineCutoff hcoarseCoupling)
      (positiveExpandedFourCellSourceSupportedPaths S root target) -
    listQSum
      (positiveExpandedFourCellTargetReceiverContribution
        S hfineCutoff hcoarseCoupling)
      (positiveExpandedFourCellTargetSupportedPaths S root target)

theorem actualPositiveExpandedSupportedFaceRawFourCellPathCross_eqv_receiverWeighted
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedSupportedFaceRawFourCellPathCross
        S hfineCutoff hcoarseCoupling root target ≈
      actualPositiveExpandedReceiverWeightedFaceRawFourCellPathCross
        S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedSupportedFaceRawFourCellPathCross
    actualPositiveExpandedReceiverWeightedFaceRawFourCellPathCross
  exact sub_eqv_both_local
    (positiveExpandedFourCellSourceSupportedMass_eqv_receiverWeighted
      S hfineCutoff hcoarseCoupling root target)
    (positiveExpandedFourCellTargetSupportedMass_eqv_receiverWeighted
      S hfineCutoff hcoarseCoupling root target)

def physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  (physicalFaceRawFourCellCross
      S.coarse M.coarseRoot M.coarseTarget *
      S.coarse.physicalPartition) *
      rawCovarianceDenominator S.fine.physicalPartition -
    (actualPositiveExpandedReceiverWeightedFaceRawFourCellPathCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget *
      S.fine.physicalPartition) *
      rawCovarianceDenominator S.coarse.physicalPartition

theorem physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect_eqv_receiverWeighted
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect
        S hfineCutoff hcoarseCoupling M := by
  unfold physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
    physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect
  exact sub_eqv_both_local (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _
      (rawCovarianceDenominator S.coarse.physicalPartition)
      (Q'.mul_eqv_congr_right _ _ S.fine.physicalPartition
        (actualPositiveExpandedSupportedFaceRawFourCellPathCross_eqv_receiverWeighted
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget)))

theorem physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedReceiverWeighted
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceRawCrossDefect S hfineCutoff
        hcoarseCoupling M ≈
      physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect
        S hfineCutoff hcoarseCoupling M :=
  Q'.eqv_trans _ _ _
    (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedSupported
      S hfineCutoff hcoarseCoupling M)
    (physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect_eqv_receiverWeighted
      S hfineCutoff hcoarseCoupling M)

/-- A relative bound on the receiver-density-weighted path cross is enough
for the exact connected pushed-law remainder estimate. -/
theorem centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedReceiverWeightedRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross :
      Q'.abs
          (physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect
            S hfineCutoff hcoarseCoupling M) ≤
        budget * connectedCovarianceRawCrossDenominator S) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      budget := by
  apply centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedSupportedPathRawCross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect_eqv_receiverWeighted
          S hfineCutoff hcoarseCoupling M)))
    hcross

#print axioms positiveExpandedFourCellSourceReceiverWeight
#print axioms positiveExpandedFourCellSourceReceiverWeight_pos
#print axioms positiveExpandedFourCellSourceReceiverDensity
#print axioms positiveExpandedFourCellSourceReceiverContribution
#print axioms positiveExpandedFourCellSourcePathRawMass_eqv_receiverContribution
#print axioms positiveExpandedFourCellSourceSupportedMass_eqv_receiverWeighted
#print axioms positiveExpandedFourCellTargetReceiverWeight
#print axioms positiveExpandedFourCellTargetReceiverWeight_pos
#print axioms positiveExpandedFourCellTargetReceiverDensity
#print axioms positiveExpandedFourCellTargetReceiverContribution
#print axioms positiveExpandedFourCellTargetPathRawMass_eqv_receiverContribution
#print axioms positiveExpandedFourCellTargetSupportedMass_eqv_receiverWeighted
#print axioms actualPositiveExpandedReceiverWeightedFaceRawFourCellPathCross
#print axioms actualPositiveExpandedSupportedFaceRawFourCellPathCross_eqv_receiverWeighted
#print axioms physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect
#print axioms physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect_eqv_receiverWeighted
#print axioms physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedReceiverWeighted
#print axioms centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedReceiverWeightedRawCross

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverDensity
